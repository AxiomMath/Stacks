module

import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.WellPowered
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitOverComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModuleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImages

/-!
# Injectivity of the canonical map of Stacks 07UM

Let `X` be a Noetherian algebraic space over a scheme `S`, let `ℐ ⊆ 𝒪_X` be a quasi-coherent
sheaf of ideals, let `U = X ∖ V(ℐ)` be its open complement, let `𝒢` be a coherent `𝒪_X`-module
and let `ℱ` be a quasi-coherent `𝒪_X`-module.  This file proves that the canonical map

`colim_n Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ) ⟶ Hom_{𝒪_U}(𝒢|_U, ℱ|_U)`

built in `StacksFrontier.AlgebraicGeometry.Spaces.CoherentHomColimitOverComplement` is
**injective**.

An element of the colimit is represented by some `φ : ℐⁿ 𝒢 ⟶ ℱ`, and it is zero as soon as `φ`
is killed by a deeper step `ℐⁿ⁺ᵏ 𝒢` of the filtration.  If the restriction of `φ` to `U`
vanishes then the image of `φ` is a coherent submodule of `ℱ` with no nonzero sections over any
chart of `U`, hence is supported in `V(ℐ)`; by [Stacks, Tag 07UK] some power `ℐᵏ` annihilates it,
and then `φ` vanishes on `ℐⁿ⁺ᵏ 𝒢` because a section of `ℐⁿ⁺ᵏ 𝒢` lies in `ℐᵏ · (ℐⁿ 𝒢)`.

## Main results

* `AlgebraicGeometry.Space.canonicalMapToHomRestrict_injective`: the canonical map
  `colim_n Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ) ⟶ Hom_{𝒪_U}(𝒢|_U, ℱ|_U)` is injective.  This is the injectivity
  clause of [Stacks, Tag 07UM], and **only** that clause.
* `AlgebraicGeometry.Space.supportOfSheaf_subset_idealZeroLocus_of_subsingleton_pc`: a module
  whose sections over every étale chart of `U` vanish is supported in `V(ℐ)`.  A chart of `X` on
  which `ℐ` is the unit ideal has all of its points in the unit locus of `ℐ`, so its structure
  morphism factors through the open subspace `U`, and the factored morphism is again a
  representable étale chart because the inclusion of `U` is a monomorphism.
* `Stacks.Sites.idealPowSmul_add`: the Artin–Rees identity `Iᵏ · (Iⁿ · N) = Iᵏ⁺ⁿ · N` for a
  power of a sheaf of ideals acting on a submodule of a sheaf of modules, together with
  `Stacks.Sites.idealPowSmul_map_le` and `Stacks.Sites.idealPowSmul_top_map_le`, which push such
  a product forward along a morphism of sheaves of modules.  These are site-generic and are
  stated for an arbitrary site in `Stacks.Sites`.

**No `@[stacks 07UM]` attribute is placed here.**  Tag 07UM asserts that the canonical map is
*bijective*, and only injectivity is proved here; surjectivity is
`AlgebraicGeometry.Space.canonicalMapToHomRestrict_surjective` of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitChartDescent.lean`, and the
attribute sits on the covering set of both clauses,
`AlgebraicGeometry.Space.canonicalMapToHomRestrict_bijective` of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitBijective.lean`.

## Implementation notes

**Equations are passed as arguments, never rewritten.**  For `M : Modules _ _ _ X.1 X.2` the
type `M.val` carries the category instance of `smallEtaleRingedSite`, while the restriction
functor to `U` produces the — definitionally equal, but not syntactically equal — instance
`ObjectProperty.FullSubcategory.category (IsEtaleChart …)`.  Supplying a term across the two
works, but `rewrite` runs at `implicit` transparency and fails with a spurious "did not find an
occurrence of the pattern" together with an application type mismatch inside `restrFun`.  So
equalities of submodules and of morphisms are transported by `congrArg … |>.le` / `.ge` and by
the `.le` / `.ge` projections of lemmas such as `PresheafOfModules.Submodule.range_obj`, and must
stay that way.

**Concrete submodules are never projected, and the ambient submodule is implicit.**  Spelling out
a submodule of a sheaf of modules in a goal forces `sheafifySubmodule`, `sInf` and
`completeLatticeOfInf` to unfold, which exhausts the heartbeat budget.  Every membership step is
therefore pushed into a small lemma taking the submodule as a *variable*
(`mem_presheafIdealSmul_top`, `mem_idealPowSmul_top`), and the ambient
submodule of `mem_of_ι_app_homOfLE_app` and `mem_of_ι_app_factorThru_app` is implicit so that it
is inferred from the supplied hypothesis rather than unified against the goal.  For the same
reason the passage from `ℐⁿ⁺ᵏ 𝒢` to `ℐᵏ · (ℐⁿ 𝒢)` is split into four declarations: the heartbeat
budget is per declaration, and a single combined version failed as a kernel deterministic
timeout.  Do not merge them.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v₁ u₁ u

namespace Stacks.Sites


variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {O : Sheaf J CommRingCat.{u}}

section Add

variable {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}

/-- `Iⁿ · N` is the closure of the objectwise product of `Iⁿ` with the sections of `N`. -/
theorem idealPowSmul_eq_sheafifySubmodule (I : IdealSubsheaf O) (n : ℕ) (N : M.Submodule) :
    idealPowSmul I n N = Stacks.SheafOfModules.sheafifySubmodule
      (presheafIdealSmul (idealPow I n) N.toSubmodule) :=
  rfl

/-- **`Iᵏ⁺ⁿ · N ⊆ Iᵏ · (Iⁿ · N)`**, the inclusion of the Artin–Rees identity which splits a
power of the ideal into two factors.

Over every object the sections of `Iᵏ⁺ⁿ · N` contain `I(X)ᵏ⁺ⁿ · N(X) = I(X)ᵏ · (I(X)ⁿ · N(X))`,
and `I(X)ⁿ · N(X)` lands in the sections of `Iⁿ · N`; the universal property of `Iᵏ⁺ⁿ · N` then
gives the inclusion. -/
theorem idealPowSmul_add_le (I : IdealSubsheaf O) (k n : ℕ) (N : M.Submodule) :
    idealPowSmul I (k + n) N ≤ idealPowSmul I k (idealPowSmul I n N) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact le_of_eq (by rw [Nat.add_zero, idealPowSmul_zero])
  · rw [idealPowSmul_le_iff]
    intro X
    calc ringSectionIdeal I X ^ (k + n) • N.obj X
        = ringSectionIdeal I X ^ k • ringSectionIdeal I X ^ n • N.obj X := by
          rw [pow_add, Submodule.mul_smul]
      _ ≤ ringSectionIdeal I X ^ k • (idealPowSmul I n N).obj X :=
          Submodule.smul_mono le_rfl (pow_smul_le_idealPowSmul I n N X)
      _ ≤ (idealPowSmul I k (idealPowSmul I n N)).obj X :=
          pow_smul_le_idealPowSmul I k (idealPowSmul I n N) X

/-- **`Iᵏ · (Iⁿ · N) = Iᵏ⁺ⁿ · N`**, the Artin–Rees identity for the product of a power of a
sheaf of ideals with a submodule of a sheaf of modules. -/
theorem idealPowSmul_add (I : IdealSubsheaf O) (k n : ℕ) (N : M.Submodule) :
    idealPowSmul I k (idealPowSmul I n N) = idealPowSmul I (k + n) N :=
  le_antisymm (idealPowSmul_idealPowSmul_le I k n N) (idealPowSmul_add_le I k n N)

end Add

section Map

variable {M M' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}

/-- A morphism of sheaves of modules carries the objectwise product `I · N` into the objectwise
product `I · P`, as soon as it carries the sections of `N` into the sections of `P`. -/
theorem presheafIdealSmul_map_le (φ : M ⟶ M') (K : IdealSubsheaf O) (N : M.val.Submodule)
    (P : M'.val.Submodule)
    (h : ∀ (X : Cᵒᵖ) (z : M.val.obj X), z ∈ N.obj X → (φ.val.app X).hom z ∈ P.obj X)
    (X : Cᵒᵖ) (z : M.val.obj X) (hz : z ∈ (presheafIdealSmul K N).obj X) :
    (φ.val.app X).hom z ∈ (presheafIdealSmul K P).obj X := by
  have hle : (presheafIdealSmul K N).obj X ≤
      ((presheafIdealSmul K P).obj X).comap (φ.val.app X).hom := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨a, ha, m, hm, rfl⟩
    change (φ.val.app X).hom (a • m) ∈ (presheafIdealSmul K P).obj X
    rw [map_smul]
    exact smul_mem_presheafIdealSmul K ha (h X m hm)
  exact hle hz

/-- **A morphism of sheaves of modules carries `Iⁿ · N` into `Iⁿ · P`** as soon as it carries the
sections of `N` into the sections of `P`.

A section of `Iⁿ · N` lies in the objectwise product along a covering sieve; the morphism is
linear and commutes with restriction, so its image lies in the objectwise product of `Iⁿ` with
`P` along the same sieve, hence in `Iⁿ · P` by local membership. -/
theorem idealPowSmul_map_le (φ : M ⟶ M') (I : IdealSubsheaf O) (n : ℕ) (N : M.Submodule)
    (P : M'.Submodule)
    (h : ∀ (X : Cᵒᵖ) (z : M.val.obj X), z ∈ N.obj X → (φ.val.app X).hom z ∈ P.obj X)
    (X : Cᵒᵖ) (z : M.val.obj X) (hz : z ∈ (idealPowSmul I n N).obj X) :
    (φ.val.app X).hom z ∈ (idealPowSmul I n P).obj X := by
  rw [idealPowSmul_eq_sheafifySubmodule] at hz
  rw [idealPowSmul_eq_sheafifySubmodule]
  obtain ⟨S, hS, hz⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule hz
  refine Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem hS fun Y f hf => ?_
  have hnat : M'.val.map f.op ((φ.val.app X).hom z)
      = (φ.val.app (op Y)).hom (M.val.map f.op z) :=
    (PresheafOfModules.naturality_apply φ.val f.op z).symm
  rw [hnat]
  exact presheafIdealSmul_map_le φ (idealPow I n) N.toSubmodule P.toSubmodule h (op Y) _ (hz f hf)

/-- **A morphism of sheaves of modules carries `Iⁿ · M` into `Iⁿ` times the image of the
morphism.** -/
theorem idealPowSmul_top_map_le (φ : M ⟶ M') (I : IdealSubsheaf O) (n : ℕ) (X : Cᵒᵖ)
    (z : M.val.obj X) (hz : z ∈ (idealPowSmul I n (⊤ : M.Submodule)).obj X) :
    (φ.val.app X).hom z ∈ (idealPowSmul I n (Stacks.SheafOfModules.sheafifySubmodule
      (PresheafOfModules.Submodule.range φ.val))).obj X := by
  refine idealPowSmul_map_le φ I n ⊤
    (Stacks.SheafOfModules.sheafifySubmodule (PresheafOfModules.Submodule.range φ.val))
    (fun Y w _ => ?_) X z hz
  refine Stacks.SheafOfModules.le_sheafifySubmodule _ Y ?_
  rw [PresheafOfModules.Submodule.range_obj]
  exact LinearMap.mem_range_self _ w

end Map

end Stacks.Sites

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (I : IdealSheaves B S hS X.1 X.2)

section LocalVanishing

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- A section lying in the zero submodule of a sheaf of modules is zero. -/
private theorem eq_zero_of_mem_bot_obj {M : SheafOfModules.{w} R} {W : Cᵒᵖ} {y : M.val.obj W}
    (hy : y ∈ (⊥ : M.Submodule).obj W) : y = 0 :=
  (_root_.Submodule.mem_bot _).1 ((SheafOfModules.Submodule.bot_obj M W).le hy)

/-- The image in the ambient sheaf of modules of a section of a submodule is a section of that
submodule. -/
private theorem ι_app_mem {M : SheafOfModules.{w} R} (N : M.Submodule) (W : Cᵒᵖ)
    (y : N.toSheafOfModules.val.obj W) : (N.ι.val.app W).hom y ∈ N.obj W := y.2

/-- The inclusion of a smaller submodule into a larger one does not change the image of a
section in the ambient sheaf of modules, so membership there is unaffected. -/
private theorem mem_of_ι_app_homOfLE_app {M : SheafOfModules.{w} R} {N₁ N₂ : M.Submodule}
    (h : N₁ ≤ N₂) {W : Cᵒᵖ} {y : N₁.toSheafOfModules.val.obj W} {P : M.Submodule}
    (hy : (N₁.ι.val.app W).hom y ∈ P.obj W) :
    (N₂.ι.val.app W).hom
      (((Stacks.SheafOfModules.Submodule.homOfLE h).val.app W).hom y) ∈ P.obj W := hy

/-- The factorization of a morphism through a submodule, followed by the inclusion of that
submodule, has the same values as the morphism, so membership there is unaffected. -/
private theorem mem_of_ι_app_factorThru_app {M P : SheafOfModules.{w} R} (N : M.Submodule)
    (f : P ⟶ M) (hf : ∀ (Y : Cᵒᵖ) (x : P.val.obj Y), (f.val.app Y).hom x ∈ N.obj Y)
    {W : Cᵒᵖ} {x : P.val.obj W} {Q : M.Submodule}
    (hx : (f.val.app W).hom x ∈ Q.obj W) :
    (N.ι.val.app W).hom (((N.factorThru f hf).val.app W).hom x) ∈ Q.obj W := hx

/-- A section of a sheaf of modules restricting into the zero submodule along every arrow of a
covering sieve is itself zero: the zero submodule has local membership. -/
private theorem eq_zero_of_map_mem_bot {M : SheafOfModules.{w} R} {W : Cᵒᵖ}
    (s : M.val.obj W) {T : Sieve W.unop} (hT : T ∈ J W.unop)
    (hs : ∀ ⦃Y : C⦄ (f : Y ⟶ W.unop), T f →
      M.val.map f.op s ∈ (⊥ : M.Submodule).obj (op Y)) : s = 0 :=
  eq_zero_of_mem_bot_obj
    ((⊥ : M.Submodule).isSheaf s (J.superset_covering (fun _ f hf => hs f hf) hT))

/-- The zero morphism of sheaves of modules sends every section to zero. -/
private theorem zero_val_app_apply {M N : SheafOfModules.{w} R} (W : Cᵒᵖ)
    (z : M.val.obj W) : ((0 : M ⟶ N).val.app W).hom z = 0 := rfl

end LocalVanishing

section AmbientChange


variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {O : Sheaf J CommRingCat.{u}}
  {M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}

/-- A section of a submodule `N` whose image in the ambient sheaf of modules lies in the
objectwise product `I · N` lies in the objectwise product of `I` with all of `N`. -/
private theorem mem_presheafIdealSmul_top (K : Stacks.Sites.IdealSubsheaf O) (N : M.Submodule)
    (Y : Cᵒᵖ) (y : N.toSheafOfModules.val.obj Y)
    (hy : (N.ι.val.app Y).hom y ∈ (Stacks.Sites.presheafIdealSmul K N.toSubmodule).obj Y) :
    y ∈ (Stacks.Sites.presheafIdealSmul K
      (⊤ : N.toSheafOfModules.Submodule).toSubmodule).obj Y := by
  have hle : (Stacks.Sites.presheafIdealSmul K N.toSubmodule).obj Y ≤
      _root_.Submodule.map (N.obj Y).subtype
        ((Stacks.Sites.presheafIdealSmul K
          (⊤ : N.toSheafOfModules.Submodule).toSubmodule).obj Y) := by
    refine _root_.Submodule.span_le.2 ?_
    rintro x ⟨a, ha, m, hm, rfl⟩
    exact ⟨a • (⟨m, hm⟩ : ↥(N.obj Y)), Stacks.Sites.smul_mem_presheafIdealSmul K ha
      (Stacks.SheafOfModules.mem_top_obj _), rfl⟩
  rw [← _root_.Submodule.comap_map_eq_self (f := (N.obj Y).subtype)
    (p := (Stacks.Sites.presheafIdealSmul K
      (⊤ : N.toSheafOfModules.Submodule).toSubmodule).obj Y)
    (by rw [_root_.Submodule.ker_subtype]; exact bot_le)]
  exact hle hy

/-- **Changing the ambient module in a power product.**  A section of a submodule `N` whose image
in the ambient sheaf of modules lies in `Iᵏ · N` lies in `Iᵏ · N` read inside `N` itself. -/
private theorem mem_idealPowSmul_top (I : Stacks.Sites.IdealSubsheaf O) (k : ℕ)
    (N : M.Submodule) (W : Cᵒᵖ) (z : N.toSheafOfModules.val.obj W)
    (hz : (N.ι.val.app W).hom z ∈ (Stacks.Sites.idealPowSmul I k N).obj W) :
    z ∈ (Stacks.Sites.idealPowSmul I k (⊤ : N.toSheafOfModules.Submodule)).obj W := by
  rw [Stacks.Sites.idealPowSmul_eq_sheafifySubmodule] at hz
  rw [Stacks.Sites.idealPowSmul_eq_sheafifySubmodule]
  obtain ⟨T, hT, hz⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule hz
  refine Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem hT fun Y f hf => ?_
  exact mem_presheafIdealSmul_top (Stacks.Sites.idealPow I k) N (op Y) _ (hz f hf)

end AmbientChange

/-- A chart `W` of `X` whose structure morphism factors through the open subspace `U = X ∖ V(ℐ)`
is the chart of `X` underlying a chart of `U`. -/
private theorem exists_pc_eq_of_factor {W : SmallEtale B S hS X.1}
    (k : yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W) ⟶
      (idealComplementSubfunctor B S hS X I).toFunctor)
    (hk : k ≫ (idealComplementSubfunctor B S hS X I).ι = W.1.hom) :
    ∃ V' : SmallEtale B S hS (idealComplement B S hS X I).1, pc B S hS X I V' = W := by
  have hEtaleRespectsIso : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @AlgebraicGeometry.Etale.{u})
  have hRespectsIso : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
  have hk2 : k ≫ (idealComplementι B S hS X I).hom = W.1.hom := hk
  have hk' : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf k := by
    refine MorphismProperty.relative_of_comp_mono yoneda _ k
      (idealComplementSubfunctor B S hS X I).ι ?_
    rw [hk]
    exact W.2
  refine ⟨⟨CostructuredArrow.mk k, hk'⟩, ?_⟩
  refine ObjectProperty.FullSubcategory.ext ?_
  change CostructuredArrow.mk (k ≫ (idealComplementι B S hS X I).hom) = W.obj
  rw [hk2]
  exact (CostructuredArrow.eq_mk W.obj).symm

/-! #### Charts of `X` lying over a chart of `U` -/

/-- **A chart of `X` admitting a morphism to the chart of `X` underlying a chart of
`U = X ∖ V(ℐ)` is itself the chart of `X` underlying a chart of `U`.** -/
theorem exists_pc_eq {V : SmallEtale B S hS (idealComplement B S hS X I).1}
    {W : SmallEtale B S hS X.1} (g : W ⟶ pc B S hS X I V) :
    ∃ V' : SmallEtale B S hS (idealComplement B S hS X I).1, pc B S hS X I V' = W :=
  exists_pc_eq_of_factor B S hS X I (yoneda.map g.hom.left ≫ V.1.hom)
    ((Category.assoc _ _ _).trans (CostructuredArrow.w g.hom))

/-- **A module whose sections over every chart of `U = X ∖ V(ℐ)` vanish is supported in the zero
locus of `ℐ`.**

A chart `W` of `X` on which `ℐ` is the unit ideal has all of its points in the unit locus of `ℐ`,
so its structure morphism factors through the open subspace `U`; the factored morphism is again a
representable étale chart because the inclusion of `U` is a monomorphism, so `W` is the chart of
`X` underlying a chart of `U` and the hypothesis applies to it. -/
theorem supportOfSheaf_subset_idealZeroLocus_of_subsingleton_pc
    (H : Modules.{u, u} B S hS X.1 X.2)
    (hvanish : ∀ V : SmallEtale B S hS (idealComplement B S hS X I).1,
      Subsingleton (H.val.obj (op (pc B S hS X I V)))) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj H) ⊆
      idealZeroLocus B S hS X I := by
  have key : ∀ W : SmallEtale B S hS X.1, I.obj (op W) = ⊤ →
      Subsingleton (H.val.obj (op W)) := by
    intro W hW
    have hunit : Set.range (pointsMap B S hS
        (idealComplementSubfunctor B S hS X I).toFunctor
        (idealComplementSubfunctor B S hS X I).ι) = idealUnitLocus B S hS X I :=
      range_pointsMap_ι_openSubspaceOfPoints B S hS _
    have hrange : Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W)) W.1.hom) ⊆
        Set.range (pointsMap B S hS (idealComplementSubfunctor B S hS X I).toFunctor
          (idealComplementSubfunctor B S hS X I).ι) := by
      rw [hunit]
      rintro x ⟨y, rfl⟩
      exact ⟨W, hW, ⟨y, rfl⟩⟩
    obtain ⟨k, hk⟩ := (factorsThrough_openSubspace_iff_points B S hS X.2
      (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS X.1).obj W))
      (idealComplementSubfunctor B S hS X I)
      (isOpenSubspace_idealComplementSubfunctor B S hS X I) W.1.hom).mpr hrange
    obtain ⟨V', heq⟩ := exists_pc_eq_of_factor B S hS X I k hk
    exact (congrArg (fun Z : SmallEtale B S hS X.1 => Subsingleton (H.val.obj (op Z))) heq).mp
      (hvanish V')
  refine supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton B S hS X H I ?_
  intro V hV W g
  exact key W (SheafOfModules.Submodule.unit_obj_eq_top_of_map I (Quiver.Hom.op g) hV)

/-! #### The image of a morphism out of `ℐⁿ 𝒢` -/

/-- The image of `φ : ℐⁿ 𝒢 ⟶ ℱ`: the smallest submodule of `ℱ` with local membership containing
the objectwise ranges of `φ`. -/
private noncomputable abbrev rangeSubmodule {G F : Modules.{u, u} B S hS X.1 X.2} {n : ℕ}
    (φ : idealPowModule I n G ⟶ F) : F.Submodule :=
  Stacks.SheafOfModules.sheafifySubmodule (PresheafOfModules.Submodule.range φ.val)

/-- Every value of `φ` is a section of the image of `φ`. -/
private theorem app_mem_rangeSubmodule {G F : Modules.{u, u} B S hS X.1 X.2} {n : ℕ}
    (φ : idealPowModule I n G ⟶ F) (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (idealPowModule I n G).val.obj W) :
    (φ.val.app W).hom x ∈ (rangeSubmodule B S hS X I φ).obj W :=
  Stacks.SheafOfModules.le_sheafifySubmodule _ W
    ((PresheafOfModules.Submodule.range_obj φ.val W).ge (LinearMap.mem_range_self _ x))

/-- **The factorization of `φ` through its image is an epimorphism**: every section of the image
is, along a covering sieve, in the range of `φ`. -/
private theorem epi_factorThruRange {G F : Modules.{u, u} B S hS X.1 X.2} {n : ℕ}
    (φ : idealPowModule I n G ⟶ F) :
    Epi ((rangeSubmodule B S hS X I φ).factorThru φ
      (app_mem_rangeSubmodule B S hS X I φ)) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {W} s => ?_⟩
  obtain ⟨T, hT, hs⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule
    (N := PresheafOfModules.Submodule.range φ.val) s.2
  refine (SmallEtale.topology B S hS X.1).superset_covering (fun Y g hg => ?_) hT
  obtain ⟨t, ht⟩ :=
    (PresheafOfModules.Submodule.range_obj φ.val (op Y)).le (hs g hg)
  exact ⟨t, Subtype.ext ht⟩

/-! #### Vanishing over `U` and the key annihilation statement -/

/-- A morphism `φ : ℐⁿ 𝒢 ⟶ ℱ` whose restriction to `U = X ∖ V(ℐ)` vanishes kills every section of
`ℐⁿ 𝒢` over a chart of `U`. -/
private theorem app_pc_eq_zero {G F : Modules.{u, u} B S hS X.1 X.2} {n : ℕ}
    (φ : idealPowModule I n G ⟶ F) (hφ : homRestrict B S hS X I φ = 0)
    (V : SmallEtale B S hS (idealComplement B S hS X I).1)
    (z : (idealPowModule I n G).val.obj (op (pc B S hS X I V))) :
    (φ.val.app (op (pc B S hS X I V))).hom z = 0 := by
  have h0 : (idealPowRestrictIso B S hS X I n G).inv ≫
      (restrictToIdealComplement B S hS X I).map φ = 0 := hφ
  have h1 : (restrictToIdealComplement B S hS X I).map φ = 0 := by
    rw [← Iso.hom_inv_id_assoc (idealPowRestrictIso B S hS X I n G)
      ((restrictToIdealComplement B S hS X I).map φ), h0, comp_zero]
  have h2 := congrArg (fun ψ :
      (restrictToIdealComplement B S hS X I).obj (idealPowModule I n G) ⟶
        (restrictToIdealComplement B S hS X I).obj F =>
      (ψ.val.app (op V)).hom z) h1
  exact h2.trans (zero_val_app_apply
    (M := (restrictToIdealComplement B S hS X I).obj (idealPowModule I n G))
    (N := (restrictToIdealComplement B S hS X I).obj F) (op V) z)

/-- Over a chart of `U = X ∖ V(ℐ)` the image of a morphism `φ : ℐⁿ 𝒢 ⟶ ℱ` whose restriction to
`U` vanishes has no nonzero sections. -/
private theorem subsingleton_rangeSubmodule_pc {G F : Modules.{u, u} B S hS X.1 X.2} {n : ℕ}
    (φ : idealPowModule I n G ⟶ F) (hφ : homRestrict B S hS X I φ = 0)
    (V : SmallEtale B S hS (idealComplement B S hS X I).1) :
    Subsingleton ((rangeSubmodule B S hS X I φ).toSheafOfModules.val.obj
      (op (pc B S hS X I V))) := by
  have hzero : ∀ z : (rangeSubmodule B S hS X I φ).toSheafOfModules.val.obj
      (op (pc B S hS X I V)), z = 0 := by
    intro z
    obtain ⟨T, hT, hz⟩ := Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule
      (N := PresheafOfModules.Submodule.range φ.val) z.2
    refine Subtype.ext (eq_zero_of_map_mem_bot (M := F) z.1 hT fun Y f hf => ?_)
    obtain ⟨V', rfl⟩ := exists_pc_eq B S hS X I f
    obtain ⟨t, ht⟩ :=
      (PresheafOfModules.Submodule.range_obj φ.val (op (pc B S hS X I V'))).le (hz f hf)
    refine (SheafOfModules.Submodule.bot_obj F (op (pc B S hS X I V'))).ge ?_
    exact (_root_.Submodule.mem_bot _).2
      (ht.symm.trans (app_pc_eq_zero B S hS X I φ hφ V' t))
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

/-- A morphism of `𝒪_X`-modules vanishing on every section over every chart is zero. -/
private theorem hom_eq_zero_of_app_eq_zero {M M' : Modules.{u, u} B S hS X.1 X.2} (ψ : M ⟶ M')
    (h : ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ) (z : M.val.obj W), (ψ.val.app W).hom z = 0) :
    ψ = 0 := by
  refine SheafOfModules.hom_ext (show ψ.val = 0 from ?_)
  ext W z
  simpa using h W z

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- **The image of a morphism out of `ℐⁿ 𝒢` is coherent** as soon as `ℐⁿ 𝒢` is coherent and the
target is quasi-coherent.

The image is an epimorphic image of `ℐⁿ 𝒢`, and it is quasi-coherent because it is a second
epimorphism-monomorphism factorization of `φ`, hence isomorphic to the image of `φ`. -/
private theorem isCoherent_rangeSubmodule
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    {G F : Modules.{u, u} B S hS X.1 X.2} [F.IsQuasicoherentOnSite] {n : ℕ}
    (φ : idealPowModule I n G ⟶ F)
    (hcohG : IsCoherent B S hS X.1 X.2 (idealPowModule I n G)) :
    IsCoherent B S hS X.1 X.2 (rangeSubmodule B S hS X I φ).toSheafOfModules := by
  have hqcG : (idealPowModule I n G).IsQuasicoherentOnSite := hcohG.toIsQuasicoherentOnSite
  have hepi := epi_factorThruRange B S hS X I φ
  have hstrong : StrongEpi ((rangeSubmodule B S hS X I φ).factorThru φ
    (app_mem_rangeSubmodule B S hS X I φ)) := strongEpi_of_epi _
  have hiso : image φ ≅ (rangeSubmodule B S hS X I φ).toSheafOfModules :=
    (image.isoStrongEpiMono ((rangeSubmodule B S hS X I φ).factorThru φ
        (app_mem_rangeSubmodule B S hS X I φ)) (rangeSubmodule B S hS X I φ).ι
      ((rangeSubmodule B S hS X I φ).factorThru_ι φ
        (app_mem_rangeSubmodule B S hS X I φ))).symm
  have hqcH : (rangeSubmodule B S hS X I φ).toSheafOfModules.IsQuasicoherentOnSite :=
    ObjectProperty.prop_of_iso
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _) hiso
      (isQuasicoherentOnSite_image_unconditional B S hS X.1 X.2 φ hqcG inferInstance)
  exact isCoherent_of_epi_of_isQuasicoherentOnSite B S hS X.1 X.2
    ((rangeSubmodule B S hS X I φ).factorThru φ
      (app_mem_rangeSubmodule B S hS X I φ)) hqcH hcohG

/-- **A section of `ℐⁿ⁺ᵏ 𝒢`, read as a section of `ℐⁿ 𝒢`, lies in `ℐᵏ · (ℐⁿ 𝒢)`** — the
Artin–Rees identity, with the ambient module changed from `𝒢` to `ℐⁿ 𝒢`. -/
theorem idealPowModuleHomOfLE_app_mem_idealPowSmul_top
    (G : Modules.{u, u} B S hS X.1 X.2) (n k : ℕ) (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : (idealPowModule I (n + k) G).val.obj W) :
    ((idealPowModuleHomOfLE I G (Nat.le_add_right n k)).val.app W).hom z ∈
      (Stacks.Sites.idealPowSmul I k (⊤ : (idealPowModule I n G).Submodule)).obj W := by
  have hsum : Stacks.Sites.idealPowSmul I k (idealPowSubmodule I n G)
      = idealPowSubmodule I (n + k) G := by
    have h := Stacks.Sites.idealPowSmul_add I k n (⊤ : G.Submodule)
    rw [Nat.add_comm k n] at h
    exact h
  have hz : ((idealPowModuleι I (n + k) G).val.app W).hom z ∈
      (Stacks.Sites.idealPowSmul I k (idealPowSubmodule I n G)).obj W :=
    (congrArg (fun P : G.Submodule => P.obj W) hsum).ge
      (ι_app_mem (idealPowSubmodule I (n + k) G) W z)
  exact mem_idealPowSmul_top I k (idealPowSubmodule I n G) W _
    (mem_of_ι_app_homOfLE_app (idealPowSubmodule_antitone I G (Nat.le_add_right n k)) hz)

/-- **A morphism `φ : ℐⁿ 𝒢 ⟶ ℱ` whose image is annihilated by `ℐᵏ` vanishes on `ℐⁿ⁺ᵏ 𝒢`.**

A section of `ℐⁿ⁺ᵏ 𝒢` lies in `ℐᵏ · (ℐⁿ 𝒢)`, so `φ` carries it into `ℐᵏ` times the image of `φ`;
read inside that image the section is annihilated, hence zero, and the inclusion of the image is
linear. -/
private theorem idealPowModuleHomOfLE_comp_eq_zero
    {G F : Modules.{u, u} B S hS X.1 X.2} {n k : ℕ} (φ : idealPowModule I n G ⟶ F)
    (hk : Stacks.Sites.idealPowSmul I k
      (⊤ : (rangeSubmodule B S hS X I φ).toSheafOfModules.Submodule) = ⊥) :
    idealPowModuleHomOfLE I G (Nat.le_add_right n k) ≫ φ = 0 := by
  refine hom_eq_zero_of_app_eq_zero B S hS X _ fun W z => ?_
  have hz2 := idealPowModuleHomOfLE_app_mem_idealPowSmul_top B S hS X I G n k W z
  have hz3 := Stacks.Sites.idealPowSmul_top_map_le φ I k W _ hz2
  have hz3' := mem_of_ι_app_factorThru_app (rangeSubmodule B S hS X I φ) φ
    (app_mem_rangeSubmodule B S hS X I φ) hz3
  have hz4 := mem_idealPowSmul_top I k (rangeSubmodule B S hS X I φ) W _ hz3'
  have hz5 := eq_zero_of_mem_bot_obj
    ((congrArg (fun P : (rangeSubmodule B S hS X I φ).toSheafOfModules.Submodule =>
      P.obj W) hk).le hz4)
  have hι := congrArg (fun y : (rangeSubmodule B S hS X I φ).toSheafOfModules.val.obj W =>
    ((rangeSubmodule B S hS X I φ).ι.val.app W).hom y) hz5
  have hfac := congrArg (fun ψ : idealPowModule I n G ⟶ F => (ψ.val.app W).hom
    (((idealPowModuleHomOfLE I G (Nat.le_add_right n k)).val.app W).hom z))
    ((rangeSubmodule B S hS X I φ).factorThru_ι φ (app_mem_rangeSubmodule B S hS X I φ))
  exact hfac.symm.trans (hι.trans (map_zero _))

/-- **A morphism out of `ℐⁿ 𝒢` which vanishes over `U = X ∖ V(ℐ)` dies on a deeper step of the
filtration**: its restriction to `ℐⁿ⁺ᵏ 𝒢` is zero for some `k`.

The image of `φ` is coherent and has no sections over any chart of `U`, so it is supported in
`V(ℐ)`; by Stacks 07UK some power `ℐᵏ` annihilates it, and then `φ` vanishes on `ℐⁿ⁺ᵏ 𝒢`. -/
private theorem exists_idealPowModuleHomOfLE_comp_eq_zero
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ X.1)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    {G F : Modules.{u, u} B S hS X.1 X.2} (hG : IsCoherent B S hS X.1 X.2 G)
    [F.IsQuasicoherentOnSite] {n : ℕ} (φ : idealPowModule I n G ⟶ F)
    (hφ : homRestrict B S hS X I φ = 0) :
    ∃ k : ℕ, idealPowModuleHomOfLE I G (Nat.le_add_right n k) ≫ φ = 0 := by
  have : Fact (HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  have hcohH : IsCoherent B S hS X.1 X.2 (rangeSubmodule B S hS X I φ).toSheafOfModules :=
    isCoherent_rangeSubmodule B S hS X I φ
      (isCoherent_idealPowModule_of_isQuasicoherentOnSite B S hS X.1 X.2 I n G hG hI)
  obtain ⟨k, hk⟩ := (exists_idealPowSmul_eq_bot_iff_supportOfSheaf_subset_idealZeroLocus
    B S hS hZ X hN (rangeSubmodule B S hS X I φ).toSheafOfModules hcohH I hI).2
    (supportOfSheaf_subset_idealZeroLocus_of_subsingleton_pc B S hS X I
      (rangeSubmodule B S hS X I φ).toSheafOfModules
      (subsingleton_rangeSubmodule_pc B S hS X I φ hφ))
  exact ⟨k, idealPowModuleHomOfLE_comp_eq_zero B S hS X I φ hk⟩

/-- **Injectivity of the canonical map of [Stacks, Tag 07UM].**  For a Noetherian algebraic space
`X` over `S`, a quasi-coherent sheaf of ideals `ℐ` with complement `U = X ∖ V(ℐ)`, a
coherent `𝒪_X`-module `𝒢` and a quasi-coherent `𝒪_X`-module `ℱ`, the canonical map

`colim_n Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ) ⟶ Hom_{𝒪_U}(𝒢|_U, ℱ|_U)`

is injective.  Every element of the colimit is represented by some `φ : ℐⁿ 𝒢 ⟶ ℱ`, and a `φ`
whose restriction to `U` vanishes already vanishes on `ℐⁿ⁺ᵏ 𝒢` for some `k`, hence represents
zero. -/
theorem canonicalMapToHomRestrict_injective
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ X.1)
    (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (G F : Modules.{u, u} B S hS X.1 X.2) (hG : IsCoherent B S hS X.1 X.2 G)
    [F.IsQuasicoherentOnSite] :
    Function.Injective (canonicalMapToHomRestrict B S hS X I G F) := by
  have hforget : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u + 1}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  refine (injective_iff_map_eq_zero
    (AddCommGrpCat.Hom.hom (canonicalMapToHomRestrict B S hS X I G F))).mpr fun z hz => ?_
  obtain ⟨m, φ, rfl⟩ := Limits.Concrete.colimit_exists_rep (homSystem B S hS X I G F) z
  obtain ⟨k, hk⟩ := exists_idealPowModuleHomOfLE_comp_eq_zero B S hS X I hZ hN hI hG φ
    ((canonicalMapToHomRestrict_ι B S hS X I G F m φ).symm.trans hz)
  calc Limits.colimit.ι (homSystem B S hS X I G F) m φ
      = Limits.colimit.ι (homSystem B S hS X I G F) (m + k)
          ((homSystem B S hS X I G F).map (homOfLE (Nat.le_add_right m k)) φ) := by
        rw [← ConcreteCategory.comp_apply, Limits.colimit.w]
    _ = Limits.colimit.ι (homSystem B S hS X I G F) (m + k) 0 :=
        congrArg (ConcreteCategory.hom
          (Limits.colimit.ι (homSystem B S hS X I G F) (m + k)))
          (show (homSystem B S hS X I G F).map (homOfLE (Nat.le_add_right m k)) φ = 0 from hk)
    _ = 0 := map_zero _

end AlgebraicGeometry.Space

end
