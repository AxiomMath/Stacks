module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftUnitHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleLocalizationBijective
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomToInjectiveSingle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ModuleCohomology
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension

/-!
# Restriction from the big to the small étale site does not preserve injective modules

Stacks 0758 proves that restriction from the big étale site `(Sch/S)_étale` to the small étale
site `S_étale`, and along a morphism `f : T → S` of the big site, preserves injective abelian
sheaves and K-injective complexes of abelian sheaves
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/Restriction.lean`), and ends
with: "The corresponding statements for modules do not hold."  This file formalizes that
sentence, with the source's counterexample.

Let `S = Spec ℤ`. Multiplication by `2` is an injective map `𝒪_S → 𝒪_S` of `𝒪_S`-modules on
`S_étale`, every object of `S_étale` being flat over `ℤ`, but it becomes zero on `Spec 𝔽₂`.  If
`α : 𝒪 → ℐ` is an injection into an injective `𝒪`-module on `(Sch/S)_étale` and `ℐ|_{S_étale}`
were injective, `α|_{S_étale}` would factor as `2 · β`; evaluating the corresponding global
sections on the final object `S/S` and restricting to `Spec 𝔽₂ → S` shows that `α` kills the
unit section over `Spec 𝔽₂`, contradicting injectivity of `α`.  The source phrases the last step
through the adjunction `π_S^* ⊣ π_{S,*}`; here it is carried out on global sections, which is
what that adjunction amounts to for the unit object.

The restriction functor is `AlgebraicGeometry.smallEtaleModuleRestriction B S S (𝟙 S)`, which is
both `i_S^*` (the Stacks 021F functor at the identity is the small étale inclusion,
`AlgebraicGeometry.smallEtaleToBigEtaleFunctor_id_eq`) and `i_f^*` for `f = 𝟙 S`, so the
counterexample refutes the module versions of parts (1)(a), (1)(b), and, through complexes
concentrated in degree `0`, of parts (2)(a), (2)(b).

## Main results

* `AlgebraicGeometry.not_injective_smallEtaleModuleRestriction_of_mono` — the source's argument:
  for any injection `𝒪 → ℐ` into an injective `𝒪`-module, `ℐ|_{S_étale}` is not injective.
* `AlgebraicGeometry.exists_injective_not_injective_smallEtaleModuleRestriction` — an injective
  `𝒪`-module whose restriction is not injective.
* `AlgebraicGeometry.exists_isKInjective_not_isKInjective_smallEtaleModuleRestriction` — a
  K-injective complex of `𝒪`-modules whose restriction is not K-injective.
* `CochainComplex.injective_of_isKInjective_singleFunctor_obj` — an object whose single complex
  is K-injective is injective.

## References

* [Stacks Project, Tag 0758](https://stacks.math.columbia.edu/tag/0758)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry

/-- A scheme flat over `Spec ℤ` has no `2`-torsion in its rings of sections. -/
theorem eq_zero_of_mul_two_eq_zero_of_flat {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) [Flat f] {U : X.Opens} (a : Γ(X, U))
    (ha : a * 2 = 0) : a = 0 := by
  apply X.IsSheaf.section_ext
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  have hVU' : V ≤ U := hVU
  refine ⟨V, hVU', hxV, ?_⟩
  have hflat : (f.appLE ⊤ V le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat (f := f) inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  let ψ : ℤ →+* Γ(X, V) :=
    ((f.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso _).inv.hom).comp
      ULift.ringEquiv.symm.toRingHom
  have hψ : ψ.Flat :=
    (RingHom.Flat.of_bijective ULift.ringEquiv.symm.bijective).comp
      ((RingHom.Flat.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv)).comp hflat)
  have hψ' : (algebraMap ℤ Γ(X, V)).Flat := Subsingleton.elim ψ (algebraMap ℤ Γ(X, V)) ▸ hψ
  have : Module.Flat ℤ Γ(X, V) := RingHom.flat_algebraMap_iff.mp hψ'
  have hreg : IsSMulRegular Γ(X, V) (2 : ℤ) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero two_ne_zero)
  apply hreg
  change (2 : ℤ) • (X.presheaf.map (homOfLE hVU').op).hom a =
    (2 : ℤ) • (X.presheaf.map (homOfLE hVU').op).hom 0
  rw [map_zero, smul_zero, zsmul_eq_mul, Int.cast_ofNat,
    ← map_ofNat (X.presheaf.map (homOfLE hVU').op).hom 2, ← map_mul, mul_comm, ha, map_zero]

/-- An object of an abelian category whose single complex in degree `0` is K-injective is
injective: `Ext¹(Y, E)` is a morphism in the derived category into the shift of a K-injective
complex, hence comes from a chain map `Y[0] ⟶ E[0][1]`, and every such chain map is zero. -/
theorem _root_.CochainComplex.injective_of_isKInjective_singleFunctor_obj {C : Type*}
    [Category* C] [Abelian C] (E : C)
    [((CochainComplex.singleFunctor C 0).obj E).IsKInjective] : Injective E := by
  let := HasDerivedCategory.standard C
  let := HasExt.standard C
  rw [injective_iff_subsingleton_ext_one]
  intro Y
  let L := (CochainComplex.singleFunctor C 0).obj E
  let K := (CochainComplex.singleFunctor C 0).obj Y
  have hz : ∀ φ : K ⟶ L⟦(1 : ℤ)⟧, φ = 0 := by
    intro φ
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    by_cases hn : n = 0
    · subst hn
      apply IsZero.eq_of_tgt
      exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 E (0 + 1) (by omega)
    · apply IsZero.eq_of_src
      exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Y n hn
  let e : (DerivedCategory.Q.obj L)⟦(1 : ℤ)⟧ ≅ DerivedCategory.Q.obj (L⟦(1 : ℤ)⟧) :=
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app L).symm
  refine ⟨fun a b => Abelian.Ext.homEquiv.injective ?_⟩
  have hsub : ∀ c d : DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦(1 : ℤ)⟧, c = d := by
    intro c d
    obtain ⟨φ, hφ⟩ := DerivedCategory.Q_map_surjective_of_isKInjective K (L⟦(1 : ℤ)⟧) (c ≫ e.hom)
    obtain ⟨ψ, hψ⟩ := DerivedCategory.Q_map_surjective_of_isKInjective K (L⟦(1 : ℤ)⟧) (d ≫ e.hom)
    rw [← cancel_mono e.hom, ← hφ, ← hψ, hz φ, hz ψ]
  exact hsub _ _

/-- A scheme `Spec R` with `R` countable lies in every big étale site. -/
theorem BigEtaleSite.contains_spec_of_countable (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
    [Countable R] : B.Contains (Spec (CommRingCat.of R)) := by
  change (Spec (CommRingCat.of R)).size < B.cutoff
  rw [Scheme.size_Spec]
  exact lt_of_le_of_lt (max_le le_rfl (Cardinal.mk_le_aleph0 (α := R))) B.aleph0_lt_cutoff

variable (B : BigEtaleSite.{u})

/-- `Spec ℤ` as an object of a big étale site. -/
abbrev BigEtaleSite.specInt : B.Scheme :=
  B.obj _ (B.contains_spec_of_countable (ULift.{u} ℤ))

/-- The structure sheaf of the big étale site over `S`, as a sheaf of modules over itself at the
module universe `u + 1` of `AlgebraicGeometry.smallEtaleModuleRestriction`. -/
abbrev bigEtaleModuleUnit (S : B.Scheme) :
    SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property) :=
  SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (SheafOfModules.unit _)

/-- The structure sheaf of the small étale site of `S`, as a sheaf of modules over itself at the
module universe `u + 1`. -/
abbrev smallEtaleModuleUnit (S : B.Scheme) :
    SheafOfModules.{u + 1} (SmallEtale.structureSheaf B S.obj S.property) :=
  SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (SheafOfModules.unit _)

/-- The ring map `ℤ → 𝔽₂`, at universe `u`. -/
private def intToFTwo : CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of (ULift.{u} (ZMod 2)) :=
  CommRingCat.ofHom ((ULift.ringEquiv.symm.toRingHom.comp (Int.castRingHom (ZMod 2))).comp
    ULift.ringEquiv.toRingHom)

/-- `Spec 𝔽₂` as an object of the big étale site over `Spec ℤ`. -/
private abbrev specFTwoOver : BigEtaleOver B (B.specInt).obj (B.specInt).property :=
  Over.mk (Y := B.obj _ (B.contains_spec_of_countable (ULift.{u} (ZMod 2))))
    (ObjectProperty.homMk (Spec.map intToFTwo))

/-- **Stacks Project, Tag 0758, the module clause.** Let `S = Spec ℤ`. For an injective
`𝒪`-module `ℐ` on `(Sch/S)_étale` and an injection `α : 𝒪 → ℐ`, the restriction `ℐ|_{S_étale}`
is not an injective `𝒪_S`-module. -/
@[stacks 0758 "module counterexample: for S = Spec ℤ, the restriction to S_étale of an \
injective O-module receiving an injection from O is not injective"]
theorem not_injective_smallEtaleModuleRestriction_of_mono
    (I : SheafOfModules.{u + 1}
      (BigEtaleOver.structureSheaf B (B.specInt).obj (B.specInt).property))
    (α : bigEtaleModuleUnit B B.specInt ⟶ I) [Mono α] :
    ¬ Injective ((smallEtaleModuleRestriction B B.specInt B.specInt (𝟙 B.specInt)).obj I) := by
  intro hJ
  let S := B.specInt
  let F := smallEtaleToBigEtaleFunctor B S S (𝟙 S)
  let J := (smallEtaleModuleRestriction B S S (𝟙 S)).obj I
  let s := Stacks.SheafOfModules.uliftUnitSheafHomEquiv.{u + 1, u, u, u + 1} I α
  let s' : J.sections := PresheafOfModules.sectionsMk (M := J.val)
    (fun X => s.val (op (F.obj X.unop)))
    (fun X Y f => PresheafOfModules.sections_property s (F.op.map f))
  let g := (Stacks.SheafOfModules.uliftUnitSheafHomEquiv.{u + 1, u, u, u + 1} J).symm s'
  let O := smallEtaleModuleUnit B S
  let two : O ⟶ O := (Stacks.SheafOfModules.uliftUnitSheafHomEquiv.{u + 1, u, u, u + 1} O).symm
    (PresheafOfModules.sectionsMk (M := O.val)
      (fun X => ULift.up (2 : (SmallEtale.structureSheaf B S.obj S.property).obj.obj X))
      (fun X Y f => ULift.ext (map_ofNat (SmallEtale.structureSheaf B S.obj S.property
        |>.obj.map f).hom 2)))
  have htwo : ∀ (X)
      (a : ULift.{u + 1} ((SmallEtale.structureSheaf B S.obj S.property).obj.obj X)),
      two.val.app X a = ULift.up (a.down * 2) := fun _ _ => rfl
  have hinj : ∀ X, Function.Injective (two.val.app X) := by
    intro X
    let Y := X.unop
    let f : Y.obj.left.obj ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) := B.inclusion.map Y.obj.hom
    have : Flat f := inferInstance
    have hc : ∀ c : (SmallEtale.structureSheaf B S.obj S.property).obj.obj X, c * 2 = 0 →
        c = 0 := fun c hc => eq_zero_of_mul_two_eq_zero_of_flat f c hc
    have key : ∀ a b : ULift.{u + 1} ((SmallEtale.structureSheaf B S.obj S.property).obj.obj X),
        two.val.app X a = two.val.app X b → a = b := by
      rintro ⟨a⟩ ⟨b⟩ hab
      have h : a * 2 = b * 2 :=
        congrArg ULift.down ((htwo X ⟨a⟩).symm.trans (hab.trans (htwo X ⟨b⟩)))
      have h' : (a - b) * 2 = 0 := by rw [sub_mul, h, sub_self]
      exact congrArg ULift.up (sub_eq_zero.mp (hc (a - b) h'))
    exact fun a b hab => key a b hab
  have : Mono two := ⟨fun {Z} φ ψ e => by
    ext X x
    apply hinj X
    exact congrArg (fun χ : Z ⟶ O => χ.val.app X x) e⟩
  let β := Injective.factorThru g two
  have hβ : two ≫ β = g := Injective.comp_factorThru g two
  let Z := SmallEtale.final B S.obj S.property
  let one : ULift.{u + 1} ((SmallEtale.structureSheaf B S.obj S.property).obj.obj (op Z)) :=
    ULift.up 1
  let t : J.val.obj (op Z) := β.val.app (op Z) one
  let s'Z : J.val.obj (op Z) := s'.val (op Z)
  have e1 : two.val.app (op Z) one =
      (2 : (SmallEtale.structureSheaf B S.obj S.property).obj.obj (op Z)) • one := by
    change (1 : (SmallEtale.structureSheaf B S.obj S.property).obj.obj (op Z)) •
      (ULift.up (2 : (SmallEtale.structureSheaf B S.obj S.property).obj.obj (op Z)) :
        O.val.obj (op Z)) = _
    rw [one_smul]
    exact ULift.ext
      (show (2 : (SmallEtale.structureSheaf B S.obj S.property).obj.obj (op Z)) = 2 * 1 from
        (mul_one _).symm)
  have keyJ : (2 : (SmallEtale.structureSheaf B S.obj S.property).obj.obj (op Z)) •
      t = s'Z := by
    have h := congrArg (fun χ : O ⟶ J => χ.val.app (op Z) one) hβ
    have h1 : (two ≫ β).val.app (op Z) one =
        (2 : (SmallEtale.structureSheaf B S.obj S.property).obj.obj (op Z)) • t := by
      change β.val.app (op Z) (two.val.app (op Z) one) = _
      rw [e1]
      exact (β.val.app (op Z)).hom.map_smul _ _
    have h2 : g.val.app (op Z) one = s'Z := by
      change (1 : (SmallEtale.structureSheaf B S.obj S.property).obj.obj (op Z)) • s'Z = _
      exact one_smul _ _
    exact h1.symm.trans (h.trans h2)
  have key : (2 : (BigEtaleOver.structureSheaf B S.obj S.property).obj.obj (op (F.obj Z))) •
      (show I.val.obj (op (F.obj Z)) from t) = s.val (op (F.obj Z)) := keyJ
  let h : specFTwoOver B ⟶ F.obj Z := Over.homMk (specFTwoOver B).hom (by simp [F, Z,
    SmallEtale.final])
  have hzero : s.val (op (specFTwoOver B)) = 0 := by
    have h2 : (2 : (BigEtaleOver.structureSheaf B S.obj S.property).obj.obj
        (op (specFTwoOver B))) = 0 := by
      change (2 : Γ(Spec (CommRingCat.of (ULift.{u} (ZMod 2))), ⊤)) = 0
      rw [← map_ofNat (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} (ZMod 2)))).inv.hom 2,
        show (2 : ULift.{u} (ZMod 2)) = 0 from rfl, map_zero]
    rw [← PresheafOfModules.sections_property s h.op, ← key, PresheafOfModules.map_smul,
      map_ofNat, h2, zero_smul]
    rfl
  have hα := Stacks.SheafOfModules.injective_app_of_mono α (op (specFTwoOver B))
  have h1 : (ULift.up 1 : ULift.{u + 1} ((BigEtaleOver.structureSheaf B S.obj S.property).obj.obj
      (op (specFTwoOver B)))) = 0 := hα (hzero.trans (map_zero _).symm)
  have h3 : (1 : Γ(Spec (CommRingCat.of (ULift.{u} (ZMod 2))), ⊤)) = 0 := congrArg ULift.down h1
  have h4 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} (ZMod 2)))).hom.hom h3
  rw [map_one, map_zero] at h4
  exact one_ne_zero h4

/-- **Stacks Project, Tag 0758, the module clause, part (1).** Restriction from the big to the
small étale site does not preserve injective modules: for `S = Spec ℤ` there is an injective
`𝒪`-module `ℐ` on `(Sch/S)_étale` such that `ℐ|_{S_étale}` is not an injective `𝒪_S`-module. -/
@[stacks 0758 "module counterexample: parts (1)(a) and (1)(b) do not hold for injective \
O-modules"]
theorem exists_injective_not_injective_smallEtaleModuleRestriction :
    ∃ I : SheafOfModules.{u + 1}
        (BigEtaleOver.structureSheaf B (B.specInt).obj (B.specInt).property),
      Injective I ∧
        ¬ Injective ((smallEtaleModuleRestriction B B.specInt B.specInt (𝟙 B.specInt)).obj I) := by
  have := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, u + 1}
    (BigEtaleOver.structureSheaf B (B.specInt).obj (B.specInt).property)
  exact ⟨Injective.under (bigEtaleModuleUnit B B.specInt), inferInstance,
    not_injective_smallEtaleModuleRestriction_of_mono B _ (Injective.ι _)⟩

/-- `i_f^*` on `𝒪`-modules preserves zero morphisms, being additive. -/
instance smallEtaleModuleRestriction_preservesZeroMorphisms (T S : B.Scheme) (f : T ⟶ S) :
    (smallEtaleModuleRestriction B T S f).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (smallEtaleModuleRestriction B T S f)

/-- `i_f^*` on cochain complexes of sheaves of `𝒪`-modules, degreewise. -/
abbrev smallEtaleModuleRestrictionComplex (T S : B.Scheme) (f : T ⟶ S) :
    CochainComplex (SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property)) ℤ ⥤
      CochainComplex (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B T.obj T.property)) ℤ :=
  (smallEtaleModuleRestriction B T S f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- If `i_f^*` of the complex `ℐ[0]` is K-injective, then so is `(i_f^*ℐ)[0]`, the two
complexes being isomorphic. -/
theorem isKInjective_singleFunctor_obj_smallEtaleModuleRestriction (T S : B.Scheme)
    (f : T ⟶ S)
    (I : SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property))
    (h : ((smallEtaleModuleRestrictionComplex B T S f).obj
      ((CochainComplex.singleFunctor _ 0).obj I)).IsKInjective) :
    ((CochainComplex.singleFunctor _ 0).obj
      ((smallEtaleModuleRestriction B T S f).obj I)).IsKInjective :=
  (CochainComplex.isKInjective_iff_of_iso ((HomologicalComplex.singleMapHomologicalComplex
    (smallEtaleModuleRestriction B T S f) (ComplexShape.up ℤ) 0).app I)).mp h

/-- **Stacks Project, Tag 0758, the module clause, part (2).** Restriction from the big to the
small étale site does not preserve K-injective complexes of modules: for `S = Spec ℤ` there is a
K-injective complex `ℐ^•` of `𝒪`-modules on `(Sch/S)_étale` such that `ℐ^•|_{S_étale}` is not a
K-injective complex of `𝒪_S`-modules. -/
@[stacks 0758 "module counterexample: parts (2)(a) and (2)(b) do not hold for K-injective \
complexes of O-modules"]
theorem exists_isKInjective_not_isKInjective_smallEtaleModuleRestriction :
    ∃ I : CochainComplex (SheafOfModules.{u + 1}
        (BigEtaleOver.structureSheaf B (B.specInt).obj (B.specInt).property)) ℤ,
      I.IsKInjective ∧
        ¬ ((smallEtaleModuleRestrictionComplex B B.specInt B.specInt (𝟙 B.specInt)).obj
          I).IsKInjective := by
  obtain ⟨I, hI, hnot⟩ := exists_injective_not_injective_smallEtaleModuleRestriction B
  refine ⟨(CochainComplex.singleFunctor _ 0).obj I,
    CochainComplex.isKInjective_single_obj_of_injective I 0, fun h => hnot ?_⟩
  have := isKInjective_singleFunctor_obj_smallEtaleModuleRestriction B _ _ _ I h
  exact CochainComplex.injective_of_isKInjective_singleFunctor_obj _

end AlgebraicGeometry
