module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModuleSheafification
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentSectionsModule
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.GeneratingFamily

/-!
# The comparison of the presheaf pullback with the pullback-sections presheaf

The associated-module functor of each of the five big sites of a scheme `S` is the pullback of
sheaves of modules along the morphism of ringed sites `((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)`, and
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleSheafificationIso` presents it as the
`τ`-sheafification of the pullback of *presheaves* of modules.  Stacks Definition 03DU (3)
instead defines it by its sections, `(f : T → S) ↦ Γ(T, f^*F)`, which is the presheaf of modules
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`.  Stacks Lemma 070S (1) identifies the
two, for every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, and this file constructs the
morphism whose local bijectivity is that identification.

The comparison morphism itself does not depend on `τ`: the structure presheaf of all five big
sites over `S` is the same, so `AlgebraicGeometry.BigFppfOver.baseStructureMap` is at every `τ`
*definitionally* the fppf comparison, and so is the presheaf-level pullback along it.  Every
declaration below is stated at a general `τ`, and the fppf forms are the instances at
`τ = .fppf`.

The morphism is the transpose, under
`CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction`, of the map which sends a
section of `F` over an open `U` of `S` to its pullback to the open subscheme `U`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.sectionsUnitApp`: pulling a section of `F` over an open of `S`
  back to the open subscheme, as a map of modules of sections.
* `AlgebraicGeometry.BigFppfOver.sectionsUnit`: the same, as a morphism of presheaves of modules
  out of `F` into the restriction of the pullback-sections presheaf along the inclusion of the
  small Zariski site.
* `AlgebraicGeometry.BigFppfOver.sectionsComparison`: **the comparison of Stacks 070S (1)**, the
  transpose of `sectionsUnit` across the pullback--pushforward adjunction.
* `AlgebraicGeometry.BigFppfOver.openSubObj` and `AlgebraicGeometry.BigFppfOver.openSubHom`: an
  open of the underlying scheme of an object of the big site, as an object of the big site, and
  its open immersion.
* `AlgebraicGeometry.BigFppfOver.affineSubordinateCover`: the Zariski covering of an object by
  those of its affine opens which map into an affine open of `S`.
* `PresheafOfModules.pullbackUnitGenerators` and `PresheafOfModules.pullbackUnitSubmodule`: for
  an arbitrary pullback of presheaves of modules, the restrictions of the images of the unit of
  the pullback--pushforward adjunction, and the subobject they span.
* `AlgebraicGeometry.BigFppfOver.pullbackPresheaf`, `AlgebraicGeometry.BigFppfOver.pullbackUnit`
  and `AlgebraicGeometry.BigFppfOver.pullbackUnitSection`: the source of the comparison, the unit
  of the pullback--pushforward adjunction at `F`, and the generators of the source — the
  restriction to an object of the big site of the image under the unit of a section of `F` over an
  open of `S`.
* `AlgebraicGeometry.BigFppfOver.affineSubordinateCoverOver`: the refinement of
  `AlgebraicGeometry.BigFppfOver.affineSubordinateCover` subordinate to an open of `S`.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleSheafificationIso`: the associated-module
  functor of the indicated big site as the `τ`-sheafification of the pullback of presheaves of
  modules.

## Main results

* `AlgebraicGeometry.Scheme.Opens.top_le_ι_preimage`: an open subscheme lies entirely over any
  larger open.
* `AlgebraicGeometry.BigFppfOver.sectionsUnitApp_apply`: the component of `sectionsUnit` is
  `AlgebraicGeometry.pullbackSectionHom`.
* `AlgebraicGeometry.BigFppfOver.unit_comp_map_sectionsComparison`: the comparison transposes
  back to `sectionsUnit`.
* `AlgebraicGeometry.BigFppfOver.sectionsComparison_unit_app`: the previous statement on a
  single section.
* `AlgebraicGeometry.BigFppfOver.mem_baseTopology_sieve₀_affineSubordinateCover` and
  `AlgebraicGeometry.BigFppfOver.mem_topology_sieve₀_affineSubordinateCover`: the affine opens
  lying over affine opens of `S` cover, for each of the five topologies and for fppf.
* `AlgebraicGeometry.BigFppfOver.surjective_app_sectionsComparison`: **the comparison is
  surjective over an object which is affine and lies over an affine open of `S`.**
* `AlgebraicGeometry.BigFppfOver.isLocallySurjective_sectionsComparison_baseOverTopology` and
  `AlgebraicGeometry.BigFppfOver.isLocallySurjective_sectionsComparison`: **the comparison is
  locally surjective for every `τ`**, which is half of Stacks 070S (1).
* `AlgebraicGeometry.BigFppfOver.isIso_baseSheafification_map_sectionsComparison`,
  `AlgebraicGeometry.BigFppfOver.isIso_sheafification_map_sectionsComparison` and
  `AlgebraicGeometry.BigFppfOver.associatedModuleIsoSectionsSheafification`: Stacks 070S (1),
  stated with local injectivity as an instance argument.
* `PresheafOfModules.mem_pullbackUnitSubmodule` and
  `PresheafOfModules.span_pullbackUnitGenerators_eq_top`: **the pullback of a presheaf of modules
  is generated by the image of the unit.**
* `AlgebraicGeometry.BigFppfOver.sectionsComparison_app_map_unit`: the comparison on a
  generator.
* `AlgebraicGeometry.eq_zero_of_mem_span_of_app_eq_pullbackSection`: **the injective half of the
  affine base-change description**.
* `AlgebraicGeometry.BigFppfOver.exists_mem_span_pullbackUnitSection`: every section of the
  pullback is a combination of generators indexed by a **single** open of `S`.
* `AlgebraicGeometry.BigFppfOver.isLocallyInjective_sectionsComparison_baseOverTopology` and
  `AlgebraicGeometry.BigFppfOver.isLocallyInjective_sectionsComparison`: **the comparison is
  locally injective for every `τ`**, the other half of Stacks 070S (1).
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`: **Stacks 070S (1) and Stacks
  03FH (1)**, for every `τ : AlgebraicGeometry.SiteKind` and with no hypothesis beyond
  quasi-coherence.
* `AlgebraicGeometry.BigFppfOver.associatedModuleIsoSections`: its instance at `τ = .fppf`.

## Implementation notes

`AlgebraicGeometry.eq_zero_of_mem_span_of_app_eq_pullbackSection` is stated for a bare morphism
of schemes rather than for an object of the big site.  The structure morphism of an object of
the big site has target spelled `(B.obj hS).obj` rather than `S`, so the tensor product of
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul` and the one in a statement
written with `Γ(S, U)` are two syntactically different terms whose unification exhausts the
elaborator's recursion depth.  With the schemes as variables the two spellings are identical.
For the same reason the extension of scalars and the base-change isomorphism are introduced by
`obtain`, with exactly the two properties used, rather than by `set`: as opaque local constants
they cannot be unfolded by a later unification.

The submodule in the proof of `AlgebraicGeometry.BigFppfOver.surjective_app_sectionsComparison`
is written out by hand, over the *commutative* ring `Γ(T, 𝒪_T)` rather than over the `RingCat`
object `(structureSheaf B S hS).obj.obj (op T)`.  The two rings and the two module structures
they carry on the sections of the pullback are definitionally equal, and a coercion between them
elaborates, but instance search does not cross the identification: asking for
`Module ↥((structureSheaf B S hS).obj.obj (op T))` on the sections written in the `Γ` notation
fails.  So each side of the argument is stated with the scalars whose instance is found there —
the span over `Γ(T, 𝒪_T)`, the semilinearity of the comparison over the `RingCat` object — and
the two are joined by `rfl`.

The component is built with `CategoryTheory.ModuleCat.homEquiv.symm` rather than
`CategoryTheory.ModuleCat.ofHom`.  The target is a restriction of scalars, whose module
structure is the one carried by the `ModuleCat` object; `ofHom` takes a bare linear map and has
its module structures found by instance search, which unfolds the restriction of scalars and
then fails, whereas `homEquiv` is stated between two given `ModuleCat` objects and so uses
theirs.

For the same reason the two proofs below are `Eq.trans` chains rather than `rewrite` sequences.
The scalars of the small site appear both as a `RingCat` object, through
`AlgebraicGeometry.Scheme.ringCatSheaf`, and as a `CommRingCat` object, through the sections
notation; the module structures over the two are definitionally equal but not syntactically so,
so a `rewrite` whose motive mentions a scalar action is rejected at `implicit` transparency.
Inside `sectionsUnit` the opposite category's object `V` also has its type unfolded to
`TopologicalSpace.Opens`, which is why `AlgebraicGeometry.Scheme.Opens.ι` is applied by name
there instead of by dot notation.

In `AlgebraicGeometry.BigFppfOver.isIso_sheafification_map_sectionsComparison` the local
injectivity instance is passed explicitly: the localized fppf topology is the localized
`τ = .fppf` topology definitionally, but `AlgebraicGeometry.BigFppfSite.baseTopology` is a
pattern match and does not unfold at the transparency instance search uses, so the hypothesis in
that statement is not *found* by instance search for the `.fppf` form of the goal.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry ChangeOfRings

universe u

universe v v₁ v₂ u₁ u₂

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  [(pushforward.{v} φ).IsRightAdjoint] (M : PresheafOfModules.{v} S)

/-- **The generators of the pullback of a presheaf of modules.**  The restrictions, along the
morphisms `X ⟶ F.obj Y` of the target category, of the images of the sections of `M` under the
unit of the pullback--pushforward adjunction. -/
public noncomputable def pullbackUnitGenerators (X : Dᵒᵖ) :
    Set (((pullback.{v} φ).obj M).obj X) :=
  {x | ∃ (Y : C) (g : X.unop ⟶ F.obj Y) (m : M.obj (op Y)),
    x = ((pullback.{v} φ).obj M).map g.op
      (((pullbackPushforwardAdjunction.{v} φ).unit.app M).app (op Y) m)}

/-- The subobject of the pullback of `M` generated by the image of the unit of the
pullback--pushforward adjunction: over an object `X`, the submodule spanned by
`PresheafOfModules.pullbackUnitGenerators`. -/
public noncomputable def pullbackUnitSubmodule : ((pullback.{v} φ).obj M).Submodule where
  obj X := Submodule.span (R.obj X) (pullbackUnitGenerators φ M X)
  map {X Y} f := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨Z, g, m, rfl⟩
    refine Submodule.subset_span ⟨Z, f.unop ≫ g, m, ?_⟩
    exact (((pullback.{v} φ).obj M).map_comp_apply g.op f _).symm

/-- The image of a section of `M` under the unit lies in
`PresheafOfModules.pullbackUnitSubmodule`. -/
public theorem mem_pullbackUnitSubmodule_unit_app (X : Cᵒᵖ) (m : M.obj X) :
    ((pullbackPushforwardAdjunction.{v} φ).unit.app M).app X m ∈
      (pullbackUnitSubmodule φ M).obj (op (F.obj X.unop)) := by
  have h : ∀ (N : PresheafOfModules.{v} R) (Z : Dᵒᵖ) (x : N.obj Z), N.map (𝟙 Z) x = x := by
    intro N Z x
    simp only [N.map_id]
    rfl
  exact Submodule.subset_span ⟨X.unop, 𝟙 _, m, (h _ _ _).symm⟩

/-- The unit of the pullback--pushforward adjunction, corestricted to
`PresheafOfModules.pullbackUnitSubmodule`. -/
public noncomputable def pullbackUnitCorestriction :
    M ⟶ (pushforward.{v} φ).obj (pullbackUnitSubmodule φ M).toPresheafOfModules where
  app X := ModuleCat.homEquiv.symm
    { toFun := fun m => ⟨((pullbackPushforwardAdjunction.{v} φ).unit.app M).app X m,
        mem_pullbackUnitSubmodule_unit_app φ M X m⟩
      map_add' := fun a b =>
        Subtype.ext (map_add (((pullbackPushforwardAdjunction.{v} φ).unit.app M).app X).hom a b)
      map_smul' := fun r a =>
        Subtype.ext
          ((((pullbackPushforwardAdjunction.{v} φ).unit.app M).app X).hom.map_smul r a) }
  naturality {X Y} f := by
    ext m
    exact Subtype.ext
      (naturality_apply ((pullbackPushforwardAdjunction.{v} φ).unit.app M) f m)

/-- The transpose of `PresheafOfModules.pullbackUnitCorestriction` across the
pullback--pushforward adjunction. -/
public noncomputable def pullbackToUnitSubmodule :
    (pullback.{v} φ).obj M ⟶ (pullbackUnitSubmodule φ M).toPresheafOfModules :=
  ((pullbackPushforwardAdjunction.{v} φ).homEquiv _ _).symm (pullbackUnitCorestriction φ M)

/-- **The inclusion of the submodule generated by the unit is split epi.**
`PresheafOfModules.pullbackToUnitSubmodule` followed by the inclusion of
`PresheafOfModules.pullbackUnitSubmodule` is the identity. -/
public theorem pullbackToUnitSubmodule_comp_ι :
    pullbackToUnitSubmodule φ M ≫ (pullbackUnitSubmodule φ M).ι = 𝟙 _ := by
  apply ((pullbackPushforwardAdjunction.{v} φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, pullbackToUnitSubmodule, Equiv.apply_symm_apply,
    Adjunction.homEquiv_unit]
  ext X m
  rfl

/-- **The pullback of a presheaf of modules is generated by the image of the unit.**  Every
section of `(pullback φ).obj M` over an object `X` is a combination, with coefficients in
`R.obj X`, of restrictions along morphisms `X ⟶ F.obj Y` of images under the unit of the
pullback--pushforward adjunction of sections of `M` over objects `Y`. -/
public theorem mem_pullbackUnitSubmodule (X : Dᵒᵖ) (p : ((pullback.{v} φ).obj M).obj X) :
    p ∈ (pullbackUnitSubmodule φ M).obj X := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun k : (pullback.{v} φ).obj M ⟶ (pullback.{v} φ).obj M => Hom.app k X)
      (pullbackToUnitSubmodule_comp_ι φ M)) p
  have h2 : (Hom.app (pullbackToUnitSubmodule φ M) X p).1 = p := h
  exact h2 ▸ (Hom.app (pullbackToUnitSubmodule φ M) X p).2

/-- **The pullback of a presheaf of modules is generated by the image of the unit**, as a span.
This is `PresheafOfModules.mem_pullbackUnitSubmodule` read as an equality of
submodules. -/
public theorem span_pullbackUnitGenerators_eq_top (X : Dᵒᵖ) :
    Submodule.span (R.obj X) (pullbackUnitGenerators φ M X) = ⊤ :=
  le_antisymm le_top fun p _ => mem_pullbackUnitSubmodule φ M X p

end PresheafOfModules


namespace AlgebraicGeometry

/-- The whole of an open subscheme lies over any larger open. -/
public theorem Scheme.Opens.top_le_ι_preimage {X : Scheme.{u}} {V U : X.Opens} (h : V ≤ U) :
    (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ U :=
  fun x _ => h x.2

/-- **A combination of pulled-back sections which the comparison kills is zero, over an affine
pair.**  Let `f : Y ⟶ X`, let `F` be a quasi-coherent module on `X` and let `U` and `V` be affine
opens of `X` and of `Y` with `V ≤ f⁻¹U`.  Let `N` be a module over the functions on `V`, let `s`
carry a section of `F` over `U` to an element of `N`, additively and semilinearly over
`AlgebraicGeometry.Scheme.Hom.appLE`, and let `θ : N ⟶ Γ(f^*F, V)` carry `s a` to the pullback of
the section `a`.  Then nothing in the span of the `s a` is killed by `θ` except `0`. -/
public theorem eq_zero_of_mem_span_of_app_eq_pullbackSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) {N : ModuleCat.{u} Γ(Y, V)} (s : Γ(F, U) → N)
    (hadd : ∀ a b, s (a + b) = s a + s b)
    (hsmul : ∀ (r : Γ(X, U)) (a : Γ(F, U)), s (r • a) = f.appLE U V hVU r • s a)
    (θ : N ⟶ ModuleCat.of Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V))
    (hsθ : ∀ a : Γ(F, U), θ (s a) = Scheme.Modules.pullbackSection f F U V hVU a)
    {x : N} (hx : x ∈ Submodule.span Γ(Y, V) (Set.range s)) (hθx : θ x = 0) : x = 0 := by
  set sm : ModuleCat.of Γ(X, U) Γ(F, U) ⟶
      (ModuleCat.restrictScalars (f.appLE U V hVU).hom).obj N :=
    ModuleCat.semilinearMapAddEquiv _ _ _
      { toFun := s, map_add' := hadd, map_smul' := hsmul } with hsm
  obtain ⟨κ, hκ1⟩ : ∃ κ : (ModuleCat.extendScalars (f.appLE U V hVU).hom).obj
        (ModuleCat.of Γ(X, U) Γ(F, U)) ⟶ N,
      ∀ a : Γ(F, U),
        ModuleCat.Hom.hom κ ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a) = s a :=
    ⟨((ModuleCat.extendRestrictScalarsAdj (f.appLE U V hVU).hom).homEquiv _ _).symm sm,
      fun a => congrArg (fun k => ModuleCat.Hom.hom k a)
        (Equiv.apply_symm_apply
          ((ModuleCat.extendRestrictScalarsAdj (f.appLE U V hVU).hom).homEquiv
            (ModuleCat.of Γ(X, U) Γ(F, U)) N) sm)⟩
  obtain ⟨e, he1⟩ : ∃ e : (ModuleCat.extendScalars (f.appLE U V hVU).hom).obj
        (ModuleCat.of Γ(X, U) Γ(F, U)) ≅
        ModuleCat.of Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V),
      ∀ a : Γ(F, U), ModuleCat.Hom.hom e.hom
          ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a) =
        Scheme.Modules.pullbackSection f F U V hVU a :=
    ⟨affinePullbackSectionsBaseChangeIso f F hU hV hVU,
      affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV hVU⟩
  have hτ : e.hom ≫ (e.inv ≫ κ) = κ := by
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
  have hinv : ∀ y : (ModuleCat.extendScalars (f.appLE U V hVU).hom).obj
        (ModuleCat.of Γ(X, U) Γ(F, U)),
      ModuleCat.Hom.hom (e.inv ≫ κ) (ModuleCat.Hom.hom e.hom y)
        = ModuleCat.Hom.hom κ y := fun y =>
    (ModuleCat.comp_apply e.hom (e.inv ≫ κ) y).symm.trans
      (congrArg (fun k => ModuleCat.Hom.hom k y) hτ)
  have hgen : ∀ a : Γ(F, U), ModuleCat.Hom.hom (θ ≫ e.inv ≫ κ) (s a) = s a := by
    intro a
    refine Eq.trans (congrArg (fun z => ModuleCat.Hom.hom (e.inv ≫ κ) z)
      ((hsθ a).trans (he1 a).symm)) ?_
    exact (hinv _).trans (hκ1 a)
  have hxZ : ModuleCat.Hom.hom (θ ≫ e.inv ≫ κ) x = x := by
    refine Submodule.span_induction
      (p := fun y _ => ModuleCat.Hom.hom (θ ≫ e.inv ≫ κ) y = y) ?_ (map_zero _) ?_ ?_ hx
    · rintro y ⟨a, rfl⟩
      exact hgen a
    · intro p q _ _ hp hq
      rw [map_add, hp, hq]
    · intro c p _ hp
      rw [map_smul, hp]
  refine hxZ.symm.trans ?_
  exact (congrArg (fun z => ModuleCat.Hom.hom (e.inv ≫ κ) z) hθx).trans (map_zero _)

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pulling a section of `F` over an open `U` of `S` back to the open subscheme `U`, as a map
of sections over `U`.  This is the component of `AlgebraicGeometry.BigFppfOver.sectionsUnit`. -/
public noncomputable def sectionsUnitApp (F : S.Modules) [F.IsQuasicoherent]
    (U : (S.Opens)ᵒᵖ) :
    ((SheafOfModules.forget S.ringCatSheaf).obj F).obj U ⟶
      ((PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (sectionsPresheafOfModules B S hS F)).obj U :=
  ModuleCat.homEquiv.symm {
    toFun := fun a =>
      pullbackSectionHom U.unop.ι F U.unop ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) a
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r a => by
      refine (pullbackSectionHom_smul U.unop.ι F U.unop ⊤
        (Scheme.Opens.top_le_ι_preimage le_rfl) r a).trans ?_
      exact congrArg
        (fun s : Γ(U.unop.toScheme, ⊤) => s • pullbackSectionHom U.unop.ι F U.unop ⊤
          (Scheme.Opens.top_le_ι_preimage le_rfl) a)
        (congrArg (fun g : Γ(S, U.unop) ⟶ Γ(U.unop, ⊤) => ConcreteCategory.hom g r)
          (Scheme.Opens.ι_appLE_top U.unop (Scheme.Opens.top_le_ι_preimage le_rfl))) }

/-- The component of `sectionsUnitApp` at `U` sends a section `a` of `F` over `U` to its pullback
`pullbackSectionHom U.unop.ι F U.unop ⊤ _ a` over all of the open subscheme `U`. -/
@[simp]
public theorem sectionsUnitApp_apply (F : S.Modules) [F.IsQuasicoherent] (U : (S.Opens)ᵒᵖ)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj U) :
    sectionsUnitApp B S hS F U a =
      pullbackSectionHom U.unop.ι F U.unop ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) a :=
  rfl

/-- **Pulling sections back, as a morphism out of `F`.**  A section of `F` over an open `U` of
`S` pulls back to a section of `U.ι^*F` over all of the open subscheme `U`, and this is natural
in `U`: it is a morphism from `F` to the restriction, along the inclusion of the small Zariski
site of `S`, of the pullback-sections presheaf of modules of the big fppf site. -/
public noncomputable def sectionsUnit (F : S.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.forget S.ringCatSheaf).obj F ⟶
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (sectionsPresheafOfModules B S hS F) where
  app U := sectionsUnitApp B S hS F U
  naturality {U V} h := by
    ext a
    have hUV : V.unop ≤ U.unop := leOfHom h.unop
    refine Eq.trans (pullbackSectionHom_map (Scheme.Opens.ι V.unop) F U.unop V.unop hUV ⊤
      (Scheme.Opens.top_le_ι_preimage le_rfl) (Scheme.Opens.top_le_ι_preimage hUV) a) ?_
    exact (pullbackSectionsMap_pullbackSectionHom F
      ((Over.post (X := B.obj hS) B.inclusion).map ((opensToBig B S hS).map h.unop))
      U.unop (Scheme.Opens.top_le_ι_preimage le_rfl)
      (Scheme.Opens.top_le_ι_preimage hUV) a).symm

/-- **The comparison of Stacks 070S (1).**  The canonical morphism from the pullback of
presheaves of modules along the structure-sheaf comparison of the big fppf site of `S` to the
pullback-sections presheaf of Stacks 03DS: the transpose, under
`CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction`, of the map which pulls a
section of `F` over an open `U` of `S` back to the open subscheme `U`. -/
public noncomputable def sectionsComparison (F : S.Modules) [F.IsQuasicoherent] :
    (PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
        ((SheafOfModules.forget S.ringCatSheaf).obj F) ⟶
      sectionsPresheafOfModules B S hS F :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom).homEquiv
    _ _).symm (sectionsUnit B S hS F)

/-- **The comparison is determined by pulling sections back.**  Transposing
`AlgebraicGeometry.BigFppfOver.sectionsComparison` back across the adjunction returns the map
which pulls a section of `F` over an open `U` of `S` back to the open subscheme `U`. -/
public theorem unit_comp_map_sectionsComparison (F : S.Modules) [F.IsQuasicoherent] :
    (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom).unit.app
          ((SheafOfModules.forget S.ringCatSheaf).obj F) ≫
        (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
          (sectionsComparison B S hS F) =
      sectionsUnit B S hS F :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (structureMap B S hS).hom).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- **The comparison, on a pulled-back section over an open of `S`.**  The component of
`AlgebraicGeometry.BigFppfOver.sectionsComparison` at the object `U → S` of the big site carries
the image of a section `a` of `F` over `U` under the unit of the pullback--pushforward adjunction
to the pullback of `a` to the open subscheme `U`.  This is
`AlgebraicGeometry.BigFppfOver.unit_comp_map_sectionsComparison` evaluated at `U` and applied to
`a`. -/
public theorem sectionsComparison_unit_app (F : S.Modules) [F.IsQuasicoherent] (U : S.Opens)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj (op U)) :
    (sectionsComparison B S hS F).app (op ((opensToBig B S hS).obj U))
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (structureMap B S hS).hom).unit.app
          ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a) =
      pullbackSectionHom U.ι F U ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) a := by
  have h := unit_comp_map_sectionsComparison B S hS F
  have h2 := congrArg (fun k : (SheafOfModules.forget S.ringCatSheaf).obj F ⟶
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (sectionsPresheafOfModules B S hS F) => PresheafOfModules.Hom.app k (op U)) h
  rw [PresheafOfModules.comp_app] at h2
  exact ConcreteCategory.congr_hom h2 a

/-- **The comparison is surjective over an affine object lying over an affine open.**  If the
underlying scheme of an object `T` of the big fppf site over `S` is affine and the structure
morphism of `T` factors through an affine open `U` of `S`, then the component of
`AlgebraicGeometry.BigFppfOver.sectionsComparison` at `T` is surjective. -/
public theorem surjective_app_sectionsComparison (F : S.Modules) [F.IsQuasicoherent]
    {T : BigFppfOver B S hS} {U : S.Opens} (hU : IsAffineOpen U)
    (hT : IsAffineOpen (⊤ : ((toScheme B S hS).obj T).Opens))
    (j : T ⟶ (opensToBig B S hS).obj U) :
    Function.Surjective (ModuleCat.Hom.hom ((sectionsComparison B S hS F).app (op T))) := by
  have hX : (⊤ : ((toScheme B S hS).obj T).Opens) ≤ T.hom.hom ⁻¹ᵁ U :=
    fun x _ => range_le_of_hom B S hS j ⟨x, rfl⟩
  have hmem : ∀ a : Γ(F, U), ∃ x, ModuleCat.Hom.hom
      ((sectionsComparison B S hS F).app (op T)) x =
      (pullbackSectionHom T.hom.hom F U ⊤ hX a :
        Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤)) := by
    intro a
    refine ⟨((PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
      ((SheafOfModules.forget S.ringCatSheaf).obj F)).map j.op
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (structureMap B S hS).hom).unit.app
            ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a), ?_⟩
    refine Eq.trans
      (PresheafOfModules.naturality_apply (sectionsComparison B S hS F) j.op _) ?_
    refine Eq.trans (congrArg (fun z => (sectionsPresheafOfModules B S hS F).map j.op z)
      (sectionsComparison_unit_app B S hS F U a)) ?_
    exact pullbackSectionsMap_pullbackSectionHom F
      ((Over.post (X := B.obj hS) B.inclusion).map j) U
      (Scheme.Opens.top_le_ι_preimage le_rfl) hX a
  let Q : Submodule Γ((toScheme B S hS).obj T, ⊤)
      Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤) :=
    { carrier := {y | ∃ x, ModuleCat.Hom.hom
        ((sectionsComparison B S hS F).app (op T)) x = y}
      add_mem' := by
        rintro y z ⟨p, hp⟩ ⟨q, hq⟩
        exact ⟨p + q, by rw [map_add, hp, hq]; rfl⟩
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro c y ⟨p, hp⟩
        refine ⟨(show (structureSheaf B S hS).obj.obj (op T) from c) • p, ?_⟩
        rw [map_smul, hp]
        rfl }
  have hle : Submodule.span Γ((toScheme B S hS).obj T, ⊤)
      (Set.range fun a : Γ(F, U) => pullbackSectionHom T.hom.hom F U ⊤ hX a) ≤ Q :=
    Submodule.span_le.2 (by rintro z ⟨a, rfl⟩; exact hmem a)
  intro y
  refine hle ?_
  exact (span_pullbackSection_eq_top T.hom.hom F hU hT hX).ge Submodule.mem_top

/-- An open of the underlying scheme of an object of the big fppf site over `S`, as an object of
the big fppf site over `S`: its structure morphism is the open immersion followed by the
structure morphism, and it is below the size cutoff by
`AlgebraicGeometry.BigFppfOver.contains_opens`. -/
@[implicit_reducible]
public def openSubObj (T : BigFppfOver B S hS) (V : T.left.obj.Opens) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj (contains_opens B T.left.property V))
    (Y := B.obj hS) (V.ι ≫ T.hom.hom))

/-- The structure morphism of `openSubObj B S hS T V` is `V.ι ≫ T.hom.hom`. -/
@[simp]
public theorem openSubObj_hom_hom (T : BigFppfOver B S hS) (V : T.left.obj.Opens) :
    (openSubObj B S hS T V).hom.hom = V.ι ≫ T.hom.hom := rfl

/-- The open immersion of an open of the underlying scheme of an object of the big fppf site
over `S`, as a morphism of the big fppf site over `S`. -/
@[implicit_reducible]
public noncomputable def openSubHom (T : BigFppfOver B S hS) (V : T.left.obj.Opens) :
    openSubObj B S hS T V ⟶ T :=
  Over.homMk (ObjectProperty.homMk (X := B.obj (contains_opens B T.left.property V)) V.ι)
    (by apply ObjectProperty.hom_ext; rw [ObjectProperty.FullSubcategory.comp_hom]; rfl)

/-- On underlying schemes, `openSubHom B S hS T V` is the open immersion `V.ι`. -/
@[simp]
public theorem openSubHom_left_hom (T : BigFppfOver B S hS) (V : T.left.obj.Opens) :
    (openSubHom B S hS T V).left.hom = V.ι := rfl

/-- **The inclusion of one open of an object of the big fppf site over `S` in a larger one**, as
a morphism of the site. On underlying schemes it is `AlgebraicGeometry.Scheme.homOfLE`. -/
@[implicit_reducible]
public noncomputable def openSubHomOfLE (T : BigFppfOver B S hS) {V W : T.left.obj.Opens}
    (hVW : V ≤ W) : openSubObj B S hS T V ⟶ openSubObj B S hS T W :=
  Over.homMk (ObjectProperty.homMk
      (X := B.obj (contains_opens B T.left.property V))
      (Y := B.obj (contains_opens B T.left.property W)) (T.left.obj.homOfLE hVW))
    (by
      apply ObjectProperty.hom_ext
      rw [ObjectProperty.FullSubcategory.comp_hom]
      change T.left.obj.homOfLE hVW ≫ W.ι ≫ T.hom.hom = V.ι ≫ T.hom.hom
      rw [← Category.assoc, Scheme.homOfLE_ι])

/-- For opens `V ≤ W`, the inclusion `openSubHomOfLE B S hS T hVW` followed by
`openSubHom B S hS T W` is `openSubHom B S hS T V`. -/
@[simp]
public theorem openSubHomOfLE_comp_openSubHom (T : BigFppfOver B S hS)
    {V W : T.left.obj.Opens} (hVW : V ≤ W) :
    openSubHomOfLE B S hS T hVW ≫ openSubHom B S hS T W = openSubHom B S hS T V := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show T.left.obj.homOfLE hVW ≫ W.ι = V.ι
  exact Scheme.homOfLE_ι _ hVW

/-- **The covering of an object by its affine opens lying over affine opens of `S`.**  Its index
type is the pairs of an affine open `V` of the underlying scheme of `T` and an affine open `U` of
`S` with `V ≤ T.hom⁻¹U`, and its members are the open immersions of those `V`. -/
public noncomputable def affineSubordinateCover (T : BigFppfOver B S hS) :
    PreZeroHypercover.{u + 1} T where
  I₀ := ULift.{u + 1} (Σ V : T.left.obj.affineOpens,
    {U : S.affineOpens // V.1 ≤ T.hom.hom ⁻¹ᵁ U.1})
  X i := openSubObj B S hS T i.down.1.1
  f i := openSubHom B S hS T i.down.1.1

/-- A family of open immersions whose images cover is an fppf covering family of the chosen
category of schemes. -/
private theorem isFppfCovering_of_forall_exists (T : BigFppfOver B S hS)
    (E : PreZeroHypercover.{u + 1} T)
    (hsurj : ∀ x : T.left.obj, ∃ i, x ∈ Set.range ⇑(E.f i).left.hom)
    (himm : ∀ i, IsOpenImmersion (E.f i).left.hom) :
    IsFppfCovering (κ := B.cutoff) ⟨T.left, E.map (Over.forget (B.obj hS))⟩ := by
  show Presieve.map B.inclusion (E.map (Over.forget (B.obj hS))).presieve₀ ∈
      Scheme.fppfPrecoverage.coverings _
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
  refine Scheme.zariskiPrecoverage_le_fppfPrecoverage _ ?_
  rw [Scheme.zariskiPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨hsurj, himm⟩

/-- The covering of an object by the affine opens lying over affine opens of `S` is an fppf
covering family of the chosen category of schemes. -/
public theorem isFppfCovering_affineSubordinateCover (T : BigFppfOver B S hS) :
    IsFppfCovering (κ := B.cutoff)
      ⟨T.left, (affineSubordinateCover B S hS T).map (Over.forget (B.obj hS))⟩ := by
  refine isFppfCovering_of_forall_exists B S hS T _ (fun x => ?_)
    (fun i => inferInstanceAs (IsOpenImmersion (i.down.1.1.ι)))
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := T.hom.hom.base x) (U := (⊤ : S.Opens)) trivial
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (X := T.left.obj) (x := x) (U := T.hom.hom ⁻¹ᵁ U) hxU
  exact ⟨⟨⟨⟨V, hV⟩, ⟨U, hU⟩, hVU⟩⟩, ⟨⟨x, hxV⟩, rfl⟩⟩

/-- A family of open immersions which is an fppf covering family generates a covering sieve for
the localization at `S` of each of the five big topologies. -/
private theorem sieve₀_mem_baseOverTopology_of_isFppfCovering (τ : SiteKind)
    (T : BigFppfOver B S hS) (E : PreZeroHypercover.{u + 1} T)
    (hE : IsFppfCovering (κ := B.cutoff) ⟨T.left, E.map (Over.forget (B.obj hS))⟩)
    (himm : ∀ i, IsOpenImmersion (B.inclusion.map ((E.map (Over.forget (B.obj hS))).f i))) :
    E.sieve₀ ∈ baseOverTopology B S hS τ T := by
  have hfppf : ((E.map (Over.forget (B.obj hS))).map B.inclusion).presieve₀ ∈
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)).coverings
        (B.inclusion.obj T.left) := by
    rw [PreZeroHypercover.presieve₀_map]
    exact hE
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact sieve₀_mem_baseTopology_of_isOpenImmersion B τ (E.map (Over.forget (B.obj hS)))
    ((Scheme.presieve₀_mem_precoverage_iff _).1 hfppf).1 himm

/-- **The affine opens lying over affine opens of `S` cover, for each of the five topologies.**
The sieve generated by `AlgebraicGeometry.BigFppfOver.affineSubordinateCover` is a covering sieve
for the localization at `S` of each of the five big topologies on the chosen category of
schemes. -/
public theorem mem_baseTopology_sieve₀_affineSubordinateCover (τ : SiteKind)
    (T : BigFppfOver B S hS) :
    (affineSubordinateCover B S hS T).sieve₀ ∈ baseOverTopology B S hS τ T :=
  sieve₀_mem_baseOverTopology_of_isFppfCovering B S hS τ T _
    (isFppfCovering_affineSubordinateCover B S hS T)
    (fun i => inferInstanceAs (IsOpenImmersion (i.down.1.1.ι)))

/-- **The affine opens lying over affine opens of `S` cover.**  The fppf case of
`AlgebraicGeometry.BigFppfOver.mem_baseTopology_sieve₀_affineSubordinateCover`, the localized
fppf topology being the localized `τ = .fppf` topology. -/
public theorem mem_topology_sieve₀_affineSubordinateCover (T : BigFppfOver B S hS) :
    (affineSubordinateCover B S hS T).sieve₀ ∈ topology B S hS T :=
  mem_baseTopology_sieve₀_affineSubordinateCover B S hS .fppf T

/-- **The comparison is surjective over an affine open lying over an affine open of `S`.**  The
case of `AlgebraicGeometry.BigFppfOver.surjective_app_sectionsComparison` which the members of
`AlgebraicGeometry.BigFppfOver.affineSubordinateCover` fall under. -/
public theorem surjective_app_sectionsComparison_openSubObj (F : S.Modules)
    [F.IsQuasicoherent] (T : BigFppfOver B S hS) {V : T.left.obj.Opens} (hV : IsAffineOpen V)
    {U : S.Opens} (hU : IsAffineOpen U) (hVU : V ≤ T.hom.hom ⁻¹ᵁ U) :
    Function.Surjective (ModuleCat.Hom.hom
      ((sectionsComparison B S hS F).app (op (openSubObj B S hS T V)))) := by
  have : IsAffine V.toScheme := hV
  refine surjective_app_sectionsComparison B S hS F hU (isAffineOpen_top V.toScheme)
    (homOfRangeLe B S hS U ?_)
  rintro x ⟨y, rfl⟩
  exact hVU y.2

/-- **The comparison of Stacks 070S (1) is locally surjective, for every one of the five
topologies.**  Every section of the pullback-sections presheaf is, locally for the localized
`τ`-topology, in the image of `AlgebraicGeometry.BigFppfOver.sectionsComparison`.

This is half of Stacks 070S (1); the other half is
`AlgebraicGeometry.BigFppfOver.isLocallyInjective_sectionsComparison_baseOverTopology`. -/
public instance isLocallySurjective_sectionsComparison_baseOverTopology (τ : SiteKind)
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsLocallySurjective (baseOverTopology B S hS τ)
      ((PresheafOfModules.toPresheaf (FibredSite.baseRingStructureSheaf B S hS τ).obj).map
        (sectionsComparison B S hS F)) where
  imageSieve_mem {T} s := by
    refine (baseOverTopology B S hS τ).superset_covering ?_
      (mem_baseTopology_sieve₀_affineSubordinateCover B S hS τ T)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact surjective_app_sectionsComparison_openSubObj B S hS F T i.down.1.2 i.down.2.1.2
      i.down.2.2 _

/-- **The comparison of Stacks 070S (1) is locally surjective.**  The fppf case of
`AlgebraicGeometry.BigFppfOver.isLocallySurjective_sectionsComparison_baseOverTopology`. -/
public instance isLocallySurjective_sectionsComparison (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsLocallySurjective (topology B S hS)
      ((PresheafOfModules.toPresheaf (structureSheaf B S hS).obj).map
        (sectionsComparison B S hS F)) :=
  isLocallySurjective_sectionsComparison_baseOverTopology B S hS .fppf F

/-- The identity of the underlying presheaf of rings of the structure sheaf of the indicated big
site is locally injective. -/
public instance isLocallyInjective_id_baseRingStructureSheaf (τ : SiteKind) :
    Presheaf.IsLocallyInjective (baseOverTopology B S hS τ)
      (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h => by exact h

/-- The identity of the underlying presheaf of rings of the structure sheaf of the indicated big
site is locally surjective. -/
public instance isLocallySurjective_id_baseRingStructureSheaf (τ : SiteKind) :
    Presheaf.IsLocallySurjective (baseOverTopology B S hS τ)
      (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj) :=
  inferInstance

/-- **Granted local injectivity, the comparison sheafifies to an isomorphism, for every one of
the five topologies.**  If `AlgebraicGeometry.BigFppfOver.sectionsComparison` is locally
injective for the localized `τ`-topology, its `τ`-sheafification is an isomorphism. -/
public theorem isIso_baseSheafification_map_sectionsComparison (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent]
    [Presheaf.IsLocallyInjective (baseOverTopology B S hS τ)
      ((PresheafOfModules.toPresheaf (FibredSite.baseRingStructureSheaf B S hS τ).obj).map
        (sectionsComparison B S hS F))] :
    IsIso ((PresheafOfModules.sheafification.{u}
        (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
      (sectionsComparison B S hS F)) := by
  have hW : (baseOverTopology B S hS τ).W
      ((PresheafOfModules.toPresheaf (FibredSite.baseRingStructureSheaf B S hS τ).obj).map
        (sectionsComparison B S hS F)) :=
    GrothendieckTopology.W_of_isLocallyBijective _ _
  rw [GrothendieckTopology.W_iff] at hW
  exact (isIso_iff_of_reflects_iso
    ((PresheafOfModules.sheafification.{u}
        (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
      (sectionsComparison B S hS F))
    (SheafOfModules.toSheaf (FibredSite.baseRingStructureSheaf B S hS τ))).1 hW

/-- **Granted local injectivity, the comparison sheafifies to an isomorphism.**  The fppf case of
`AlgebraicGeometry.BigFppfOver.isIso_baseSheafification_map_sectionsComparison`. -/
public theorem isIso_sheafification_map_sectionsComparison (F : S.Modules)
    [F.IsQuasicoherent]
    [hinj : Presheaf.IsLocallyInjective (topology B S hS)
      ((PresheafOfModules.toPresheaf (structureSheaf B S hS).obj).map
        (sectionsComparison B S hS F))] :
    IsIso ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
      (sectionsComparison B S hS F)) :=
  @isIso_baseSheafification_map_sectionsComparison B S hS .fppf F _ hinj

/-- **Stacks 070S (1), granted local injectivity of the comparison.**  The associated module of a
quasi-coherent module `F` on `S` is the fppf sheafification of the pullback-sections presheaf
`(f : T → S) ↦ Γ(T, f⁺F)` of Stacks 03DS.  This is
`AlgebraicGeometry.BigFppfOver.associatedModuleSheafificationIso`, which presents the associated
module as the sheafification of the presheaf-level pullback, followed by the sheafification of
`AlgebraicGeometry.BigFppfOver.sectionsComparison`. -/
public noncomputable def associatedModuleIsoSectionsSheafification (F : S.Modules)
    [F.IsQuasicoherent]
    [Presheaf.IsLocallyInjective (topology B S hS)
      ((PresheafOfModules.toPresheaf (structureSheaf B S hS).obj).map
        (sectionsComparison B S hS F))] :
    (associatedModule B S hS).obj F ≅
      (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).obj
        (sectionsPresheafOfModules B S hS F) :=
  (associatedModuleSheafificationIso B S hS).app F ≪≫
    @asIso _ _ _ _ _ (isIso_sheafification_map_sectionsComparison B S hS F)

/-- **The comparison on a restricted pulled-back section.**  Over an object `T` of the big site
whose structure morphism factors through an open `U` of `S`, the component of
`AlgebraicGeometry.BigFppfOver.sectionsComparison` carries the restriction to `T` of the unit's
image of a section `a` of `F` over `U` to the pullback of `a` to `T`. -/
public theorem sectionsComparison_app_map_unit (F : S.Modules) [F.IsQuasicoherent]
    {T : BigFppfOver B S hS} {U : S.Opens} (j : T ⟶ (opensToBig B S hS).obj U)
    (hX : (⊤ : ((toScheme B S hS).obj T).Opens) ≤ T.hom.hom ⁻¹ᵁ U)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj (op U)) :
    ModuleCat.Hom.hom ((sectionsComparison B S hS F).app (op T))
        (((PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
          ((SheafOfModules.forget S.ringCatSheaf).obj F)).map j.op
            (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
              (structureMap B S hS).hom).unit.app
                ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a)) =
      (pullbackSectionHom T.hom.hom F U ⊤ hX a :
        Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤)) := by
  refine Eq.trans
    (PresheafOfModules.naturality_apply (sectionsComparison B S hS F) j.op _) ?_
  refine Eq.trans (congrArg (fun z => (sectionsPresheafOfModules B S hS F).map j.op z)
    (sectionsComparison_unit_app B S hS F U a)) ?_
  exact pullbackSectionsMap_pullbackSectionHom F
    ((Over.post (X := B.obj hS) B.inclusion).map j) U
    (Scheme.Opens.top_le_ι_preimage le_rfl) hX a


/-- **The source of the comparison of Stacks 070S (1).**  The pullback, as a presheaf of modules,
of a quasi-coherent module `F` on `S` along the structure-sheaf comparison of the big fppf site;
`AlgebraicGeometry.BigFppfOver.associatedModuleSheafificationIso` presents the associated module
of `F` as its sheafification. -/
public noncomputable abbrev pullbackPresheaf (F : S.Modules) [F.IsQuasicoherent] :
    PresheafOfModules.{u} (structureSheaf B S hS).obj :=
  (PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
    ((SheafOfModules.forget S.ringCatSheaf).obj F)

/-- The unit of the pullback--pushforward adjunction at a quasi-coherent module `F` on `S`.  Over
an open `U` of `S` it sends a section of `F` to a section of
`AlgebraicGeometry.BigFppfOver.pullbackPresheaf` over the object `U → S` of the big site. -/
public noncomputable abbrev pullbackUnit (F : S.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.forget S.ringCatSheaf).obj F ⟶
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (pullbackPresheaf B S hS F) :=
  (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom).unit.app
    ((SheafOfModules.forget S.ringCatSheaf).obj F)

/-- **A generator of the source of the comparison.**  Given an object `T` of the big site
factoring through an open `U` of `S` by `j`, the restriction along `j` of the image under the unit
of a section `a` of `F` over `U`.  These are the elements of
`PresheafOfModules.pullbackUnitGenerators`, so by
`PresheafOfModules.span_pullbackUnitGenerators_eq_top` they span the sections of
`AlgebraicGeometry.BigFppfOver.pullbackPresheaf` over `T`. -/
public noncomputable abbrev pullbackUnitSection (F : S.Modules) [F.IsQuasicoherent]
    {T : BigFppfOver B S hS} {U : S.Opens} (j : T ⟶ (opensToBig B S hS).obj U) (a : Γ(F, U)) :
    (pullbackPresheaf B S hS F).obj (op T) :=
  (pullbackPresheaf B S hS F).map j.op ((pullbackUnit B S hS F).app (op U) a)

/-- **The scalars along which a generator is semilinear.**  Over an object `T` of the big site
factoring through an open `U` of `S`, restricting a function on `U` to the global functions of the
open subscheme `U` and then along `j` agrees with `AlgebraicGeometry.Scheme.Hom.appLE` of the
structure morphism of `T`. -/
public theorem structureSheaf_map_structureMap_app {T : BigFppfOver B S hS} {U : S.Opens}
    (j : T ⟶ (opensToBig B S hS).obj U)
    (hX : (⊤ : ((toScheme B S hS).obj T).Opens) ≤ T.hom.hom ⁻¹ᵁ U) (r : Γ(S, U)) :
    (structureSheaf B S hS).obj.map j.op ((structureMap B S hS).hom.app (op U) r) =
      T.hom.hom.appLE U ⊤ hX r := by
  have hLE : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (_ : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)),
      f.appLE ⊤ ⊤ ‹_› = f.appTop := fun f _ => Scheme.Hom.appLE_eq_app f
  have e₁ : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := Scheme.Opens.top_le_ι_preimage le_rfl
  have e₂ : (⊤ : ((toScheme B S hS).obj T).Opens) ≤ j.left.hom ⁻¹ᵁ ⊤ := le_rfl
  have hgen : ∀ (f : ((toScheme B S hS).obj T) ⟶ S) (_ : T.hom.hom = f)
      (h : (⊤ : ((toScheme B S hS).obj T).Opens) ≤ f ⁻¹ᵁ U),
      f.appLE U ⊤ h = T.hom.hom.appLE U ⊤ hX := by
    rintro f rfl h
    rfl
  have key : (Scheme.Opens.topIso U).inv ≫ (j.left.hom).appTop = T.hom.hom.appLE U ⊤ hX := by
    rw [← Scheme.Opens.ι_appLE_top U e₁, ← hLE (j.left.hom) e₂]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (hgen _ (hom_hom_eq B S hS j) _)
  exact (CommRingCat.comp_apply _ _ r).symm.trans (ConcreteCategory.congr_hom key r)

/-- The sections of `AlgebraicGeometry.BigFppfOver.pullbackPresheaf` over an object `T` as a
module over the *commutative* ring `Γ(T, 𝒪_T)`, rather than over the `RingCat` object
`(structureSheaf B S hS).obj.obj (op T)` which carries them; the two rings and the two module
structures are definitionally equal. -/
public noncomputable instance module_gamma_pullbackPresheaf (F : S.Modules) [F.IsQuasicoherent]
    (T : BigFppfOver B S hS) :
    Module ↥Γ(T.left.obj, ⊤) ↥((pullbackPresheaf B S hS F).obj (op T)) :=
  inferInstanceAs (Module ((structureSheaf B S hS).obj.obj (op T)) _)

/-- **A generator is semilinear in its section.**  Scaling the section of `F` scales the generator
by the restriction of the scalar to the object. -/
public theorem pullbackUnitSection_smul (F : S.Modules) [F.IsQuasicoherent]
    {T : BigFppfOver B S hS} {U : S.Opens} (j : T ⟶ (opensToBig B S hS).obj U)
    (r : Γ(S, U)) (a : Γ(F, U)) :
    pullbackUnitSection B S hS F j (r • a) =
      (structureSheaf B S hS).obj.map j.op ((structureMap B S hS).hom.app (op U) r) •
        pullbackUnitSection B S hS F j a := by
  refine Eq.trans (congrArg (fun z => (pullbackPresheaf B S hS F).map j.op z)
    (((pullbackUnit B S hS F).app (op U)).hom.map_smul r a)) ?_
  exact PresheafOfModules.map_smul (pullbackPresheaf B S hS F) j.op
    ((structureMap B S hS).hom.app (op U) r) ((pullbackUnit B S hS F).app (op U) a)

/-- The component of `AlgebraicGeometry.BigFppfOver.sectionsComparison` at an object `T`, read as
a map of modules over `Γ(T, 𝒪_T)` rather than over the `RingCat` object of the structure sheaf of
the big site.  The two module structures are definitionally equal, so the underlying function
is unchanged. -/
public noncomputable def sectionsComparisonGamma (F : S.Modules) [F.IsQuasicoherent]
    (T : BigFppfOver B S hS) :
    ModuleCat.of Γ(T.left.obj, ⊤) ((pullbackPresheaf B S hS F).obj (op T)) ⟶
      ModuleCat.of Γ(T.left.obj, ⊤) Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤) :=
  ModuleCat.homEquiv.symm
    { toFun := fun x => (sectionsComparison B S hS F).app (op T) x
      map_add' := fun x y => map_add ((sectionsComparison B S hS F).app (op T)).hom x y
      map_smul' := fun c x =>
        ((sectionsComparison B S hS F).app (op T)).hom.map_smul c x }

/-- A span over the `RingCat` object of the structure sheaf of the big site is a span over
`Γ(T, 𝒪_T)`. -/
public theorem mem_span_gamma_of_mem_span (F : S.Modules) [F.IsQuasicoherent]
    (T : BigFppfOver B S hS) (G : Set ((pullbackPresheaf B S hS F).obj (op T)))
    {x : (pullbackPresheaf B S hS F).obj (op T)}
    (hx : x ∈ Submodule.span ((structureSheaf B S hS).obj.obj (op T)) G) :
    x ∈ Submodule.span Γ(T.left.obj, ⊤) G := by
  refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span Γ(T.left.obj, ⊤) G)
    (fun y hy => Submodule.subset_span hy) (Submodule.zero_mem _) ?_ ?_ hx
  · intro p q _ _ hp hq
    exact Submodule.add_mem _ hp hq
  · intro c p _ hp
    exact Submodule.smul_mem _ c hp

/-- **The comparison kills nothing in the span of the generators over an affine object lying over
an affine open.**  If the underlying scheme of `T` is affine and `T` factors through an affine
open `U` of `S`, then an element of the span of the generators indexed by `U` which the component
of `AlgebraicGeometry.BigFppfOver.sectionsComparison` at `T` sends to `0` is itself `0`. -/
public theorem eq_zero_of_mem_span_pullbackUnitSection (F : S.Modules) [F.IsQuasicoherent]
    {T : BigFppfOver B S hS} {U : S.Opens} (hU : IsAffineOpen U)
    (hT : IsAffineOpen (⊤ : ((toScheme B S hS).obj T).Opens))
    (j : T ⟶ (opensToBig B S hS).obj U)
    {x : (pullbackPresheaf B S hS F).obj (op T)}
    (hx : x ∈ Submodule.span ((structureSheaf B S hS).obj.obj (op T))
      (Set.range fun a : Γ(F, U) => pullbackUnitSection B S hS F j a))
    (hθ : (sectionsComparison B S hS F).app (op T) x = 0) : x = 0 := by
  have hX : (⊤ : ((toScheme B S hS).obj T).Opens) ≤ T.hom.hom ⁻¹ᵁ U :=
    fun y _ => range_le_of_hom B S hS j ⟨y, rfl⟩
  refine eq_zero_of_mem_span_of_app_eq_pullbackSection T.hom.hom F hU hT hX
    (N := ModuleCat.of Γ(T.left.obj, ⊤) ((pullbackPresheaf B S hS F).obj (op T)))
    (fun a => pullbackUnitSection B S hS F j a) ?_ ?_
    (sectionsComparisonGamma B S hS F T) ?_
    (mem_span_gamma_of_mem_span B S hS F T _ hx) hθ
  · intro a b
    exact Eq.trans
      (congrArg (fun z => (pullbackPresheaf B S hS F).map j.op z)
        (map_add ((pullbackUnit B S hS F).app (op U)).hom a b))
      (map_add ((pullbackPresheaf B S hS F).map j.op).hom _ _)
  · intro r a
    refine Eq.trans (pullbackUnitSection_smul B S hS F j r a) ?_
    exact congrArg (fun c => c • pullbackUnitSection B S hS F j a)
      (structureSheaf_map_structureMap_app B S hS j hX r)
  · intro a
    exact (sectionsComparison_app_map_unit B S hS F j hX a).trans
      (pullbackSectionHom_apply T.hom.hom F U ⊤ hX a)

/-- Restricting a generator along a morphism of the big site gives the generator over the same
open of `S`. -/
public theorem pullbackUnitSection_map (F : S.Modules) [F.IsQuasicoherent]
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) {U : S.Opens}
    (j : T ⟶ (opensToBig B S hS).obj U) (j' : T' ⟶ (opensToBig B S hS).obj U) (a : Γ(F, U)) :
    (pullbackPresheaf B S hS F).map g.op (pullbackUnitSection B S hS F j a) =
      pullbackUnitSection B S hS F j' a := by
  have hj : g ≫ j = j' := Subsingleton.elim _ _
  refine Eq.trans
    (PresheafOfModules.map_comp_apply (pullbackPresheaf B S hS F) j.op g.op _).symm ?_
  exact congrArg (fun k : T' ⟶ (opensToBig B S hS).obj U =>
    (pullbackPresheaf B S hS F).map k.op ((pullbackUnit B S hS F).app (op U) a)) hj

/-- **Shrinking the open of `S`.**  The generator indexed by a section `a` over `U` is the
generator indexed by the restriction of `a` to a smaller open `U'`, as soon as the object still
factors through `U'`. -/
public theorem pullbackUnitSection_map_le (F : S.Modules) [F.IsQuasicoherent]
    {T : BigFppfOver B S hS} {U U' : S.Opens} (h : U' ≤ U)
    (j : T ⟶ (opensToBig B S hS).obj U) (j' : T ⟶ (opensToBig B S hS).obj U') (a : Γ(F, U)) :
    pullbackUnitSection B S hS F j'
        (((SheafOfModules.forget S.ringCatSheaf).obj F).map (homOfLE h).op a) =
      pullbackUnitSection B S hS F j a := by
  have hj : j' ≫ (opensToBig B S hS).map (homOfLE h) = j := Subsingleton.elim _ _
  refine Eq.trans (congrArg (fun z => (pullbackPresheaf B S hS F).map j'.op z)
    (PresheafOfModules.naturality_apply (pullbackUnit B S hS F) (homOfLE h).op a)) ?_
  refine Eq.trans (PresheafOfModules.map_comp_apply (pullbackPresheaf B S hS F)
    ((opensToBig B S hS).map (homOfLE h)).op j'.op _).symm ?_
  exact congrArg (fun k : T ⟶ (opensToBig B S hS).obj U =>
    (pullbackPresheaf B S hS F).map k.op ((pullbackUnit B S hS F).app (op U) a)) hj

/-- The span of the generators grows as the open of `S` indexing them shrinks. -/
public theorem span_pullbackUnitSection_mono (F : S.Modules) [F.IsQuasicoherent]
    {T : BigFppfOver B S hS} {U U' : S.Opens} (h : U' ≤ U)
    (j : T ⟶ (opensToBig B S hS).obj U) (j' : T ⟶ (opensToBig B S hS).obj U') :
    Submodule.span ((structureSheaf B S hS).obj.obj (op T))
        (Set.range fun a : Γ(F, U) => pullbackUnitSection B S hS F j a) ≤
      Submodule.span ((structureSheaf B S hS).obj.obj (op T))
        (Set.range fun a : Γ(F, U') => pullbackUnitSection B S hS F j' a) := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨a, rfl⟩
  exact Submodule.subset_span ⟨_, pullbackUnitSection_map_le B S hS F h j j' a⟩

/-- Restriction along a morphism of the big site carries the span of the generators indexed by an
open of `S` into the span of the generators indexed by the same open. -/
public theorem map_mem_span_pullbackUnitSection (F : S.Modules) [F.IsQuasicoherent]
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) {U : S.Opens}
    (j : T ⟶ (opensToBig B S hS).obj U) (j' : T' ⟶ (opensToBig B S hS).obj U)
    {z : (pullbackPresheaf B S hS F).obj (op T)}
    (hz : z ∈ Submodule.span ((structureSheaf B S hS).obj.obj (op T))
      (Set.range fun a : Γ(F, U) => pullbackUnitSection B S hS F j a)) :
    (pullbackPresheaf B S hS F).map g.op z ∈
      Submodule.span ((structureSheaf B S hS).obj.obj (op T'))
        (Set.range fun a : Γ(F, U) => pullbackUnitSection B S hS F j' a) := by
  refine Submodule.span_induction
    (p := fun y _ => (pullbackPresheaf B S hS F).map g.op y ∈
      Submodule.span ((structureSheaf B S hS).obj.obj (op T'))
        (Set.range fun a : Γ(F, U) => pullbackUnitSection B S hS F j' a)) ?_ ?_ ?_ ?_ hz
  · rintro y ⟨a, rfl⟩
    exact Submodule.subset_span ⟨a, (pullbackUnitSection_map B S hS F g j j' a).symm⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro p q _ _ hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  · intro c p _ hp
    rw [PresheafOfModules.map_smul]
    exact Submodule.smul_mem _ _ hp

/-- **Every section of the pullback is a combination of generators over one open of `S`.**
Every section of `AlgebraicGeometry.BigFppfOver.pullbackPresheaf` over `T` lies in the span of
the generators indexed by a single open `W` of `S` through which `T` factors. -/
public theorem exists_mem_span_pullbackUnitSection (F : S.Modules) [F.IsQuasicoherent]
    (T : BigFppfOver B S hS) (x : (pullbackPresheaf B S hS F).obj (op T)) :
    ∃ (W : S.Opens) (g : T ⟶ (opensToBig B S hS).obj W),
      x ∈ Submodule.span ((structureSheaf B S hS).obj.obj (op T))
        (Set.range fun a : Γ(F, W) => pullbackUnitSection B S hS F g a) := by
  have htop := PresheafOfModules.span_pullbackUnitGenerators_eq_top
    (structureMap B S hS).hom ((SheafOfModules.forget S.ringCatSheaf).obj F) (op T)
  refine Submodule.span_induction
    (p := fun y _ => ∃ (W : S.Opens) (g : T ⟶ (opensToBig B S hS).obj W),
      y ∈ Submodule.span ((structureSheaf B S hS).obj.obj (op T))
        (Set.range fun a : Γ(F, W) => pullbackUnitSection B S hS F g a))
    ?_ ?_ ?_ ?_ (htop.ge Submodule.mem_top)
  · rintro y ⟨W, g, a, rfl⟩
    exact ⟨W, g, Submodule.subset_span ⟨a, rfl⟩⟩
  · exact ⟨⊤, homOfRangeLe B S hS ⊤ (by simp), Submodule.zero_mem _⟩
  · rintro y z _ _ ⟨W₁, g₁, hy⟩ ⟨W₂, g₂, hz⟩
    have hr : Set.range ⇑T.hom.hom ⊆ ((W₁ ⊓ W₂ : S.Opens) : Set S) :=
      Set.subset_inter (range_le_of_hom B S hS g₁) (range_le_of_hom B S hS g₂)
    exact ⟨W₁ ⊓ W₂, homOfRangeLe B S hS (W₁ ⊓ W₂) hr, Submodule.add_mem _
      (span_pullbackUnitSection_mono B S hS F inf_le_left g₁ _ hy)
      (span_pullbackUnitSection_mono B S hS F inf_le_right g₂ _ hz)⟩
  · rintro c y _ ⟨W, g, hy⟩
    exact ⟨W, g, Submodule.smul_mem _ c hy⟩

/-- **The covering of an object by its affine opens lying over affine opens inside a given open of
`S`.**  The refinement of `AlgebraicGeometry.BigFppfOver.affineSubordinateCover` subordinate to an
open `W` of `S`: its index type is the pairs of an affine open `V` of the underlying scheme of `T`
and an affine open `U ≤ W` of `S` with `V ≤ T.hom⁻¹U`, and its members are the open immersions of
those `V`. -/
public noncomputable def affineSubordinateCoverOver (T : BigFppfOver B S hS) (W : S.Opens) :
    PreZeroHypercover.{u + 1} T where
  I₀ := ULift.{u + 1} (Σ V : T.left.obj.affineOpens,
    {U : S.affineOpens // U.1 ≤ W ∧ V.1 ≤ T.hom.hom ⁻¹ᵁ U.1})
  X i := openSubObj B S hS T i.down.1.1
  f i := openSubHom B S hS T i.down.1.1

/-- The refinement subordinate to `W` is an fppf covering family of the chosen category of
schemes, provided the structure morphism of `T` has range inside `W`. -/
public theorem isFppfCovering_affineSubordinateCoverOver (T : BigFppfOver B S hS) (W : S.Opens)
    (hW : Set.range ⇑T.hom.hom ⊆ (W : Set S)) :
    IsFppfCovering (κ := B.cutoff)
      ⟨T.left, (affineSubordinateCoverOver B S hS T W).map (Over.forget (B.obj hS))⟩ := by
  refine isFppfCovering_of_forall_exists B S hS T _ (fun x => ?_)
    (fun i => inferInstanceAs (IsOpenImmersion (i.down.1.1.ι)))
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := T.hom.hom.base x) (U := W) (hW ⟨x, rfl⟩)
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (X := T.left.obj) (x := x) (U := T.hom.hom ⁻¹ᵁ U) hxU
  exact ⟨⟨⟨⟨V, hV⟩, ⟨U, hU⟩, hUW, hVU⟩⟩, ⟨⟨x, hxV⟩, rfl⟩⟩

/-- **The affine opens lying over affine opens inside `W` cover, for each of the five
topologies.**  If the structure morphism of `T` has range inside `W`, the sieve generated by
`AlgebraicGeometry.BigFppfOver.affineSubordinateCoverOver` is a covering sieve for the
localization at `S` of each of the five big topologies. -/
public theorem mem_baseTopology_sieve₀_affineSubordinateCoverOver (τ : SiteKind)
    (T : BigFppfOver B S hS) (W : S.Opens) (hW : Set.range ⇑T.hom.hom ⊆ (W : Set S)) :
    (affineSubordinateCoverOver B S hS T W).sieve₀ ∈ baseOverTopology B S hS τ T :=
  sieve₀_mem_baseOverTopology_of_isFppfCovering B S hS τ T _
    (isFppfCovering_affineSubordinateCoverOver B S hS T W hW)
    (fun i => inferInstanceAs (IsOpenImmersion (i.down.1.1.ι)))

/-- **The affine opens lying over affine opens inside `W` cover.**  The fppf case of
`AlgebraicGeometry.BigFppfOver.mem_baseTopology_sieve₀_affineSubordinateCoverOver`. -/
public theorem mem_topology_sieve₀_affineSubordinateCoverOver (T : BigFppfOver B S hS)
    (W : S.Opens) (hW : Set.range ⇑T.hom.hom ⊆ (W : Set S)) :
    (affineSubordinateCoverOver B S hS T W).sieve₀ ∈ topology B S hS T :=
  mem_baseTopology_sieve₀_affineSubordinateCoverOver B S hS .fppf T W hW

/-- **The comparison of Stacks 070S (1) is locally injective, for every one of the five
topologies.**  Two sections of the pullback with the same image under
`AlgebraicGeometry.BigFppfOver.sectionsComparison` agree locally for the localized
`τ`-topology.

This is the other half of Stacks 070S (1); the locally surjective half is
`AlgebraicGeometry.BigFppfOver.isLocallySurjective_sectionsComparison_baseOverTopology`. -/
public instance isLocallyInjective_sectionsComparison_baseOverTopology (τ : SiteKind)
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsLocallyInjective (baseOverTopology B S hS τ)
      ((PresheafOfModules.toPresheaf (FibredSite.baseRingStructureSheaf B S hS τ).obj).map
        (sectionsComparison B S hS F)) where
  equalizerSieve_mem {Zop} x y h := by
    have h' : (sectionsComparison B S hS F).app Zop
          (x : (pullbackPresheaf B S hS F).obj Zop) =
        (sectionsComparison B S hS F).app Zop
          (y : (pullbackPresheaf B S hS F).obj Zop) := h
    have hxy : (sectionsComparison B S hS F).app Zop
        ((x : (pullbackPresheaf B S hS F).obj Zop) - y) = 0 :=
      (map_sub ((sectionsComparison B S hS F).app Zop).hom
        (x : (pullbackPresheaf B S hS F).obj Zop) y).trans (sub_eq_zero_of_eq h')
    obtain ⟨W, g, hp⟩ := exists_mem_span_pullbackUnitSection B S hS F Zop.unop
      ((x : (pullbackPresheaf B S hS F).obj Zop) - y)
    refine (baseOverTopology B S hS τ).superset_covering ?_
      (mem_baseTopology_sieve₀_affineSubordinateCoverOver B S hS τ Zop.unop W
        (range_le_of_hom B S hS g))
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    obtain ⟨⟨⟨V, hV⟩, ⟨U, hU⟩, hUW, hVU⟩⟩ := i
    have hVaff : IsAffine V.toScheme := hV
    have hr : Set.range ⇑(openSubObj B S hS (unop Zop) V).hom.hom ⊆ (U : Set S) := by
      rintro z ⟨w, rfl⟩
      exact hVU w.2
    have hzero : (pullbackPresheaf B S hS F).map
        (openSubHom B S hS (unop Zop) V).op
          ((x : (pullbackPresheaf B S hS F).obj Zop) - y) = 0 := by
      refine eq_zero_of_mem_span_pullbackUnitSection B S hS F hU
        (isAffineOpen_top V.toScheme) (homOfRangeLe B S hS U hr) ?_ ?_
      · refine span_pullbackUnitSection_mono B S hS F hUW
          (openSubHom B S hS (unop Zop) V ≫ g) _ ?_
        exact map_mem_span_pullbackUnitSection B S hS F
          (openSubHom B S hS (unop Zop) V) g _ hp
      · refine Eq.trans (PresheafOfModules.naturality_apply (sectionsComparison B S hS F)
          (openSubHom B S hS (unop Zop) V).op _) ?_
        exact (congrArg (fun z => (sectionsPresheafOfModules B S hS F).map
          (openSubHom B S hS (unop Zop) V).op z) hxy).trans (map_zero _)
    exact sub_eq_zero.1 ((map_sub ((pullbackPresheaf B S hS F).map
      (openSubHom B S hS (unop Zop) V).op).hom
      (x : (pullbackPresheaf B S hS F).obj Zop) y).symm.trans hzero)

/-- **The comparison of Stacks 070S (1) is locally injective.**  The fppf case of
`AlgebraicGeometry.BigFppfOver.isLocallyInjective_sectionsComparison_baseOverTopology`. -/
public instance isLocallyInjective_sectionsComparison (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsLocallyInjective (topology B S hS)
      ((PresheafOfModules.toPresheaf (structureSheaf B S hS).obj).map
        (sectionsComparison B S hS F)) :=
  isLocallyInjective_sectionsComparison_baseOverTopology B S hS .fppf F

/-- The associated-module functor of the indicated big site of `S` is the `τ`-sheafification of
the pullback of presheaves of modules along the structure-sheaf comparison.  Both functors are
left adjoint to restriction along the inclusion of the small Zariski site.

This is `CategoryTheory.SheafOfModules.pullbackIso` read at
`AlgebraicGeometry.BigFppfOver.baseStructureMap`; the fppf case is
`AlgebraicGeometry.BigFppfOver.associatedModuleSheafificationIso`. -/
public noncomputable def baseAssociatedModuleSheafificationIso (τ : SiteKind) :
    baseAssociatedModule B S hS τ ≅
      SheafOfModules.forget S.ringCatSheaf ⋙
        PresheafOfModules.pullback.{u} (baseStructureMap B S hS τ).hom ⋙
          PresheafOfModules.sheafification
            (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj) :=
  SheafOfModules.pullbackIso.{u} (baseStructureMap B S hS τ)

/-- For each of the five topologies `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, the
associated module of a quasi-coherent module `F` on `S` — the pullback along the morphism of
ringed sites `id_{τ,Zar} : ((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)` — is the `τ`-sheafification of the
pullback-sections presheaf `(f : T → S) ↦ Γ(T, f⁺F)` of Stacks 03DS.

This is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleSheafificationIso` at `F`, which
presents the associated module as the `τ`-sheafification of the presheaf-level pullback, followed
by the `τ`-sheafification of `AlgebraicGeometry.BigFppfOver.sectionsComparison`. -/
@[stacks 070S "part (1)", stacks 03FH "part (1)"]
public noncomputable def baseAssociatedModuleIsoSections (τ : SiteKind) (F : S.Modules)
    [F.IsQuasicoherent] :
    (baseAssociatedModule B S hS τ).obj F ≅
      (PresheafOfModules.sheafification.{u}
          (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).obj
        (sectionsPresheafOfModules B S hS F) :=
  (baseAssociatedModuleSheafificationIso B S hS τ).app F ≪≫
    @asIso _ _ _ _ _ (isIso_baseSheafification_map_sectionsComparison B S hS τ F)

/-- **Stacks 070S (1) at the big fppf site.**  The associated module of a quasi-coherent module
`F` on `S` is the fppf sheafification of the pullback-sections presheaf
`(f : T → S) ↦ Γ(T, f⁺F)` of Stacks 03DS. -/
public noncomputable def associatedModuleIsoSections (F : S.Modules) [F.IsQuasicoherent] :
    (associatedModule B S hS).obj F ≅
      (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).obj
        (sectionsPresheafOfModules B S hS F) :=
  associatedModuleIsoSectionsSheafification B S hS F


end BigFppfOver

end AlgebraicGeometry

end

