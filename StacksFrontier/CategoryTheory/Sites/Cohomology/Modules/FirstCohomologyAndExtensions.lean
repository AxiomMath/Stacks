module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Whiskering
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.Injectives.Sheaf.ModulesOnRingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# First cohomology of a ringed site classifies extensions of the structure sheaf

Let `(C, O)` be a ringed site on a small site and `M` a sheaf of `O`-modules. An extension
`0 → M → E → O → 0` of the structure sheaf by `M` has a class in `H^1(C, M)`, namely the
image of the unit global section `1 ∈ Γ(C, O)` under the connecting map of the extension.
This file proves that this assignment is an isomorphism of abelian groups
`Ext^1_{Mod(O)}(O, M) ≅ H^1(C, M)`.

The proof is the universality argument rather than the pullback construction of the source.
Both sides are the degree-one part of a cohomological `δ`-functor on `Mod(O)`:
`extDeltaFunctorForUnit` is `n ↦ Ext^n(O, -)` with the Yoneda connecting maps, and
`cohomologyDeltaFunctorAddCommGrp` is the cohomology `δ`-functor of Stacks 071H pushed into
abelian groups. Both are universal, because both vanish in positive degrees on injective
objects, so Stacks 010T identifies them uniquely from their degree-zero parts; and in degree
zero both are global sections, since `Ext^0(O, M) = Hom(O, M) = Γ(C, M)`. Comparing the
degree-one parts of the two `δ`-functors gives the isomorphism, and the compatibility of the
comparison with the connecting maps is exactly the formula "the class of an extension is the
connecting image of `1`", which in turn pins the isomorphism down uniquely.

## Main definitions

* `Stacks.Cohomology.SiteModules.universalCohomologyDeltaFunctor`: a fixed universal cohomological
  `δ`-functor whose functors are the cohomology functors of Stacks 071H.
* `Stacks.Cohomology.SiteModules.cohomologyZeroMap`: the canonical comparison from global
  sections to degree-zero cohomology, transported to that fixed presentation.
* `Stacks.Cohomology.SiteModules.extDeltaFunctorForUnit`: the `δ`-functor
  `n ↦ Ext^n(O, -)`.

## Main results

* `Stacks.Cohomology.SiteModules.extOneEquivFirstCohomology`: the canonical additive
  equivalence `Ext^1(O, M) ≃+ H^1(C, M)`.
* `Stacks.Cohomology.SiteModules.extOneEquivFirstCohomology_extClass`: it sends the class of
  an extension to the connecting image of the unit global section.
* `Stacks.Cohomology.SiteModules.extOneEquivFirstCohomology_unique`: that formula determines
  it uniquely.
* `Stacks.Cohomology.SiteModules.extOneEquivFirstCohomology_naturality`: it is natural in the
  coefficient module.

## Implementation notes

`Ext` groups of a category of sheaves of modules in universe `u` live in universe `u + 1`,
while cohomology is valued in `u`-modules over `Γ(C, O)`; the comparison therefore runs
through `moduleToLiftedAddCommGrp`, the forgetful functor to abelian groups followed by
`ULift`. That functor is additive and preserves and reflects finite limits and colimits, so it
transports both the `δ`-functor structure and its universality.

The source states the bijection without naming a `δ`-functor presentation of cohomology, which
is only unique up to isomorphism; `universalCohomologyDeltaFunctor` fixes one by choice, and
`universalCohomologyDeltaFunctor_functor` records that its underlying functors are the cohomology
functors on the nose. The degree-zero normalisation used is the canonical map
`Functor.toRightDerivedZero`, not an arbitrary isomorphism, which is what makes
`extOneEquivFirstCohomology_unique` a genuine uniqueness statement.

## References

* [Stacks Project, Tag 03F1](https://stacks.math.columbia.edu/tag/03F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u

namespace Stacks.Cohomology.SiteModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- A fixed universal cohomological `δ`-functor structure on the cohomology functors of
sheaves of modules on a small site.

This is the universal `δ`-functor obtained by choice from
`Stacks.Cohomology.SiteModules.exists_universal_cohomologyDeltaFunctor`;
`Stacks.Cohomology.SiteModules.cohomologyDeltaFunctor` is the unrelated right-derived
`δ`-functor of the global-sections functor on a ringed site. -/
def universalCohomologyDeltaFunctor (R : Sheaf J RingCat.{u}) :
    DeltaFunctor (SheafOfModules.{u} R)
      (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) :=
  Classical.choose (exists_universal_cohomologyDeltaFunctor R)

/-- The functors underlying the fixed `δ`-functor are the cohomology functors themselves. -/
theorem universalCohomologyDeltaFunctor_functor (R : Sheaf J RingCat.{u}) (n : ℕ) :
    (universalCohomologyDeltaFunctor R).functor n = cohomologyFunctor R n :=
  (Classical.choose_spec (exists_universal_cohomologyDeltaFunctor R)).1 n

/-- The canonical map from global sections to degree-zero cohomology, transported to the fixed
`δ`-functor presentation. -/
def cohomologyZeroMap (R : Sheaf J RingCat.{u}) :
    globalSectionsFunctor R ⟶ (universalCohomologyDeltaFunctor R).functor 0 :=
  (globalSectionsFunctor R).toRightDerivedZero ≫
    eqToHom (universalCohomologyDeltaFunctor_functor R 0).symm

/-- The cohomological `δ`-functor `n ↦ Ext^n(O, -)` on sheaves of modules, with the Yoneda
connecting maps. -/
def extDeltaFunctorForUnit (R : Sheaf J RingCat.{u}) :
    DeltaFunctor (SheafOfModules.{u} R) AddCommGrpCat.{u + 1} where
  functor n := extFunctorObj (SheafOfModules.unit R) n
  δ hS n := AddCommGrpCat.ofHom
    ((hS.map_of_exact (𝟭 (SheafOfModules.{u} R))).extClass.postcomp
      (SheafOfModules.unit R) (rfl : n + 1 = n + 1))
  map_g_δ {S} hS n := by
    ext e
    change Ext (SheafOfModules.unit R) _ n at e
    change (e.comp (Ext.mk₀ (S.map (𝟭 (SheafOfModules.{u} R))).g) (add_zero n)).comp
      (hS.map_of_exact (𝟭 (SheafOfModules.{u} R))).extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero,
      (hS.map_of_exact (𝟭 (SheafOfModules.{u} R))).comp_extClass, Ext.comp_zero]
  δ_map_f {S} hS n := by
    ext e
    change Ext (SheafOfModules.unit R) _ n at e
    change (e.comp (hS.map_of_exact (𝟭 (SheafOfModules.{u} R))).extClass rfl).comp
      (Ext.mk₀ (S.map (𝟭 (SheafOfModules.{u} R))).f) (add_zero _) = 0
    rw [Ext.comp_assoc_of_third_deg_zero,
      (hS.map_of_exact (𝟭 (SheafOfModules.{u} R))).extClass_comp, Ext.comp_zero]
  mono_map_f hS := by
    have := hS.mono_f
    exact Ext.mono_postcomp_mk₀_of_mono (SheafOfModules.unit R)
      ((𝟭 (SheafOfModules.{u} R)).map _)
  exact_map hS n := by
    have := hS.mono_f
    have := hS.epi_g
    exact Ext.covariant_sequence_exact₂' (SheafOfModules.unit R)
      (hS.map_of_exact (𝟭 (SheafOfModules.{u} R))) n
  exact_δ₁ hS n := by
    have := hS.mono_f
    have := hS.epi_g
    exact Ext.covariant_sequence_exact₃' (SheafOfModules.unit R)
      (hS.map_of_exact (𝟭 (SheafOfModules.{u} R))) n (n + 1) rfl
  exact_δ₂ hS n := by
    have := hS.mono_f
    have := hS.epi_g
    exact Ext.covariant_sequence_exact₁' (SheafOfModules.unit R)
      (hS.map_of_exact (𝟭 (SheafOfModules.{u} R))) n (n + 1) rfl
  δ_naturality hS hT φ n := by
    have := hS.mono_f
    have := hS.epi_g
    have := hT.mono_f
    have := hT.epi_g
    ext e
    change Ext (SheafOfModules.unit R) _ n at e
    change (e.comp (Ext.mk₀ ((𝟭 (SheafOfModules.{u} R)).map φ.τ₃)) (add_zero n)).comp
      (hT.map_of_exact (𝟭 (SheafOfModules.{u} R))).extClass rfl =
      (e.comp (hS.map_of_exact (𝟭 (SheafOfModules.{u} R))).extClass rfl).comp
        (Ext.mk₀ ((𝟭 (SheafOfModules.{u} R)).map φ.τ₁)) (add_zero _)
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]
    exact congrArg (fun a => e.comp a rfl)
      ((hS.map_of_exact (𝟭 (SheafOfModules.{u} R))).extClass_naturality
        (hT.map_of_exact (𝟭 (SheafOfModules.{u} R)))
        ((𝟭 (SheafOfModules.{u} R)).mapShortComplex.map φ)).symm

/-- The functor sending a module over the ring of global sections of `R` to its underlying
abelian group, lifted one universe up. -/
def moduleToLiftedAddCommGrp (R : Sheaf J RingCat.{u}) :
    ModuleCat.{u} (RingCat.sectionsSubring R.obj) ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The functor `moduleToLiftedAddCommGrp R` is additive. -/
instance moduleToLiftedAddCommGrp_additive (R : Sheaf J RingCat.{u}) :
    (moduleToLiftedAddCommGrp R).Additive := by
  constructor
  intro Y Z f g
  apply AddCommGrpCat.hom_ext
  ext x
  rfl

/-- The functor `moduleToLiftedAddCommGrp R` preserves finite limits. -/
instance moduleToLiftedAddCommGrp_preservesFiniteLimits (R : Sheaf J RingCat.{u}) :
    PreservesFiniteLimits (moduleToLiftedAddCommGrp R) :=
  Limits.comp_preservesFiniteLimits
    (forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u})
    (AddCommGrpCat.uliftFunctor.{u + 1, u})

/-- The functor `moduleToLiftedAddCommGrp R` preserves finite colimits. -/
instance moduleToLiftedAddCommGrp_preservesFiniteColimits (R : Sheaf J RingCat.{u}) :
    PreservesFiniteColimits (moduleToLiftedAddCommGrp R) := by
  let F := forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u}
  let G := AddCommGrpCat.uliftFunctor.{u + 1, u}
  have : PreservesFiniteColimits F := PreservesColimits.preservesFiniteColimits F
  exact Limits.comp_preservesFiniteColimits F G

/-- The cohomology `δ`-functor of Stacks 071H, pushed forward into abelian groups one universe
up so that it can be compared with `Ext`. -/
def cohomologyDeltaFunctorAddCommGrp (R : Sheaf J RingCat.{u}) :
    DeltaFunctor (SheafOfModules.{u} R) AddCommGrpCat.{u + 1} where
  functor n := (universalCohomologyDeltaFunctor R).functor n ⋙ moduleToLiftedAddCommGrp R
  additive n := by
    have := (universalCohomologyDeltaFunctor R).additive n
    infer_instance
  δ {S} hS n := (moduleToLiftedAddCommGrp R).map ((universalCohomologyDeltaFunctor R).δ hS n)
  map_g_δ {S} hS n := by
    change (moduleToLiftedAddCommGrp R).map
      (((universalCohomologyDeltaFunctor R).functor n).map S.g ≫
        (universalCohomologyDeltaFunctor R).δ hS n) = 0
    rw [(universalCohomologyDeltaFunctor R).map_g_δ hS n, Functor.map_zero]
  δ_map_f {S} hS n := by
    change (moduleToLiftedAddCommGrp R).map
      ((universalCohomologyDeltaFunctor R).δ hS n ≫
        ((universalCohomologyDeltaFunctor R).functor (n + 1)).map S.f) = 0
    rw [(universalCohomologyDeltaFunctor R).δ_map_f hS n, Functor.map_zero]
  mono_map_f {S} hS := by
    change Mono ((moduleToLiftedAddCommGrp R).map
      (((universalCohomologyDeltaFunctor R).functor 0).map S.f))
    have : Mono (((universalCohomologyDeltaFunctor R).functor 0).map S.f) :=
      (universalCohomologyDeltaFunctor R).mono_map_f hS
    exact Functor.map_mono (moduleToLiftedAddCommGrp R) _
  exact_map {S} hS n := by
    change ((S.map ((universalCohomologyDeltaFunctor R).functor n)).map
      (moduleToLiftedAddCommGrp R)).Exact
    exact ((universalCohomologyDeltaFunctor R).exact_map hS n).map _
  exact_δ₁ {S} hS n := by
    convert ((universalCohomologyDeltaFunctor R).exact_δ₁ hS n).map
      (moduleToLiftedAddCommGrp R) using 1
    rfl
  exact_δ₂ {S} hS n := by
    convert ((universalCohomologyDeltaFunctor R).exact_δ₂ hS n).map
      (moduleToLiftedAddCommGrp R) using 1
    rfl
  δ_naturality {S} {T} hS hT φ n := by
    simpa only [Functor.comp_map, Functor.map_comp] using congrArg (fun f =>
      (moduleToLiftedAddCommGrp R).map f)
        ((universalCohomologyDeltaFunctor R).δ_naturality hS hT φ n)

/-- `Ext^n(O, -)` vanishes on injectives for `n > 0`, so it is a universal `δ`-functor. -/
theorem extDeltaFunctorForUnit_isUniversal (R : Sheaf J RingCat.{u}) :
    (extDeltaFunctorForUnit R).IsUniversal := by
  apply DeltaFunctor.isUniversal_of_isZero_injective
  intro n I hI
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr
    (subsingleton_of_forall_eq 0 (fun e => Ext.eq_zero_of_injective e))

/-- Higher cohomology vanishes on injectives, so the cohomology `δ`-functor is universal. -/
theorem cohomologyDeltaFunctorAddCommGrp_isUniversal (R : Sheaf J RingCat.{u}) :
    (cohomologyDeltaFunctorAddCommGrp R).IsUniversal := by
  apply DeltaFunctor.isUniversal_of_isZero_injective
  intro n I hI
  change IsZero ((moduleToLiftedAddCommGrp R).obj
    (((universalCohomologyDeltaFunctor R).functor (n + 1)).obj I))
  rw [universalCohomologyDeltaFunctor_functor R (n + 1)]
  change IsZero ((moduleToLiftedAddCommGrp R).obj
    (((globalSectionsFunctor R).rightDerived (n + 1)).obj I))
  exact Functor.map_isZero (moduleToLiftedAddCommGrp R)
    (Functor.isZero_rightDerived_obj_injective_succ (globalSectionsFunctor R) n I)

/-- `Ext^0(O, -)` is `Hom(O, -)`. -/
def extZeroIsoCoyoneda (R : Sheaf J RingCat.{u}) :
    extFunctorObj (SheafOfModules.unit R) 0 ≅
      preadditiveCoyoneda.obj (op (SheafOfModules.unit R)) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents (fun M =>
    (Ext.addEquiv₀.trans AddEquiv.ulift.symm).toAddCommGrpIso) (by
    intro M N f
    ext e
    change ULift.up (Ext.addEquiv₀ (e.comp (Ext.mk₀ f) (add_zero 0))) =
      ULift.up (Ext.addEquiv₀ e ≫ f)
    apply congrArg ULift.up
    change Ext.homEquiv₀ (e.comp (Ext.mk₀ f) (add_zero 0)) = Ext.homEquiv₀ e ≫ f
    apply (Ext.mk₀_bijective _ _).injective
    rw [Ext.mk₀_homEquiv₀_apply, ← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply e])

/-- Maps out of the structure sheaf are its global sections, as an additive equivalence. -/
def unitHomAddEquiv (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ M) ≃+ M.sections := by
  let f : (SheafOfModules.unit R ⟶ M) →+ M.sections :=
    { toFun := M.unitHomEquiv
      map_zero' := by
        apply Subtype.ext
        funext Y
        rw [SheafOfModules.unitHomEquiv_apply_coe]
        rfl
      map_add' := by
        intro g h
        apply Subtype.ext
        funext Y
        rw [SheafOfModules.unitHomEquiv_apply_coe]
        rfl }
  exact AddEquiv.ofBijective f M.unitHomEquiv.bijective

/-- `Hom(O, -)` is global sections, naturally. -/
def unitCoyonedaSectionsIso (R : Sheaf J RingCat.{u}) :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit R)) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      globalSectionsFunctor.{u, u, u, u} R ⋙ moduleToLiftedAddCommGrp R :=
  NatIso.ofComponents (fun M =>
    ((AddEquiv.ulift.{u, u + 1}.trans (unitHomAddEquiv R M)).trans
      (AddEquiv.ulift.{u, u + 1}).symm).toAddCommGrpIso) (by
      intro M N f
      ext g
      let g' : SheafOfModules.unit R ⟶ M := AddEquiv.ulift.{u, u + 1} g
      change ULift.up.{u + 1, u} (N.unitHomEquiv (g' ≫ f)) =
        ULift.up.{u + 1, u} (SheafOfModules.sectionsMap f (M.unitHomEquiv g'))
      simpa using congrArg (ULift.up.{u + 1, u})
        (SheafOfModules.unitHomEquiv_comp_apply g' f))

/-- Global sections of sheaves of modules preserve finite limits: they are corepresented by
the structure sheaf, and the comparison functor to abelian groups reflects finite limits. -/
theorem globalSectionsFunctor_preservesFiniteLimits (R : Sheaf J RingCat.{u}) :
    PreservesFiniteLimits (globalSectionsFunctor.{u, u, u, u} R) := by
  let F := globalSectionsFunctor.{u, u, u, u} R
  let G := moduleToLiftedAddCommGrp R
  have : PreservesFiniteLimits
      (preadditiveCoyoneda.obj (op (SheafOfModules.unit R)) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}) := inferInstance
  have : PreservesFiniteLimits (F ⋙ G) :=
    preservesFiniteLimits_of_natIso (unitCoyonedaSectionsIso R)
  have : ReflectsFiniteLimits G := by
    dsimp [G, moduleToLiftedAddCommGrp]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves F G

/-- In degree zero the cohomology `δ`-functor is global sections. -/
def cohomologyZeroIsoAddCommGrp (R : Sheaf J RingCat.{u}) :
    globalSectionsFunctor.{u, u, u, u} R ⋙ moduleToLiftedAddCommGrp R ≅
      (cohomologyDeltaFunctorAddCommGrp R).functor 0 := by
  have : IsIso (cohomologyZeroMap R) := by
    have := globalSectionsFunctor_preservesFiniteLimits R
    dsimp [cohomologyZeroMap]
    infer_instance
  exact Functor.isoWhiskerRight (asIso (cohomologyZeroMap R)) (moduleToLiftedAddCommGrp R)

/-- The two `δ`-functors agree in degree zero: both are global sections. -/
def extCohomologyDeltaZeroIso (R : Sheaf J RingCat.{u}) :
    (extDeltaFunctorForUnit R).functor 0 ≅ (cohomologyDeltaFunctorAddCommGrp R).functor 0 := by
  simpa only [extDeltaFunctorForUnit] using
    (extZeroIsoCoyoneda R ≪≫ unitCoyonedaSectionsIso R ≪≫ cohomologyZeroIsoAddCommGrp R)

/-- Two universal `δ`-functors agreeing in degree zero agree, so `Ext^n(O, -)` is
cohomology. -/
def extCohomologyDeltaIso (R : Sheaf J RingCat.{u}) :
    extDeltaFunctorForUnit R ≅ cohomologyDeltaFunctorAddCommGrp R := by
  have := extDeltaFunctorForUnit_isUniversal R
  have := cohomologyDeltaFunctorAddCommGrp_isUniversal R
  exact DeltaFunctor.IsUniversal.isoOfIso (extCohomologyDeltaZeroIso R)

/-- Evaluating a `δ`-functor in degree one at a fixed object. -/
def deltaFunctorEvalOne (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) :
    DeltaFunctor (SheafOfModules.{u} R) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} where
  obj F := (F.functor 1).obj M
  map η := (η.app 1).app M
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Stacks 03F1.** For a ringed site `(C, O)` and a sheaf of `O`-modules `M`, first
extensions of the structure sheaf by `M` are canonically first cohomology. -/
@[stacks 03F1 "canonical bijection"]
def extOneEquivFirstCohomology (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) :
    Ext (SheafOfModules.unit R) M 1 ≃+ (cohomologyFunctor R 1).obj M := by
  let h₁ := (deltaFunctorEvalOne R M).mapIso (extCohomologyDeltaIso R)
  let e₁ : Ext (SheafOfModules.unit R) M 1 ≃+
      ((universalCohomologyDeltaFunctor R).functor 1).obj M :=
    (Iso.addCommGroupIsoToAddEquiv h₁).trans (AddEquiv.ulift.{u, u + 1})
  let hcast : ((universalCohomologyDeltaFunctor R).functor 1).obj M ≅
      (cohomologyFunctor R 1).obj M :=
    (eqToIso (universalCohomologyDeltaFunctor_functor R 1)).app M
  let F := forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u}
  exact e₁.trans <| Iso.addCommGroupIsoToAddEquiv (F.mapIso hcast)

/-- The equivalence is the degree-one component of the comparison of `δ`-functors, followed by
the identification of the two presentations of cohomology. -/
private theorem extOneEquivFirstCohomology_apply (R : Sheaf J RingCat.{u})
    (M : SheafOfModules.{u} R) (ξ : Ext (SheafOfModules.unit R) M 1) :
    extOneEquivFirstCohomology R M ξ =
      (eqToHom (universalCohomologyDeltaFunctor_functor R 1)).app M
        (AddEquiv.ulift.{u, u + 1} (((extCohomologyDeltaIso R).hom.app 1).app M ξ)) :=
  rfl

/-- **Stacks 03F1.** The class of the extension `0 → M → E → O → 0` goes to the image of the
unit global section under the connecting morphism of the extension. -/
@[stacks 03F1 "image of an extension"]
theorem extOneEquivFirstCohomology_extClass (R : Sheaf J RingCat.{u})
    (M : SheafOfModules.{u} R) (E : SheafOfModules.{u} R) (f : M ⟶ E)
    (g : E ⟶ SheafOfModules.unit R) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) :
    extOneEquivFirstCohomology R M hS.extClass =
      (eqToHom (universalCohomologyDeltaFunctor_functor R 1)).app M
        ((universalCohomologyDeltaFunctor R).δ hS 0
        ((cohomologyZeroMap R).app (SheafOfModules.unit R)
            (SheafOfModules.unitHomEquiv (SheafOfModules.unit R) (𝟙 _)))) := by
  let d := extCohomologyDeltaIso R
  have hzero : ((d.hom.app 0).app (SheafOfModules.unit R))
      (Ext.mk₀ (𝟙 (SheafOfModules.unit R))) =
      ULift.up ((cohomologyZeroMap R).app (SheafOfModules.unit R)
        (SheafOfModules.unitHomEquiv (SheafOfModules.unit R) (𝟙 _))) := by
    have := extDeltaFunctorForUnit_isUniversal R
    have := cohomologyDeltaFunctorAddCommGrp_isUniversal R
    have hd0 : d.hom.app 0 = (extCohomologyDeltaZeroIso R).hom := by
      dsimp [d, extCohomologyDeltaIso]
      exact DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero _
    rw [hd0]
    have hExt : Ext.addEquiv₀ (Ext.mk₀ (𝟙 (SheafOfModules.unit R))) =
        𝟙 (SheafOfModules.unit R) := by
      apply (Ext.mk₀_bijective _ _).injective
      simp
    have h1 : ((extZeroIsoCoyoneda R).hom.app (SheafOfModules.unit R))
        (Ext.mk₀ (𝟙 (SheafOfModules.unit R))) =
        ULift.up (𝟙 (SheafOfModules.unit R)) := by
      dsimp [extZeroIsoCoyoneda]
      change ULift.up (Ext.addEquiv₀ (Ext.mk₀ (𝟙 (SheafOfModules.unit R)))) = _
      rw [hExt]
    have h2 : ((unitCoyonedaSectionsIso R).hom.app (SheafOfModules.unit R))
        (((extZeroIsoCoyoneda R).hom.app (SheafOfModules.unit R))
          (Ext.mk₀ (𝟙 (SheafOfModules.unit R)))) =
        ULift.up ((SheafOfModules.unit R).unitHomEquiv (𝟙 _)) := by
      rw [h1]
      dsimp [unitCoyonedaSectionsIso]
      change ULift.up ((SheafOfModules.unit R).unitHomEquiv (𝟙 _)) = _
      rfl
    have h3 : ((cohomologyZeroIsoAddCommGrp R).hom.app (SheafOfModules.unit R))
        (((unitCoyonedaSectionsIso R).hom.app (SheafOfModules.unit R))
          (((extZeroIsoCoyoneda R).hom.app (SheafOfModules.unit R))
            (Ext.mk₀ (𝟙 (SheafOfModules.unit R))))) =
        ULift.up ((cohomologyZeroMap R).app (SheafOfModules.unit R)
          ((SheafOfModules.unit R).unitHomEquiv (𝟙 _))) := by
      rw [h2]
      change ULift.up ((cohomologyZeroMap R).app (SheafOfModules.unit R)
        ((SheafOfModules.unit R).unitHomEquiv (𝟙 _))) = _
      rfl
    dsimp [extCohomologyDeltaZeroIso]
    change ((cohomologyZeroIsoAddCommGrp R).hom.app (SheafOfModules.unit R))
        (((unitCoyonedaSectionsIso R).hom.app (SheafOfModules.unit R))
          (((extZeroIsoCoyoneda R).hom.app (SheafOfModules.unit R))
            (Ext.mk₀ (𝟙 (SheafOfModules.unit R))))) = _
    exact h3
  have hδ := d.hom.comm hS 0
  have h := congrArg (fun φ => φ (Ext.mk₀ (𝟙 (SheafOfModules.unit R)))) hδ
  change ((cohomologyDeltaFunctorAddCommGrp R).δ hS 0)
      (((d.hom.app 0).app (SheafOfModules.unit R))
        (Ext.mk₀ (𝟙 (SheafOfModules.unit R)))) =
    ((d.hom.app 1).app M)
      ((extDeltaFunctorForUnit R).δ hS 0 (Ext.mk₀ (𝟙 (SheafOfModules.unit R)))) at h
  rw [hzero] at h
  have hclass : (extDeltaFunctorForUnit R).δ hS 0
      (Ext.mk₀ (𝟙 (SheafOfModules.unit R))) = hS.extClass := by
    change (Ext.mk₀ (𝟙 (SheafOfModules.unit R))).comp hS.extClass (zero_add 1) = hS.extClass
    exact Ext.mk₀_id_comp _
  rw [hclass] at h
  rw [extOneEquivFirstCohomology_apply, ← h]
  rfl

/-- **Stacks 03F1.** The connecting-image formula determines the identification uniquely. -/
@[stacks 03F1 "uniqueness"]
theorem extOneEquivFirstCohomology_unique (R : Sheaf J RingCat.{u})
    (M : SheafOfModules.{u} R)
    (e : Ext (SheafOfModules.unit R) M 1 ≃+ (cohomologyFunctor R 1).obj M)
    (he : ∀ (E : SheafOfModules.{u} R) (f : M ⟶ E)
      (g : E ⟶ SheafOfModules.unit R) (w : f ≫ g = 0)
      (hS : (ShortComplex.mk f g w).ShortExact),
      e hS.extClass =
        (eqToHom (universalCohomologyDeltaFunctor_functor R 1)).app M
          ((universalCohomologyDeltaFunctor R).δ hS 0
            ((cohomologyZeroMap R).app (SheafOfModules.unit R)
              (SheafOfModules.unitHomEquiv (SheafOfModules.unit R) (𝟙 _))))) :
    e = extOneEquivFirstCohomology R M := by
  ext ξ
  obtain ⟨E, f, g, w, hS, hξ⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (SheafOfModules.{u} R) (SheafOfModules.unit R) M).1 ξ
  rw [← hξ]
  exact (he E f g w hS).trans (extOneEquivFirstCohomology_extClass R M E f g w hS).symm

/-- **Stacks 03F1.** The identification is natural in the coefficient module sheaf. -/
@[stacks 03F1 "naturality"]
theorem extOneEquivFirstCohomology_naturality (R : Sheaf J RingCat.{u})
    {M N : SheafOfModules.{u} R} (f : M ⟶ N) (e : Ext (SheafOfModules.unit R) M 1) :
    extOneEquivFirstCohomology R N
        ((Ext.mk₀ f).postcomp (SheafOfModules.unit R) (Nat.add_zero 1) e) =
      (cohomologyFunctor R 1).map f (extOneEquivFirstCohomology R M e) := by
  have hnat := congrArg (fun φ => AddEquiv.ulift.{u, u + 1} (φ e))
    (((extCohomologyDeltaIso R).hom.app 1).naturality f)
  rw [extOneEquivFirstCohomology_apply, extOneEquivFirstCohomology_apply]
  erw [hnat]
  exact ConcreteCategory.congr_hom
    ((eqToHom (universalCohomologyDeltaFunctor_functor R 1)).naturality f) _

end Stacks.Cohomology.SiteModules
