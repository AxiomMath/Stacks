module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedIsIso
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import StacksCore.Tactic.StacksAttribute

/-!
# Pullback and derived colimits on the unbounded derived category, at abelian coefficients

For a functor `f : C' ⥤ C` between small categories with their chaotic topologies and a
cosimplicial object `U_•` of `C'` such that both `U_•` and `f(U_•)` are point resolutions, the
identification `Lπ'_! ∘ g^{-1} = Lπ_!` holds as an isomorphism of functors `D(C) ⥤ D(Ab)` on the
unbounded derived category of abelian presheaves. The abelian group `ULift ℤ` is a projective
compact separator of `AddCommGrpCat`.

## Main definitions

* `Stacks.ChaoticSite.uliftIntModuleForget`: the forgetful functor from `ULift ℤ`-modules to
  abelian groups, an additive equivalence.
* `Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionUnboundedNatIso`: the
  isomorphism of functors `Lπ'_! ∘ g^{-1} ≅ Lπ_!` on the unbounded derived category.

## Main results

* `Stacks.ChaoticSite.projective_uliftIntAddCommGrp`: `ULift ℤ` is a projective abelian group.
* `Stacks.ChaoticSite.isCompactObject_uliftIntAddCommGrp`: `ULift ℤ` is a compact object of
  `AddCommGrpCat`.
* `Stacks.ChaoticSite.isSeparating_uliftIntAddCommGrp`: `ULift ℤ` is a separating family of one
  object in `AddCommGrpCat`.
* `Stacks.ChaoticSite.AbelianValued.isIso_derivedColimitPresheafRestrictionUnboundedComparison`:
  the comparison `Lπ'_! ∘ g^{-1} ⟶ Lπ_!` is an isomorphism on the unbounded derived category.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-! ### `ULift ℤ` is a projective compact separator of `AddCommGrpCat` -/

/-- The functor from `ULift ℤ`-modules to abelian groups that restricts scalars along the ring
isomorphism `ℤ ≃+* ULift ℤ` and then forgets the `ℤ`-module structure. Both steps are additive
equivalences, and the composite carries the regular module `ULift ℤ` to the abelian group
`ULift ℤ`. -/
abbrev uliftIntModuleForget : ModuleCat.{u} (ULift.{u} ℤ) ⥤ AddCommGrpCat.{u} :=
  ModuleCat.restrictScalars.{u} (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toRingHom ⋙
    forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}

/-- `ULift ℤ` is a projective object of `AddCommGrpCat`. -/
theorem projective_uliftIntAddCommGrp : Projective (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  uliftIntModuleForget.{u}.projective_obj_of_projective
    (X := ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))
    (inferInstanceAs (Projective (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))))

/-- `ULift ℤ` is a compact object of `AddCommGrpCat`. -/
theorem isCompactObject_uliftIntAddCommGrp :
    IsCompactObject.{u} (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (CategoryTheory.isCompactObject_iff_isCompactObject_obj uliftIntModuleForget.{u}
      (ModuleCat.of (ULift.{u} ℤ) (ULift.{u} ℤ))).mp
    StacksDraft.Perfect.isCompactObject_regularModule

/-- The single object `ULift ℤ` is a separating family in `AddCommGrpCat`. -/
theorem isSeparating_uliftIntAddCommGrp :
    (ObjectProperty.ofObj
      (fun _ : PUnit.{u + 1} ↦ AddCommGrpCat.of (ULift.{u} ℤ))).IsSeparating := by
  have hsep : IsSeparator (AddCommGrpCat.of (ULift.{u} ℤ)) := by
    rw [isSeparator_iff_faithful_coyoneda_obj]
    exact Functor.Faithful.of_iso AddCommGrpCat.coyonedaObjIsoForget.symm
  intro X Y a b h
  refine hsep a b fun G hG k ↦ ?_
  obtain rfl := (ObjectProperty.singleton_iff _ _).mp hG
  exact h _ (ObjectProperty.ofObj_apply _ PUnit.unit) k

/-! ### Abelian coefficients -/

attribute [local instance] projective_uliftIntAddCommGrp

variable {C C' : Type u} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)

/-- For a functor `f : C' ⥤ C` between small categories with their chaotic
topologies and a cosimplicial object `U_•` of `C'` such that both `U_•` and `f(U_•)` are point
resolutions, the comparison `Lπ'_! ∘ g^{-1} ⟶ Lπ_!` of
`Stacks.ChaoticSite.AbelianValued.derivedColimitPresheafRestrictionUnboundedComparison` is an
isomorphism of functors `D(C) ⥤ D(Ab)` on the unbounded derived category `D(C)`. -/
@[stacks 08QA "the identification `Lπ'_! ∘ g^{-1} = Lπ_!` with values in `D(Ab)`, at abelian \
  coefficients, as an isomorphism of functors on the UNBOUNDED derived category `D(C)`, which \
  is what the source's `as functors D(C) ⥤ D(Ab)` says"]
theorem AbelianValued.isIso_derivedColimitPresheafRestrictionUnboundedComparison
    {U : CosimplicialObject C'} (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f)) :
    IsIso (AbelianValued.derivedColimitPresheafRestrictionUnboundedComparison f) :=
  isIso_unboundedComparison_of_isPointResolutions f AddCommGrpCat.{u} hU hfU
    (fun _ : PUnit.{u + 1} ↦ AddCommGrpCat.of (ULift.{u} ℤ))
    (fun _ ↦ isCompactObject_uliftIntAddCommGrp) isSeparating_uliftIntAddCommGrp

/-- For a functor `f : C' ⥤ C` between small categories with their chaotic topologies and a
cosimplicial object `U_•` of `C'` such that both `U_•` and `f(U_•)` are point resolutions, the
isomorphism of functors `Lπ'_! ∘ g^{-1} ≅ Lπ_!` from `D(C)` to `D(Ab)` on the unbounded derived
category. -/
@[stacks 08QA "the identification `Lπ'_! ∘ g^{-1} = Lπ_!` with values in `D(Ab)` as an \
  ISOMORPHISM OF FUNCTORS on the unbounded derived category `D(C)`, packaged from the \
  invertibility of the comparison"]
def AbelianValued.derivedColimitPresheafRestrictionUnboundedNatIso
    {U : CosimplicialObject C'} (hU : IsPointResolution U) (hfU : IsPointResolution (U ⋙ f)) :
    (Stacks.CategoryHomology.presheafRestriction.{u, u, u} f).mapDerivedCategory ⋙
        totalDerivedColimit C' AddCommGrpCat.{u} ≅
      totalDerivedColimit C AddCommGrpCat.{u} :=
  haveI := AbelianValued.isIso_derivedColimitPresheafRestrictionUnboundedComparison f hU hfU
  asIso (AbelianValued.derivedColimitPresheafRestrictionUnboundedComparison f)

end Stacks.ChaoticSite

end
