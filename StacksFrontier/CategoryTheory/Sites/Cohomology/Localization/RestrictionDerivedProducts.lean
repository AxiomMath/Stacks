module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.KInjectiveRestrictionAlongOverMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProductsFunctor

/-!
# Derived restriction to a slice site preserves countable products

Let `(C, J)` be a site, let `R` be a sheaf of rings on it and let `U` be an object of `C`.
Restriction of sheaves of modules to the slice site `C/U` is exact, so it induces a functor
`D(R) ⥤ D(R_U)` of derived categories; this file proves that the induced functor preserves
countable products, and the same for the restriction `C/U ⟶ C/V` along an arrow `a : V ⟶ U`.

## Main results

* `Stacks.Cohomology.Localization.preservesProducts_overFunctor`: restriction to the slice site
  preserves countable products of sheaves of modules.
* `Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overFunctor`: the induced
  functor of derived categories preserves countable products.
* `Stacks.Cohomology.Localization.preservesProducts_overMap` and
  `Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overMap`: the same two
  statements for the restriction between two slices, along `Over.map a`.

## Implementation notes

The exactness hypothesis of [Stacks, Tag 07KC] — Grothendieck's AB4*, that countable products
are exact — is unavailable for sheaves of modules, so the general
`CategoryTheory.Functor.preservesProducts_mapDerivedCategory` of
`StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections` cannot be used. The route
taken is the K-injective one,
`CategoryTheory.Functor.preservesProducts_mapDerivedCategory_of_isKInjective`, whose three
inputs are all available here:

* restriction preserves countable products of sheaves of modules because it is a *right
  adjoint*: `SheafOfModules.overFunctor R U` is by definition
  `SheafOfModules.pushforward (𝟙 (R.over U))` along `Over.forget U`, and
  `SheafOfModules.pullbackPushforwardAdjunction` exhibits extension by zero as a left adjoint of
  it. Instance search will not find the adjointness through the `overFunctor` spelling, which has
  a different head symbol, so the adjunction is named and the preservation deduced from it by
  `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`. For `SheafOfModules.overMap a` the
  same device needs one more step: `(SheafOfModules.pushforward φ).IsRightAdjoint` is stated
  over `(PresheafOfModules.pushforward φ.hom).IsRightAdjoint`, which instance search does not
  discharge there, so `PresheafOfModules.isRightAdjoint_pushforward_of_univLE` is supplied by
  name;
* restriction carries K-injective complexes to K-injective complexes:
  `Stacks.Cohomology.Localization.isKInjective_over` and, between two slices,
  `Stacks.Cohomology.Localization.isKInjective_overMap`, both [Stacks, Tag 08FI];
* every complex of sheaves of modules admits a quasi-isomorphism to a K-injective complex:
  `HomologyComparison.exists_quasiIso_isKInjective_sheafOfModules`, in the namespace
  `Stacks.Cohomology.HypercohomologyEdge`.

The countable products of the two derived categories come from
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`, the same
K-injective route taken for their mere existence.

Site, morphisms, sheaf of rings and modules all live in one universe `u`, as they do in
`isKInjective_over`, which is what the proof consumes; the model of each derived category is a
free binder, so the results apply at `HasDerivedCategory.standard` as well as at any other
model.

No `@[stacks]` attribute is attached: [Stacks, Tag 08FI] is carried by `isKInjective_over` and
[Stacks, Tag 0BK6] by the declarations the product statement is proved from.

## References

* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

universe u w w'

namespace Stacks.Cohomology.Localization

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})
  (U : C)

/-- **Restriction of sheaves of modules to a slice site preserves countable products**, being a
right adjoint: extension by zero along `Over.forget U` is a left adjoint of it. -/
theorem preservesProducts_overFunctor :
    PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.overFunctor.{u} R U) :=
  have h : PreservesLimitsOfSize.{0, 0} (SheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))) :=
    (SheafOfModules.pullbackPushforwardAdjunction (F := Over.forget U)
      (𝟙 (R.over U) : (R.over U) ⟶ (R.over U))).rightAdjoint_preservesLimits
  h.preservesLimitsOfShape

/-- Countable products in the derived category of sheaves of modules on `C`, at any model. -/
theorem hasProductsOfShape_nat_derivedCategory
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)] :
    HasProductsOfShape ℕ (DerivedCategory (SheafOfModules.{u} R)) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules.{w, u, u, u, u} R

/-- **The functor of derived categories induced by restriction to a slice site preserves
countable products.** The restriction is exact and preserves countable products of sheaves of
modules (`preservesProducts_overFunctor`) and K-injective complexes
(`Stacks.Cohomology.Localization.isKInjective_over`, [Stacks, Tag 08FI]), and every complex of
sheaves of modules has a K-injective resolution, so
`CategoryTheory.Functor.preservesProducts_mapDerivedCategory_of_isKInjective` applies. No
exactness of the countable products of sheaves of modules is assumed, and none is available.

Exactness of the restriction is taken as hypotheses, as it must be: it is what makes the
statement typecheck, and it is supplied by
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits` and
`..._preservesFiniteColimits`. -/
theorem preservesProducts_mapDerivedCategory_overFunctor
    [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} R U)]
    [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} R U)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (R.over U))] :
    PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.overFunctor.{u} R U).mapDerivedCategory := by
  have := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u} (J := J)
  have := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
    (J := J)
  have := Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u, u, u, u} R
  have := hasProductsOfShape_nat_derivedCategory.{u, w} J R
  have := hasProductsOfShape_nat_derivedCategory.{u, w'} (J.over U) (R.over U)
  have := preservesProducts_overFunctor J R U
  have hres := exists_quasiIso_isKInjective_sheafOfModules.{u, u, u, u, u} R
  exact CategoryTheory.Functor.preservesProducts_mapDerivedCategory_of_isKInjective _ hres
    fun I hI ↦ have := hI; isKInjective_over J R U I

section OverMap

variable {V U : C} (a : V ⟶ U)

/-- **Restriction of sheaves of modules between two slice sites preserves countable products**,
being a right adjoint. The adjointness is not found by instance search: it rests on the
adjointness of the pushforward of *presheaves* of modules, which is
`PresheafOfModules.isRightAdjoint_pushforward_of_univLE` and has to be named. -/
theorem preservesProducts_overMap :
    PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.overMap.{u} R a) :=
  have : (PresheafOfModules.pushforward.{u}
      ((Sheaf.pushforwardOverMapIso R a).inv).hom).IsRightAdjoint :=
    PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{u, u, u, u, u, u} _
  have h : PreservesLimitsOfSize.{0, 0} (SheafOfModules.pushforward.{u} (F := Over.map a)
      (Sheaf.pushforwardOverMapIso R a).inv) :=
    (SheafOfModules.pullbackPushforwardAdjunction (F := Over.map a)
      (Sheaf.pushforwardOverMapIso R a).inv).rightAdjoint_preservesLimits
  h.preservesLimitsOfShape

/-- **The functor of derived categories induced by the restriction between two slice sites
preserves countable products.** This is
`preservesProducts_mapDerivedCategory_overFunctor` for `SheafOfModules.overMap a`, with
`Stacks.Cohomology.Localization.isKInjective_overMap` in place of `isKInjective_over`.

It is this form, rather than the one for `overFunctor`, that the comparison of the
derived-completeness condition over `U` with the condition over `V` consumes: the single-object
product hypothesis of
`AlgebraicGeometry.RingedSite.isDerivedCompleteAt_map_of_center` follows from it. -/
theorem preservesProducts_mapDerivedCategory_overMap
    [PreservesFiniteLimits (SheafOfModules.overMap.{u} R a)]
    [PreservesFiniteColimits (SheafOfModules.overMap.{u} R a)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (R.over V))] :
    PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.overMap.{u} R a).mapDerivedCategory := by
  have := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u} (J := J.over U)
  have := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
    (J := J.over U)
  have := Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u, u, u, u} (R.over U)
  have := hasProductsOfShape_nat_derivedCategory.{u, w} (J.over U) (R.over U)
  have := hasProductsOfShape_nat_derivedCategory.{u, w'} (J.over V) (R.over V)
  have := preservesProducts_overMap J R a
  have hres := exists_quasiIso_isKInjective_sheafOfModules.{u, u, u, u, u} (R.over U)
  exact CategoryTheory.Functor.preservesProducts_mapDerivedCategory_of_isKInjective _ hres
    fun I hI ↦ have := hI; isKInjective_overMap J R a I

end OverMap

end Stacks.Cohomology.Localization

end
