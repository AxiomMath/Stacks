module

public import StacksFrontier.AlgebraicGeometry.Quot.PullSheafHomComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomPullbackIso

/-!
# Stacks 08JF for algebraic spaces: the comparison out of a perfect object is invertible

Let `g : X ⟶ Y` be a morphism of algebraic spaces, `P` a perfect and `M` an arbitrary object of
`D(𝒪_Y)`. The canonical map `Lg^* R𝓗om(P, M) ⟶ R𝓗om(Lg^*P, Lg^*M)` of Stacks 08JF
(`AlgebraicGeometry.Space.pullSheafHomComparison`) is an isomorphism: its transpose under
Stacks 08J8 is the inverse of the comparison of Stacks 07A4 followed by `Lg^*` of the evaluation,
so `AlgebraicGeometry.Space.isIso_of_homEquiv_symm_eq_pullbackTensorIso` applies.

## Main results

* `AlgebraicGeometry.Space.pullSheafHomComparisonIsIso`: **Stacks 08JF, the invertibility for a
  perfect source**, `AlgebraicGeometry.Space.PullSheafHomComparisonIsIso`.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 08JF, the invertibility for a perfect source.** For every morphism `g : X ⟶ Y` of
algebraic spaces, every perfect `P` and every `M` in `D(𝒪_Y)`, the canonical map
`Lg^* R𝓗om(P, M) ⟶ R𝓗om(Lg^*P, Lg^*M)` is an isomorphism. -/
theorem pullSheafHomComparisonIsIso : PullSheafHomComparisonIsIso B S hS := by
  intro X Y g P M hP
  refine isIso_of_homEquiv_symm_eq_pullbackTensorIso_of_eq g
    ((smallEtaleDerivedPullbackData B S hS).pull g) rfl (smallEtaleDerivedPullbackTensorIso g)
    HEq.rfl P M hP (pullSheafHomComparison g P M) ?_
  rw [homEquiv_symm_pullSheafHomComparison, pullSheafHomComparisonTranspose]
  rfl

end AlgebraicGeometry.Space

end
