module

public import StacksFrontier.AlgebraicGeometry.Quot.PullSheafHomComparisonIsIso
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualOfPullSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectDerivedTensor

/-!
# Two held inputs of Stacks 0DKY, from the base

Two of the inputs that the proof of Stacks 0DKY on this branch takes as propositions are proved
on the base: Stacks 0DKB and the second assertion of Stacks 0DKS.
This file derives the two propositions from the base's statements, and then Stacks 0DKY, in the
form its consumers take, from the two inputs that are still pending. Nothing is registered.

## Main results

* `AlgebraicGeometry.Space.pseudoCoherentHomotopyColimitApproximation_of_base`:
  `AlgebraicGeometry.Space.PseudoCoherentHomotopyColimitApproximation`, from the base's Stacks
  0DKB, `AlgebraicGeometry.Space.isPseudoCoherent_iff_exists_isHomotopyColimitWith`.
* `AlgebraicGeometry.Space.tensorPerfectRelativelyPerfect_of_base`:
  `AlgebraicGeometry.Space.TensorPerfectRelativelyPerfect`, from the base's second assertion of
  Stacks 0DKS, `AlgebraicGeometry.Space.isRelativelyPerfect_derivedTensor`.
* `AlgebraicGeometry.Space.relativeDerivedHomDualExistsNaturalCompatible_of_pushforwardBaseChange`:
  Stacks 0DKY in the natural and compatible form, from Stacks 0DKX and the invertibility of the
  map of Stacks 08JF for perfect sources only.
* In `AlgebraicGeometry.Space`,
  `relativeDerivedHomDualExistsNaturalCompatible_of_relativelyPerfectPushforwardBaseChange`:
  Stacks 0DKY in the natural and compatible form, from Stacks 0DKX alone, the invertibility of
  the map of Stacks 08JF for perfect sources being
  `AlgebraicGeometry.Space.pullSheafHomComparisonIsIso`.

## References

* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 0DKB](https://stacks.math.columbia.edu/tag/0DKB)
* [Stacks Project, Tag 0DKS](https://stacks.math.columbia.edu/tag/0DKS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

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

/-- **Stacks 0DKB, in the shape the proof of Stacks 0DKY takes** (unregistered):
`AlgebraicGeometry.Space.PseudoCoherentHomotopyColimitApproximation` holds. This is the base's
`AlgebraicGeometry.Space.isPseudoCoherent_iff_exists_isHomotopyColimitWith`, read
at the standard model. -/
theorem pseudoCoherentHomotopyColimitApproximation_of_base :
    PseudoCoherentHomotopyColimitApproximation B S hS :=
  fun hZ X hqc hqs K =>
    isPseudoCoherent_iff_exists_isHomotopyColimitWith B S hS hZ X.1 X.2 hqc hqs K

/-- **Stacks 0DKS, the second assertion, in the shape the proof of Stacks 0DKY takes**
(unregistered): `AlgebraicGeometry.Space.TensorPerfectRelativelyPerfect` holds. This is the
base's `AlgebraicGeometry.Space.isRelativelyPerfect_derivedTensor` at the
canonical derived tensor product, `Y`-perfectness being
`AlgebraicGeometry.Space.IsPerfectRelativeToCanonical` by
`AlgebraicGeometry.Space.isRelativelyPerfect_iff_isPerfectRelativeToCanonical`. -/
theorem tensorPerfectRelativelyPerfect_of_base : TensorPerfectRelativelyPerfect B S hS := by
  intro X Y f hflat hlfp K M hK hM
  -- The base lemma carries a derived category on each slice of the small étale site of `X`,
  -- used only in its proof; any one will do.
  let : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      HasDerivedCategory.{u + 1}
        (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U)) :=
    fun _ => HasDerivedCategory.standard _
  exact (isRelativelyPerfect_iff_isPerfectRelativeToCanonical B S hS f hflat hlfp _).1
    (isRelativelyPerfect_derivedTensor B S hS f hflat hlfp
      (smallEtaleDerivedTensorProduct B S hS X) K M hK
      ((isRelativelyPerfect_iff_isPerfectRelativeToCanonical B S hS f hflat hlfp M).2 hM))

/-- **Stacks 0DKY from Stacks 0DKX and Stacks 08JF** (unregistered): granted Stacks 0DKX and
the invertibility of the map of Stacks 08JF for perfect sources, both not yet proved here, the
natural and compatible form of Stacks 0DKY,
`AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNaturalCompatible`, holds. This is
`AlgebraicGeometry.Space.relativeDerivedHomDualExistsNaturalCompatible` with Stacks 0DKB and
Stacks 0DKS (2) discharged from the base. -/
theorem relativeDerivedHomDualExistsNaturalCompatible_of_pushforwardBaseChange
    (h0DKX : RelativelyPerfectPushforwardBaseChange B S hS)
    (hH : PullSheafHomComparisonIsIso B S hS) :
    RelativeDerivedHomDualExistsNaturalCompatible B S hS :=
  relativeDerivedHomDualExistsNaturalCompatible B S hS
    (pseudoCoherentHomotopyColimitApproximation_of_base B S hS) h0DKX
    (tensorPerfectRelativelyPerfect_of_base B S hS) hH

/-- **Stacks 0DKY from Stacks 0DKX** (unregistered): granted Stacks 0DKX (not yet proved
here), the natural and compatible form of Stacks 0DKY,
`AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNaturalCompatible`, holds. This is
`AlgebraicGeometry.Space.relativeDerivedHomDualExistsNaturalCompatible_of_pushforwardBaseChange`
with the invertibility of the map of Stacks 08JF for perfect sources discharged by
`AlgebraicGeometry.Space.pullSheafHomComparisonIsIso`. -/
theorem relativeDerivedHomDualExistsNaturalCompatible_of_relativelyPerfectPushforwardBaseChange
    (h0DKX : RelativelyPerfectPushforwardBaseChange B S hS) :
    RelativeDerivedHomDualExistsNaturalCompatible B S hS :=
  relativeDerivedHomDualExistsNaturalCompatible_of_pushforwardBaseChange B S hS h0DKX
    (pullSheafHomComparisonIsIso B S hS)

end AlgebraicGeometry.Space

end
