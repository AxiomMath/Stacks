module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorCommShiftComplexBifunctors
import StacksCore.Tactic.StacksAttribute

/-!
# Shift compatibility of the two comparisons of Tag 079U

The comparison `Stacks.Cohomology.DerivedPullbackTensor.modelComparison` of [Stacks, Tag 079U]
on a pair of K-flat complexes is `leftComparison` followed by the inverse of `rightComparison`.
This file states the shift compatibility of these two comparisons, in the curried form taken by
`CategoryTheory.NatTrans.CommShift₂`, between the bifunctors `(K, L) ↦ Lf^*(QK ⊗^L QL)`,
`(K, L) ↦ Lf^*(QK) ⊗^L Lf^*(QL)` and `(K, L) ↦ Q(f^*Tot(K ⊗ L))`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackTensor.LeftComparisonCommShift₂`: `leftComparison`, curried,
  is compatible with the shifts in each variable.
* `Stacks.Cohomology.DerivedPullbackTensor.RightComparisonCommShift₂`: `rightComparison`,
  curried, is compatible with the shifts in each variable.
* `Stacks.Cohomology.DerivedPullbackTensor.RightComparisonCommShiftApp` and
  `Stacks.Cohomology.DerivedPullbackTensor.RightComparisonCommShiftFlipApp`: the two one-variable
  halves of `RightComparisonCommShift₂`.
* `Stacks.Cohomology.DerivedPullbackTensor.DerivedToTensorCommShift₂`: the canonical map from the
  derived tensor product to the ordinary total tensor complex, curried, is compatible with the
  shifts in each variable.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.rightComparisonCommShift₂_of`:
  `RightComparisonCommShift₂` follows from its two one-variable halves.

## Implementation notes

`leftComparison f` is `Functor.whiskerRight (derivedToTensorNatTrans Y) Lf^*` followed by
`Functor.whiskerLeft (totalComplexPair _) (derivedPullbackNatTrans f)`, and `rightComparison f`
is built from the derived pullback in each variable, `derivedToTensorNatTrans X` and
`pullbackTensorComplexNatIso f`. Every factor other than `derivedToTensorNatTrans` is
shift-compatible by a whiskering of a shift-compatible transformation, so
`DerivedToTensorCommShift₂` is the one condition the two comparisons share.

A `CategoryTheory.NatTrans.CommShift₂` structure consists of two one-variable conditions, and
`RightComparisonCommShift₂` is reduced to them. In `RightComparisonCommShiftApp`,
`RightComparisonCommShiftFlipApp` and `rightComparisonCommShift₂_of` the shift data of the source
and target are introduced with `letI`: with `haveI` the synthesised instance is not definitionally
equal to the one inferred by the typing rules, and the statement does not elaborate.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

attribute [local instance] HasDerivedCategory.standard

open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules)

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The curried form of `Stacks.Cohomology.DerivedPullbackTensor.leftComparison` is compatible
with the shifts in each variable separately, for the shift data
`curryComplexesPullbackOfTensor_commShift₂Int` on its source and
`curryComplexesTotalPullback_commShift₂Int` on its target. -/
def LeftComparisonCommShift₂ : Prop :=
  haveI := curryComplexesPullbackOfTensor_commShift₂Int f
  haveI := curryComplexesTotalPullback_commShift₂Int f
  NatTrans.CommShift₂Int (Functor.curry.map (leftComparison f))

/-- The curried form of `Stacks.Cohomology.DerivedPullbackTensor.rightComparison` is compatible
with the shifts in each variable separately, for the shift data
`curryComplexesTensorOfPullbacks_commShift₂Int` on its source and
`curryComplexesTotalPullback_commShift₂Int` on its target. -/
def RightComparisonCommShift₂ : Prop :=
  haveI := curryComplexesTensorOfPullbacks_commShift₂Int f
  haveI := curryComplexesTotalPullback_commShift₂Int f
  NatTrans.CommShift₂Int (Functor.curry.map (rightComparison f))

/-- For every complex `K`, the transformation `(Functor.curry.map (rightComparison f)).app K`,
natural in the second variable `L`, commutes with the shifts, for the shift data at which
`RightComparisonCommShift₂` is stated. -/
def RightComparisonCommShiftApp : Prop :=
  letI := curryComplexesTensorOfPullbacks_commShift₂Int f
  letI := curryComplexesTotalPullback_commShift₂Int f
  ∀ K : CochainComplex (Modules Y) ℤ,
    NatTrans.CommShift ((Functor.curry.map (rightComparison f)).app K) ℤ

/-- For every complex `L`, the transformation `(Functor.curry.map (rightComparison f)).flipApp L`,
natural in the first variable `K`, commutes with the shifts, for the shift data at which
`RightComparisonCommShift₂` is stated. -/
def RightComparisonCommShiftFlipApp : Prop :=
  letI := curryComplexesTensorOfPullbacks_commShift₂Int f
  letI := curryComplexesTotalPullback_commShift₂Int f
  ∀ L : CochainComplex (Modules Y) ℤ,
    NatTrans.CommShift ((Functor.curry.map (rightComparison f)).flipApp L) ℤ

/-- `RightComparisonCommShift₂ f` holds as soon as its two one-variable halves
`RightComparisonCommShiftApp f` and `RightComparisonCommShiftFlipApp f` do. -/
theorem rightComparisonCommShift₂_of (happ : RightComparisonCommShiftApp f)
    (hflip : RightComparisonCommShiftFlipApp f) : RightComparisonCommShift₂ f :=
  let := curryComplexesTensorOfPullbacks_commShift₂Int f
  let := curryComplexesTotalPullback_commShift₂Int f
  { commShift_app := happ
    commShift_flipApp := hflip }

/-- The curried form of the canonical map `derivedToTensorNatTrans Z` from the derived tensor
product on `Z` to the ordinary total tensor complex is compatible with the shifts in each
variable separately. -/
def DerivedToTensorCommShift₂ (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    Prop :=
  haveI := curryComplexesDerivedTensor_commShift₂Int Z
  haveI := curryComplexesTotal_commShift₂Int Z
  NatTrans.CommShift₂Int (Functor.curry.map (derivedToTensorNatTrans Z))

end Stacks.Cohomology.DerivedPullbackTensor

end
