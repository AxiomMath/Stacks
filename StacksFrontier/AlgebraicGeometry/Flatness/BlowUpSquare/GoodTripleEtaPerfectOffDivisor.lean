module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartBasis
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect
public import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up complexes: Stacks tag 0GTW with the charts off the divisor supplied

`AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedEta_obj` asks, at the points off
the divisor `D`, for affine charts with principal determinantal ideals. Off `D` the equation `f`
of a chart is a unit, so its determinantal ideals are the unit ideal, and a chart exists around
every point because `M` is perfect: that is
`ComplexAndDivisorSituation.exists_chart_isPrincipal_determinantalIdeal_of_notMem_supportSet`.
This file discharges that input, leaving the affine-chart comparison as a hypothesis.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedEta_obj_of_isGoodTriple`:
  for a good triple and an affine-chart comparison, `Lη_I M` is perfect.  Tag 0GTW, with the
  comparison discharged too, is
  `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodTriple.isPerfect_derivedEta_obj`.

## References

* [Stacks Project, Tag 0GTW](https://stacks.math.columbia.edu/tag/0GTW)
* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesHomology

universe u d

attribute [local instance] AlgebraicGeometry.ComplexAndDivisorSituation.isEffectiveCartierDivisor

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable {S : ComplexAndDivisorSituation.{u, d}}

attribute [local instance 100000] modulesHasDerivedCategory

/-- If `(X, D, M)` is a good triple, then `Lη_I M` is a perfect object of `D(𝒪_X)`, for every
functor `Lη_I` with the properties of tag 0F8Q and every affine-chart comparison of the shape of
the second assertion of tag 0GTV.  The comparison is a theorem of the library,
`AlgebraicGeometry.ComplexAndDivisorSituation.chartDecalage_of_derivedEta`, and Stacks tag 0GTW
with it discharged is
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodTriple.isPerfect_derivedEta_obj`. -/
theorem isPerfect_derivedEta_obj_of_isGoodTriple (S : ComplexAndDivisorSituation.{u, d})
    (E : Stacks.Divisors.Eta.DerivedEta S.D)
    (hS : IsGoodTriple S)
    (hcomp : ChartDecalage S E) :
    RingedSpace.IsPerfect (X := S.X.toRingedSpace) (E.functor.obj S.M) :=
  isPerfect_derivedEta_obj S E hS
    (fun _ hx => S.exists_chart_isPrincipal_determinantalIdeal_of_notMem_supportSet hx) hcomp

end AlgebraicGeometry.ComplexAndDivisorSituation

end
