module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedFibreProduct
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectivePullbackCover

/-!
# Variants of the results of `StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover`

This module proves the joint surjectivity assertion of Definition 0AIM for the chart cover of a
fibre product, the one thing the source's proof of Stacks 0GBD needs of that cover which
`StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover`, where the cover is built, does
not prove.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_chartPullbackMap`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)


section ChartCover

attribute [local instance] sheaf_hasColimits

end ChartCover

end AlgebraicGeometry.FormalSpace

end
