module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement

/-!
# Tag 01NR's two chart-formula assertions

This file registers two of the assertions of Tag 01NR on declarations proved in
`StacksFrontier/AlgebraicGeometry/RelativeProjTwists/Statement.lean`. It attaches no attribute of its
own: the two registrations below are `add_to_stacks` commands over the existing declarations.

## The tag's five assertions

Tag 01NR states five labelled assertions:

1. `"the graded twists and homogeneous-section map"`: the existence of the twist data,
   `Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`. Its cocycle hypothesis
   `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` is discharged by
   `Stacks.AlgebraicGeometry.ProjTwistCocycle.isNestedCocycle`; the multiplication and unit come
   from `Stacks.AlgebraicGeometry.GluedTwistAlgebra.gluedTwistAlgebra` and the section map from
   `Stacks.AlgebraicGeometry.GluedTwistSectionMap.mkOfGradedAlgebra`.
2. `"multiplication on affine charts"`: registered here on
   `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.chartIso_mul`.
3. `"the unit on affine charts"`: registered here on
   `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.chartIso_one`.
4. `"uniqueness of the complete structure"`:
   `Stacks.AlgebraicGeometry.TwistExistence.isUniqueTwistData`.
5. `"uniqueness of the affine-chart identifications"`:
   `Stacks.AlgebraicGeometry.TwistRigidity.determinesChartIso`.

## What assertions 2 and 3 say

Each of them is a single assertion, stated for an arbitrary `D : TwistData A` in place of the
canonical twist data; the universally quantified form implies the statement for any particular
construction, and a `TwistData` carries no hypothesis beyond the structure itself. Assertions 4
and 5 are stated in the same way.

They are projections: `chartIso_mul` is `D.isGradedChartIso.1` and `chartIso_one` is
`D.isGradedChartIso.2`. This is the shape of the statement itself, in which the twist data carries
`isGradedChartIso` as a field and the two conjuncts are then restated as separate assertions about
the canonical datum. Their content therefore lies in the construction of a term,
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

add_to_stacks 01NR "multiplication on affine charts"
  Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.chartIso_mul

add_to_stacks 01NR "the unit on affine charts"
  Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.chartIso_one
