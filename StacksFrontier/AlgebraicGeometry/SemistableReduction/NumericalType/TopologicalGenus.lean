module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Graph

/-!
# The topological genus of a numerical type

The *topological genus* of a numerical type is the cycle rank `1 - n + e` of its
intersection graph, where `n` is the number of components and `e` the number of
pairs of distinct components whose intersection number is positive.

## Main definitions

* `AlgebraicGeometry.NumericalType.topologicalGenus`.

## Main results

* `AlgebraicGeometry.NumericalType.topologicalGenus_nonneg`: the topological
  genus is nonnegative, the intersection graph being connected.

## Implementation notes

The topological genus is an integer, as is
`AlgebraicGeometry.NumericalType.genus`, against which it is compared; that it
is a nonnegative integer is `topologicalGenus_nonneg`.

## References

* [Stacks Project, Tag 0C78](https://stacks.math.columbia.edu/tag/0C78)
* [Stacks Project, Tag 0C79](https://stacks.math.columbia.edu/tag/0C79)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-- The **topological genus** of a numerical type: one minus its number of
components plus the number of pairs of distinct components whose intersection
number is positive. -/
@[stacks 0C79]
public def topologicalGenus (T : NumericalType) : ℤ :=
  (1 : ℤ) - T.componentCount + edgeCount T

/-- The topological genus of a numerical type is nonnegative. -/
public lemma topologicalGenus_nonneg (T : NumericalType) : 0 ≤ topologicalGenus T :=
  one_sub_componentCount_add_edgeCount_nonneg T

end AlgebraicGeometry.NumericalType
