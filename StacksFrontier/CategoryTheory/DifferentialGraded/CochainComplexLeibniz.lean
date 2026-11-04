module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory

/-!
# The Leibniz rule for composition of homogeneous maps of complexes

In the differential graded category of cochain complexes over a preadditive category, the
differential of a composite of homogeneous maps satisfies the graded Leibniz rule
`d (g ∘ f) = d g ∘ f + (-1)^m (g ∘ d f)` for `g` of degree `m`.

## Main results

The Leibniz rule is `DGCategory.leibniz`, a field of the differential graded category structure,
so the statement for complexes is that projection applied to `CochainComplex.dgCategory`.

## Implementation notes

`CochainComplex.dgCategory` verifies the Leibniz axiom as part of constructing the differential
graded category of complexes, so the existing projection `DGCategory.leibniz` applied to that
construction already is this proposition and no specialization of it is introduced. This file
therefore only records which declaration carries the source's statement.

## References

* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9)
-/

add_to_stacks 09L9 "composition_leibniz" DGCategory.leibniz
