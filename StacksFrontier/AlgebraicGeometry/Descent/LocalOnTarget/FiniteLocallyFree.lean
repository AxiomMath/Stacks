module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Integral
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Degree

/-!
# Finite locally free morphisms are fpqc local on the base

A morphism of schemes is finite locally free precisely when its base changes along the members
of an fpqc covering of the target are finite locally free, and the same holds with a degree
`d ≥ 0` fixed throughout. This is Tag 02VO.

Both clauses are stated and proved in
`StacksFrontier/AlgebraicGeometry/FiniteLocallyFree/FpqcLocalAtTarget.lean`, as
`Stacks.Morphisms.isFiniteLocallyFree_isLocalAtTarget_fpqc` and
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_isLocalAtTarget_fpqc`, and are re-exported here.

## References

* [Stacks Project, Tag 02VO](https://stacks.math.columbia.edu/tag/02VO)
-/
