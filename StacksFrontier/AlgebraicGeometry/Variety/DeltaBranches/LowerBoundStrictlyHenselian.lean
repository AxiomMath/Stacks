module

public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.DeltaBranchBound

/-!
# The delta invariant bounds the number of geometric branches, strictly henselian case

For a strictly henselian, reduced Nagata local ring, the delta invariant is at least one less
than the number of geometric branches.

Both invariants take values in `ℕ∞`, so subtraction on the right is truncated subtraction in
the extended natural numbers. No dimension hypothesis is needed.

The statement is `Ring.deltaInvariant_ge_numberOfGeometricBranches_sub_one_of_strictlyHenselian`,
which this module re-exports from
`StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.DeltaBranchBound`.

## References

* [Stacks Project, Tag 0C42](https://stacks.math.columbia.edu/tag/0C42)
-/
