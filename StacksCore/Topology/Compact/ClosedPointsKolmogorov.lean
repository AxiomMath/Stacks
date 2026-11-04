module

public import Mathlib.Topology.JacobsonSpace

/-!
# The closed points of a quasi-compact Kolmogorov space

Every point specializes to a closed point in its closure. The set of closed points therefore
inherits compactness from the ambient space.

## Main results

* `isCompact_closedPoints` (Stacks 08ZM): the set of closed points of a quasi-compact Kolmogorov
  space is quasi-compact.

## References

* [Stacks Project, Tag 08ZM](https://stacks.math.columbia.edu/tag/08ZM)
-/

@[expose] public section

/-- **Stacks 08ZM.** Let `X` be a quasi-compact Kolmogorov (`T₀`) topological space. Then the set
`closedPoints X` of closed points of `X` is quasi-compact.

Every point specializes to a closed point in its closure, so compactness descends from `X` to
`closedPoints X`. -/
@[stacks 08ZM]
theorem isCompact_closedPoints (X : Type*) [TopologicalSpace X] [CompactSpace X] [T0Space X] :
    IsCompact (closedPoints X) := by
  refine isCompact_univ.of_subset_of_specializes (Set.subset_univ _) fun x _ ↦ ?_
  obtain ⟨y, hy, hy_closed⟩ := isClosed_closure.exists_closed_singleton
    (Set.singleton_nonempty x).closure
  exact ⟨y, hy_closed, specializes_iff_mem_closure.mpr hy⟩
