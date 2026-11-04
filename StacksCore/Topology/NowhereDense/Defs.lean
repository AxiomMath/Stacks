module

public import Mathlib.Topology.GDelta.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Nowhere dense subsets

Stacks 03HN defines the *interior* of a subset `T` of a topological space to be the largest open
subset contained in `T`, and calls `T` *nowhere dense* if the closure of `T` has empty interior.

Both are Mathlib definitions, and they are the same definitions: `interior T` is
`⋃₀ {U | IsOpen U ∧ U ⊆ T}` and `IsNowhereDense T` is `interior (closure T) = ∅`. That
`interior T` is the largest open subset of `T` is `isOpen_interior`, `interior_subset` and
`interior_maximal`.

## References

* [Stacks Project, Tag 03HN](https://stacks.math.columbia.edu/tag/03HN)
-/

@[expose] public section

add_to_stacks 03HN "the interior of a subset" interior
add_to_stacks 03HN "a nowhere dense subset" IsNowhereDense
