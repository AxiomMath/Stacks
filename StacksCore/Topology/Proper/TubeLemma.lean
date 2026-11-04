module

public import Mathlib.Topology.Compactness.Compact
import StacksCore.Tactic.StacksAttribute

/-!
# The tube lemma for quasi-compact subsets

An open subset of `X × Y` containing a product `A ×ˢ B` of quasi-compact subsets contains a
product of open sets `U ×ˢ V` with `A ⊆ U` and `B ⊆ V`. This is registered directly as Mathlib's
`generalized_tube_lemma`. Mathlib's `IsCompact` expresses quasi-compactness without requiring
separation assumptions.

## References

* [Stacks Project, Tag 005N](https://stacks.math.columbia.edu/tag/005N)
-/

@[expose] public section

add_to_stacks 005N "the tube lemma for a product of two quasi-compact subsets"
  generalized_tube_lemma
