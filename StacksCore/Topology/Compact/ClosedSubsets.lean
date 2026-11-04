module

public import Mathlib.Topology.Compactness.Compact
import StacksCore.Tactic.StacksAttribute

/-!
# Closed subsets of quasi-compact spaces

A closed subset of a quasi-compact topological space is quasi-compact. This is registered
directly as Mathlib's `IsClosed.isCompact`.

The Stacks Project's quasi-compactness carries no Hausdorff assumption: it is expressed by
`IsCompact` for subsets and `CompactSpace` for spaces.

## References

* [Stacks Project, Tag 005C](https://stacks.math.columbia.edu/tag/005C)
-/

@[expose] public section

add_to_stacks 005C "a closed subset of a quasi-compact space is quasi-compact" IsClosed.isCompact
