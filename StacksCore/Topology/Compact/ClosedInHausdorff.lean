module

public import Mathlib.Topology.Separation.Hausdorff
import StacksCore.Tactic.StacksAttribute

/-!
# Closed subsets of quasi-compact Hausdorff spaces

In a quasi-compact Hausdorff space, a subset is closed if and only if it is quasi-compact.
The two implications are registered directly from Mathlib as `IsClosed.isCompact` and
`IsCompact.isClosed`. Each theorem uses only the assumptions needed for its implication.

## References

* [Stacks Project, Tag 08YC](https://stacks.math.columbia.edu/tag/08YC)
-/

@[expose] public section

add_to_stacks 08YC "a closed subset of a quasi-compact space is quasi-compact" IsClosed.isCompact
add_to_stacks 08YC "a quasi-compact subset of a Hausdorff space is closed" IsCompact.isClosed
