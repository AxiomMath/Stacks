module

public import Mathlib.Topology.Separation.Hausdorff
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-compact subsets of Hausdorff spaces

In a Hausdorff space, every quasi-compact subset is closed, and two disjoint quasi-compact
subsets admit disjoint open neighbourhoods.

Both conclusions are registered directly from Mathlib. The second is expressed using
`SeparatedNhds`, whose definition gives the required disjoint open neighbourhoods.

## References

* [Stacks Project, Tag 08YB](https://stacks.math.columbia.edu/tag/08YB)
-/

@[expose] public section

add_to_stacks 08YB "(1)" IsCompact.isClosed
add_to_stacks 08YB "(2)" SeparatedNhds.of_isCompact_isCompact
add_to_sga "4 Vbis 4.1.4" "case A ∩ B = ∅" SeparatedNhds.of_isCompact_isCompact
