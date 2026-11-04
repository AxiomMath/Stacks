module

public import Mathlib.Topology.Compactness.Compact
import StacksCore.Tactic.StacksAttribute

/-!
# The finite intersection property in quasi-compact spaces

In a quasi-compact space, a family of closed subsets whose finite intersections are nonempty
has nonempty intersection. This is registered directly as Mathlib's
`CompactSpace.iInter_nonempty`.

## References

* [Stacks Project, Tag 005D](https://stacks.math.columbia.edu/tag/005D)
-/

@[expose] public section

add_to_stacks 005D "the finite intersection property in a quasi-compact space"
  CompactSpace.iInter_nonempty
