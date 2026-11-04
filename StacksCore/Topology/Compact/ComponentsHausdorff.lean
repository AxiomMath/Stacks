module

public import Mathlib.Topology.Separation.Regular
import StacksCore.Tactic.StacksAttribute

/-!
# Connected components of a quasi-compact Hausdorff space

Stacks 08ZN: in a quasi-compact Hausdorff space the connected component of a point is the
intersection of the clopen subsets containing it.

This is Mathlib's theorem, which indexes the intersection by the subtype of clopen sets
containing the point rather than by `⋂₀` over that family.

## References

* [Stacks Project, Tag 08ZN](https://stacks.math.columbia.edu/tag/08ZN)
-/

@[expose] public section

add_to_stacks 08ZN "the connected component is the intersection of the clopen neighbourhoods"
  connectedComponent_eq_iInter_isClopen
