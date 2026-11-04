module

public import Mathlib.Topology.Separation.Hausdorff
import StacksCore.Tactic.StacksAttribute

/-!
# Local quasi-compactness of a Hausdorff space

Stacks 08ZR — a Hausdorff space is locally quasi-compact if and only if every point has a
quasi-compact neighbourhood — is Mathlib's pair `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`
(the forward direction) and `WeaklyLocallyCompactSpace.locallyCompactSpace` (the converse, proved
under the weaker `R1Space` hypothesis that `T2Space` supplies).

## References

* [Stacks Project, Tag 08ZR](https://stacks.math.columbia.edu/tag/08ZR)
-/

@[expose] public section

add_to_stacks 08ZR "every point of a locally quasi-compact space has a quasi-compact neighbourhood"
  WeaklyLocallyCompactSpace.exists_compact_mem_nhds
add_to_stacks 08ZR "conversely, an R₁ (in particular Hausdorff) space in which every point has a
  quasi-compact neighbourhood is locally quasi-compact"
  WeaklyLocallyCompactSpace.locallyCompactSpace
