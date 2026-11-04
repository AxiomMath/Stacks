module

public import Mathlib.Topology.Connected.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The image of a connected subset is connected

A continuous map sends a connected subset to a connected subset. This is registered directly
as Mathlib's `IsConnected.image`, which only requires continuity on the subset.

## References

* [Stacks Project, Tag 0376](https://stacks.math.columbia.edu/tag/0376)
-/

@[expose] public section

add_to_stacks 0376 "the image of a connected set under a continuous map is connected"
  IsConnected.image
