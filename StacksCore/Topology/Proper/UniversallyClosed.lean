module

public import Mathlib.Topology.Maps.Proper.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Universal closedness of continuous maps out of a quasi-compact space

A continuous map from a quasi-compact space to a Hausdorff space is proper
(`Continuous.isProperMap`). Proper maps are universally closed: their products with the
identity map of any topological space are closed (`IsProperMap.universally_closed`).

## References

* [Stacks Project, Tag 08YD](https://stacks.math.columbia.edu/tag/08YD)
-/

@[expose] public section

add_to_stacks 08YD "a continuous map from a quasi-compact space to a Hausdorff space is proper"
  Continuous.isProperMap
add_to_stacks 08YD "proper maps are universally closed" IsProperMap.universally_closed
