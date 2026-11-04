module

public import Mathlib.Topology.SeparatedMap
import StacksCore.Tactic.StacksAttribute

/-!
# A continuous map out of a Hausdorff space is separated

Stacks 0CY3: if `X` is Hausdorff then every map `f : X → Y` is separated, i.e. distinct points of
`X` with the same image in `Y` admit disjoint open neighbourhoods. Continuity of `f` is part of the
Stacks formulation but is not needed for the conclusion, and Mathlib's theorem omits it too.

## References

* [Stacks Project, Tag 0CY3](https://stacks.math.columbia.edu/tag/0CY3)
-/

@[expose] public section

add_to_stacks 0CY3 T2Space.isSeparatedMap
