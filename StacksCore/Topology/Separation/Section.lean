module

public import Mathlib.Topology.Separation.Hausdorff
import StacksCore.Tactic.StacksAttribute

/-!
# Closed images of sections in Hausdorff spaces

Let `f : X → Y` be continuous with `X` Hausdorff. A continuous section `s : Y → X` of `f`
has closed image in `X`.

This is registered directly as Mathlib's `Function.LeftInverse.isClosed_range`: the section
condition is expressed by `Function.LeftInverse f s`.

## References

* [Stacks Project, Tag 08ZG](https://stacks.math.columbia.edu/tag/08ZG)
-/

@[expose] public section

add_to_stacks 08ZG "a retract of a Hausdorff space is closed" Function.LeftInverse.isClosed_range
