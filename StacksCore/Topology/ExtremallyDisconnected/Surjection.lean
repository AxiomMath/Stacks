module

public import Mathlib.Topology.ExtremallyDisconnected
import StacksCore.Tactic.StacksAttribute

/-!
# Surjections onto an extremally disconnected space

Stacks 08YL: a continuous surjection `f : X → Y` of quasi-compact Hausdorff spaces with `Y`
extremally disconnected that carries no proper closed subset of `X` onto `Y` is a homeomorphism.
Mathlib constructs that homeomorphism, and does not need `Y` to be quasi-compact.

## References

* [Stacks Project, Tag 08YL](https://stacks.math.columbia.edu/tag/08YL)
-/

@[expose] public section

add_to_stacks 08YL ExtremallyDisconnected.homeoCompactToT2
