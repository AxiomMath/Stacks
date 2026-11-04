module

public import Mathlib.Topology.SeparatedMap
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of a separated map is separated

Stacks 0CY4: if `f : X → Y` is separated and `g : Y' → Y` is a continuous map, then the
projection `Y' ×_Y X → Y'` is separated.

This is Mathlib's theorem, stated there for the fibre product `Function.Pullback` and its
projection `Function.Pullback.snd`. Continuity of `g` is part of the Stacks formulation but is
not needed for the conclusion, and Mathlib does not assume it.

## References

* [Stacks Project, Tag 0CY4](https://stacks.math.columbia.edu/tag/0CY4)
-/

@[expose] public section

add_to_stacks 0CY4 "the base change of a separated map is separated" IsSeparatedMap.pullback
