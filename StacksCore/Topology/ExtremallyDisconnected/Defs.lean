module

public import Mathlib.Topology.ExtremallyDisconnected
import StacksCore.Tactic.StacksAttribute

/-!
# Extremally disconnected spaces

Stacks 08YI: a topological space is *extremally disconnected* if the closure of every open subset
of it is open. This is Mathlib's class `ExtremallyDisconnected`, whose only field is exactly that
condition.

## References

* [Stacks Project, Tag 08YI](https://stacks.math.columbia.edu/tag/08YI)
-/

@[expose] public section

add_to_stacks 08YI "extremally disconnected spaces" ExtremallyDisconnected
add_to_stacks 08YI "the closure of every open subset is open" ExtremallyDisconnected.open_closure
