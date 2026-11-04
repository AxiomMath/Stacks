module

public import Mathlib.Topology.SeparatedMap
import StacksCore.Tactic.StacksAttribute

/-!
# Characterizations of separated maps

For a continuous map `f : X → Y`, Stacks 0CY2 equates three conditions: the canonical map
`X → X ×_Y X` is closed, its diagonal image is closed, and distinct points in a fibre have
disjoint open neighbourhoods. Mathlib defines `IsSeparatedMap` by the third condition and
proves the two equivalences registered below.

## References

* [Stacks Project, Tag 0CY1](https://stacks.math.columbia.edu/tag/0CY1)
* [Stacks Project, Tag 0CY2](https://stacks.math.columbia.edu/tag/0CY2)
-/

@[expose] public section

add_to_stacks 0CY1 IsSeparatedMap
add_to_stacks 0CY1 isSeparatedMap_iff_isClosedMap

add_to_stacks 0CY2 "(3) distinct points in a fibre have disjoint open neighbourhoods"
  IsSeparatedMap
add_to_stacks 0CY2 "(1) ↔ (3): the canonical map X → X ×_Y X is closed"
  isSeparatedMap_iff_isClosedMap
add_to_stacks 0CY2 "(2) ↔ (3): the diagonal is closed in X ×_Y X"
  isSeparatedMap_iff_isClosed_diagonal
