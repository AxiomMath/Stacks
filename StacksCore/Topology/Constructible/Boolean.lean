module

public import Mathlib.Topology.Constructible
import StacksCore.Tactic.StacksAttribute

/-!
# Boolean operations on constructible subsets

Constructible subsets of a topological space are closed under finite unions, finite
intersections and complements.

The three closure properties are registered directly as Mathlib's
`Topology.IsConstructible.iUnion`, `Topology.IsConstructible.iInter` and
`Topology.IsConstructible.compl`.

## References

* [Stacks Project, Tag 005H](https://stacks.math.columbia.edu/tag/005H)
-/

@[expose] public section

add_to_stacks 005H "a finite union of constructible sets is constructible"
  Topology.IsConstructible.iUnion
add_to_ega "0 9.1.2" "finite unions" Topology.IsConstructible.iUnion
add_to_stacks 005H "a finite intersection of constructible sets is constructible"
  Topology.IsConstructible.iInter
add_to_stacks 005H "the complement of a constructible set is constructible"
  Topology.IsConstructible.compl
