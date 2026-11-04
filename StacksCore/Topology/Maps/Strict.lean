module

public import Mathlib.Topology.Maps.Strict.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Strict and submersive maps

A map `f : X → Y` is strict when the subspace topology and the quotient topology on its
image agree. Mathlib expresses this as `Topology.IsStrictMap f`: the range factorization
of `f` is a quotient map.

A map is submersive if and only if it is strict and surjective. This is registered as
`Topology.isQuotientMap_iff_isStrictMap_surjective`. The definition of submersiveness itself
is registered in `StacksCore.Topology.Defs.Induced`.

## References

* [Stacks Project, Tag 0406](https://stacks.math.columbia.edu/tag/0406)
-/

@[expose] public section

add_to_stacks 0406 Topology.IsStrictMap

add_to_stacks 0406 Topology.isQuotientMap_iff_isStrictMap_surjective
