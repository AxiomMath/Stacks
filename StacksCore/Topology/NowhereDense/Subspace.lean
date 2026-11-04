module

public import Mathlib.Topology.GDelta.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Nowhere dense subsets of subspaces

A nowhere dense subset of an open subspace has nowhere dense image in the ambient space.
Mathlib's `IsNowhereDense.image_val` is registered directly: it proves the stronger result
for any subspace, without assuming openness.

## References

* [Stacks Project, Tag 03J0](https://stacks.math.columbia.edu/tag/03J0)
-/

@[expose] public section

add_to_stacks 03J0 "nowhere dense subsets of a subspace" IsNowhereDense.image_val
