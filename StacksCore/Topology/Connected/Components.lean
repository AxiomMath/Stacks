module

public import Mathlib.Topology.Connected.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Connected components

Every part of Stacks 004T is Mathlib's, over the construction `connectedComponent x`: the connected
component of `X` containing the point `x`. The tag is recorded against the upstream declarations
here. Mathlib takes a connected component to be a value of `connectedComponent` rather than a
subset satisfying a predicate, which is what makes parts (3) and (4) — "contained in a unique
connected component" — the lemmas pinning down `connectedComponent x`.

## Main results

* (1) the closure of a connected subset is connected: `IsConnected.closure`.
* (2) a connected component is closed: `isClosed_connectedComponent`.
* (3) a connected subset `T` lies in a unique connected component:
  `IsConnected.subset_connectedComponent` puts `T` inside `connectedComponent x` for any `x ∈ T`,
  and `connectedComponent_eq` identifies any component meeting `T` with that one.
* (4) a point lies in a unique connected component, equivalently `X` is the disjoint union of its
  connected components: `mem_connectedComponent`, `connectedComponent_eq` and
  `connectedComponent_disjoint`.

## References

* [Stacks Project, Tag 004T](https://stacks.math.columbia.edu/tag/004T)
-/

@[expose] public section

add_to_stacks 004T "(1)" IsConnected.closure
add_to_stacks 004T "(2)" isClosed_connectedComponent
add_to_stacks 004T "(3)" IsConnected.subset_connectedComponent
add_to_stacks 004T "(3), (4): uniqueness" connectedComponent_eq
add_to_stacks 004T "(4)" mem_connectedComponent
add_to_stacks 004T "(4): disjointness" connectedComponent_disjoint
