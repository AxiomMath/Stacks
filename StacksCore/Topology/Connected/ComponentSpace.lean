module

public import Mathlib.Topology.Connected.TotallyDisconnected
import StacksCore.Tactic.StacksAttribute

/-!
# The space of connected components

The space `π₀(X) = ConnectedComponents X` is totally disconnected. Every continuous map from
`X` to a totally disconnected space factors continuously through `π₀(X)`.

Both parts are registered directly from Mathlib, together with the continuity and
factorization identities for `Continuous.connectedComponentsLift`.

## References

* [Stacks Project, Tag 08ZL](https://stacks.math.columbia.edu/tag/08ZL)
-/

@[expose] public section

add_to_stacks 08ZL "π₀(X) is totally disconnected" ConnectedComponents.totallyDisconnectedSpace
add_to_stacks 08ZL "factorization: the induced map on π₀(X)" Continuous.connectedComponentsLift
add_to_stacks 08ZL "factorization: the induced map is continuous"
  Continuous.connectedComponentsLift_continuous
add_to_stacks 08ZL "factorization: the induced map lifts the original one"
  Continuous.connectedComponentsLift_comp_coe
