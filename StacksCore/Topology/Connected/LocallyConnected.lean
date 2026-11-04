module

public import Mathlib.Topology.Connected.LocallyConnected
import StacksCore.Tactic.StacksAttribute

/-!
# Locally connected spaces

Stacks 04ME: if `X` is locally connected then (1) every open subset of `X` is locally connected
and (2) the connected components of `X` are open; so also the connected components of an open
subset are open, and in particular every point has a fundamental system of open connected
neighbourhoods.

Every clause is a Mathlib theorem. The "so also" clause is (2) applied to the open subspace
supplied by (1), and the "in particular" clause is the defining field of
`LocallyConnectedSpace`.

## References

* [Stacks Project, Tag 04MD](https://stacks.math.columbia.edu/tag/04MD)
* [Stacks Project, Tag 04ME](https://stacks.math.columbia.edu/tag/04ME)
-/

@[expose] public section

add_to_stacks 04MD LocallyConnectedSpace

add_to_stacks 04ME "(1) an open subset of a locally connected space is locally connected"
  IsOpen.locallyConnectedSpace
add_to_stacks 04ME "(2) the connected components are open" isOpen_connectedComponent
add_to_stacks 04ME "in particular, a fundamental system of open connected neighbourhoods"
  LocallyConnectedSpace.open_connected_basis
