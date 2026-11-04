module

public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.PresheavesOfGroupsAndActions
import StacksCore.Tactic.StacksAttribute

/-!
# Torsors under a sheaf of groups

Let `G` be a sheaf of groups on a topological space. A torsor under `G` is a sheaf of sets `F`
with a `G`-action which is simply transitive on every open where `F` has a section and whose
stalks are all nonempty. A morphism of torsors is an equivariant morphism of the underlying
sheaves, and `G` acting on itself by left multiplication is the trivial torsor. These are the
three notions introduced in Tag 02FO; all three are already available on this branch, in
`StacksFrontier/Topology/Sheaves/Cohomology/Torsors/PresheavesOfGroupsAndActions.lean`
(Stacks Tag 02FP), so this file only records the tag for them.

## Main definitions

No new definitions are introduced.

## Main results

No new results are introduced.

## Implementation notes

The three declarations are formulated for the underlying presheaves; applying them to the
underlying presheaves of sheaves gives exactly the notions of the source. Nonemptiness of a
stalk is expressed by the equivalent existence of a section on some neighbourhood, which
avoids constructing the stalk.

## References

* [Stacks Project, Tag 02FO](https://stacks.math.columbia.edu/tag/02FO)
-/

@[expose] public section

add_to_stacks 02FO "the torsor condition on an action" Stacks.SpaceTorsor.Action.IsTorsor
add_to_stacks 02FO "an equivariant morphism of torsors" Stacks.SpaceTorsor.TorsorHom
add_to_stacks 02FO "the action defining the trivial torsor"
  Stacks.SpaceTorsor.PresheafOfGroups.trivialAction
