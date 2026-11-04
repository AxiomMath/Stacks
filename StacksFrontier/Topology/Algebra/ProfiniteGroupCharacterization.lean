module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import StacksCore.Tactic.StacksAttribute

/-! Mathlib already states Stacks tag 0BR2, the definition of a profinite group, as
    `ProfiniteGrp`: a group with a topology making it a topological group whose underlying space is
    profinite, i.e. compact, Hausdorff and totally disconnected. `ProfiniteGrp.of` builds one from
    exactly those hypotheses on a topological group.

    The equivalent conditions of Stacks 0BR1 that the definition refers to are stated in
    `StacksFrontier.Topology.Algebra.ProfiniteGroup`. -/

@[expose] public section

add_to_stacks 0BR2 "a profinite group" ProfiniteGrp
add_to_sga "1 V 5.1" ProfiniteGrp
add_to_sga "4 IV 2.7.2" ProfiniteGrp
add_to_stacks 0BR2 "the profinite group attached to a compact, Hausdorff, totally disconnected
  topological group" ProfiniteGrp.of
