module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import StacksCore.Tactic.StacksAttribute

/-! Mathlib already states both definitions of Stacks tag 0B1Z. A topological group — a group
    endowed with a topology making multiplication and inversion continuous — is
    `IsTopologicalGroup`, and a homomorphism of topological groups — a continuous group
    homomorphism — is `ContinuousMonoidHom`. -/

@[expose] public section

add_to_stacks 0B1Z "a topological group" IsTopologicalGroup
add_to_stacks 0B1Z "a homomorphism of topological groups" ContinuousMonoidHom
