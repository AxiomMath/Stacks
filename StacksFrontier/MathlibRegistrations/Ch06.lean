module
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of Chapter 6 (Sheaves on Spaces) covered by Mathlib

Stacks tags of the Sheaves on Spaces chapter that Mathlib states, registered against the Mathlib
declarations with `add_to_stacks`.
-/

@[expose] public section

add_to_stacks 006U "F(∅) is a final object" TopCat.Sheaf.isTerminalOfEmpty
add_to_stacks 006U "disjoint opens: F(U ∪ V) = F(U) × F(V)" TopCat.Sheaf.isProductOfDisjoint
