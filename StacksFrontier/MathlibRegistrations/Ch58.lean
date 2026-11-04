module

public import Mathlib.CategoryTheory.Galois.Action
public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.CategoryTheory.Galois.Topology
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib registrations for Stacks Chapter 58 (Fundamental Groups of Schemes)

Tags of this chapter whose statements are already in Mathlib, registered on the Mathlib
declarations that state them. Where a tag is covered by several declarations, each registration
names the part it gives.
-/

@[expose] public section

add_to_stacks 0BMW "the functor `X ↦ F(X)` to finite `Aut(F)`-sets"
  CategoryTheory.PreGaloisCategory.functorToAction
add_to_stacks 0BMW "the topology on `Aut(F)`"
  CategoryTheory.PreGaloisCategory.instTopologicalSpaceAutFunctorFintypeCat
add_to_stacks 0BMW "`Aut(F)` is a topological group"
  CategoryTheory.PreGaloisCategory.instIsTopologicalGroupAutFunctorFintypeCat
add_to_stacks 0BMW "`Aut(F)` is compact"
  CategoryTheory.PreGaloisCategory.instCompactSpaceAutFunctorFintypeCat
add_to_stacks 0BMW "`Aut(F)` is Hausdorff"
  CategoryTheory.PreGaloisCategory.instT2SpaceAutFunctorFintypeCat
add_to_stacks 0BMW "`Aut(F)` is totally disconnected"
  CategoryTheory.PreGaloisCategory.instTotallyDisconnectedSpaceAutFunctorFintypeCat
add_to_stacks 0BMW "the action of `Aut(F)` on `F(X)` is continuous"
  CategoryTheory.PreGaloisCategory.continuousSMul_aut_fiber

add_to_stacks 0BN2 CategoryTheory.PreGaloisCategory.exists_hom_from_galois_of_connected
