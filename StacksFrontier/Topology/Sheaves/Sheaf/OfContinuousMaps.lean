module

public import Mathlib.Topology.Sheaves.LocalPredicate

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 006V — Continuous maps into a fixed space form a sheaf

Stacks 006V is the basic example: for topological spaces `X` and `Y`, the rule assigning to an
open `U ⊆ X` the set of continuous maps `U → Y`, with restriction along inclusions of opens, is
a sheaf. Continuous maps agreeing on the overlaps of an open covering glue to a map on the
union, and that map is continuous because continuity is local.

Mathlib states all of this: the presheaf is `TopCat.presheafToTop`, the same presheaf together
with the sheaf condition is `TopCat.sheafToTop`, and the gluing of a compatible family of
continuous maps over an open covering is `ContinuousMap.liftCover`.
-/

@[expose] public section

-- The former @[stacks 006V] theorem is the sheaf condition carried by `TopCat.sheafToTop`.
add_to_stacks 006V "the presheaf `U ↦ {f : U → Y | f continuous}` on `X`" TopCat.presheafToTop
add_to_sga "6 II AppII.3.0.1" "presheaf U ↦ C(U,Y)" TopCat.presheafToTop
add_to_stacks 006V "that presheaf is a sheaf" TopCat.sheafToTop
add_to_sga "4½ Arcata 1.2.3" "more general" TopCat.sheafToTop
add_to_sga "5 VII 3.8" "partial" TopCat.sheafToTop
add_to_sga "6 II AppII.3.0.1" TopCat.sheafToTop
add_to_stacks 006V "the gluing of a compatible family of continuous maps over an open covering"
  ContinuousMap.liftCover
add_to_sga "4½ Arcata 1.2.3" "partial" ContinuousMap.liftCover
