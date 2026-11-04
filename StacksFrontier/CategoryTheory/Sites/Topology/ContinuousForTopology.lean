module

public import Mathlib.CategoryTheory.Sites.Closed

import StacksCore.Tactic.StacksAttribute

/-!
# A topology is determined by its sheaves

Stacks 00ZP says that two Grothendieck topologies `J₁`, `J₂` on a category `C` are equal if and
only if a presheaf of sets is a `J₁`-sheaf exactly when it is a `J₂`-sheaf.

That equivalence is Mathlib's `CategoryTheory.topology_eq_iff_same_sheaves`.
-/

@[expose] public section

-- The former @[stacks 00ZP] declaration is now the Mathlib theorem.
add_to_stacks 00ZP "two topologies are equal exactly when they have the same `Type`-valued
  sheaves" CategoryTheory.topology_eq_iff_same_sheaves
add_to_sga "4 IV 9.1.2" "9.1.2 c)" CategoryTheory.topology_eq_iff_same_sheaves
