module

public import Mathlib.CategoryTheory.Sites.Sieves.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Sieves

Stacks 00YX defines a *sieve* `S` on an object `U` of `C` to be a subpresheaf of `h_U`;
concretely, a collection of arrows with target `U` that is stable under precomposition, so that
`g ∈ S` implies `f ≫ g ∈ S`.

That is Mathlib's bundled `CategoryTheory.Sieve`, whose closure condition is the field
`CategoryTheory.Sieve.downward_closed`.
-/

@[expose] public section

-- The former @[stacks 00YX] declaration is now the Mathlib declarations.
add_to_stacks 00YX "a sieve on `U`, i.e. a subpresheaf of `h_U`" CategoryTheory.Sieve
add_to_sga "3 IV 4.1.1" "special case" CategoryTheory.Sieve
add_to_sga "4 I 4.1" CategoryTheory.Sieve
add_to_sga "4 I 4.3" CategoryTheory.Sieve
add_to_sga "4½ Arcata 1.1" CategoryTheory.Sieve
add_to_sga "4½ Arcata 1.3.4" "more general" CategoryTheory.Sieve
add_to_sga "4½ Arcata 1.4.3" CategoryTheory.Sieve
add_to_sga "4½ Arcata 1.6.1" CategoryTheory.Sieve
add_to_sga "3 IV 4.1.7" CategoryTheory.Sieve
add_to_stacks 00YX "the closure condition that makes a collection of arrows into `U` a sieve:
  stability under precomposition" CategoryTheory.Sieve.downward_closed
add_to_sga "3 IV 4.1.7" "downward closed" CategoryTheory.Sieve.downward_closed
