module

public import Mathlib.CategoryTheory.Sites.Sieves.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of a sieve along one of its own members

Stacks 00Z3 says that if `f : V ⟶ U` lies in a sieve `S` on `U`, then the base change
`S ×_U V = S.pullback f` is the maximal sieve `h_V = ⊤` on `V`.

That is Mathlib's `CategoryTheory.Sieve.pullback_eq_top_of_mem`.
-/

@[expose] public section

-- The former @[stacks 00Z3] declaration is now the Mathlib theorem.
add_to_stacks 00Z3 "pulling a sieve back along one of its own members gives the maximal sieve"
  CategoryTheory.Sieve.pullback_eq_top_of_mem
