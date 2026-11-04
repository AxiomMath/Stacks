module

public import Mathlib.CategoryTheory.Sites.Sieves.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Sieves are stable under precomposition

Stacks 00YY is the defining stability property of a sieve: if the arrow `α : T ⟶ U` lies in a
sieve `S` on `U` and `g : T' ⟶ T` is any arrow, then `g ≫ α : T' ⟶ U` lies in `S`.

That is Mathlib's `CategoryTheory.Sieve.downward_closed`.
-/

@[expose] public section

-- The former @[stacks 00YY] declaration is now the Mathlib field.
add_to_stacks 00YY "a sieve on `U` is stable under precomposition"
  CategoryTheory.Sieve.downward_closed
