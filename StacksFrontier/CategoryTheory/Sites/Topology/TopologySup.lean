module

public import Mathlib.CategoryTheory.Sites.Sieves.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Pullbacks of sieves

Stacks 00Z2 defines the *pullback* of a sieve `S` on `U` along `f : V ⟶ U` to be the sieve
`S ×_U V` on `V` characterised by `(α : T ⟶ V) ∈ S ×_U V` if and only if `α ≫ f ∈ S`.

That is Mathlib's `CategoryTheory.Sieve.pullback`, whose defining rule is
`CategoryTheory.Sieve.pullback_apply`.
-/

@[expose] public section

-- The former @[stacks 00Z2] declaration is now the Mathlib declarations.
add_to_stacks 00Z2 "the pullback `S ×_U V` of a sieve `S` on `U` along `f : V ⟶ U`"
  CategoryTheory.Sieve.pullback
add_to_sga "4½ Arcata 1.6.1" "restriction U_V" CategoryTheory.Sieve.pullback
add_to_sga "4 I 4.3.1" "base change sieve" CategoryTheory.Sieve.pullback
add_to_stacks 00Z2 "the defining rule `α ∈ S ×_U V ↔ α ≫ f ∈ S` for the pullback of a sieve"
  CategoryTheory.Sieve.pullback_apply
add_to_sga "4½ Arcata 1.6.1" "restriction U_V" CategoryTheory.Sieve.pullback_apply
add_to_sga "4 I 4.3.1" "membership rule" CategoryTheory.Sieve.pullback_apply
