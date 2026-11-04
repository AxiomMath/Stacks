module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags covered by Mathlib: Chapter 25 (Hypercoverings)

The Stacks tags below are stated in Mathlib. This file registers the Mathlib declarations that
realize them with `add_to_stacks`; it contains no declarations of its own.
-/

add_to_stacks 01G0 "the objects of `SR(C)`: families `{U_i}_{i ∈ I}` of objects of `C`"
  CategoryTheory.Limits.FormalCoproduct

add_to_stacks 01G0 "the morphisms of `SR(C)`: a map `α : I → J` and morphisms `U_i → V_{α(i)}`"
  CategoryTheory.Limits.FormalCoproduct.Hom

add_to_stacks 01G0 "the category structure on `SR(C)`: identities and composition of such pairs"
  CategoryTheory.Limits.FormalCoproduct.category

add_to_stacks 0DB0 "the induced map ∐ U_i ⟶ ∐ V_j from α : I → J and f_i : U_i ⟶ V_{α i}"
  CategoryTheory.Limits.Sigma.map'
add_to_stacks 0DB0 "it sends the summand U_i into V_{α i} via f_i"
  CategoryTheory.Limits.Sigma.ι_comp_map'

add_to_stacks 01G1 "the functor `F : SR(C) → PSh(C)`, `{U_i}_{i ∈ I} ↦ ∐ h_{U_i}`"
  CategoryTheory.Limits.FormalCoproduct.yoneda
