module

public import Mathlib.CategoryTheory.Functor.Category
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of chapter 96 (Sheaves on Algebraic Stacks) covered by Mathlib

Each tag registered here is stated in Mathlib; this file only records the correspondence.

A presheaf on a category fibred in groupoids `X` is a presheaf on its underlying category, that
is, an object of the functor category `Xᵒᵖ ⥤ Type`, whose morphisms are natural transformations.
-/

add_to_stacks 06TJ "(1), (2) and PSh(X): presheaves on the underlying category of X, the functor \
  category Xᵒᵖ ⥤ Type (morphisms are natural transformations)"
  CategoryTheory.Functor.category
