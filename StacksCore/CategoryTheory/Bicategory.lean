module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import StacksCore.Tactic.StacksAttribute

/-! # Bicategories
This file adds stacks tags to various mathlib declarations around bicategories.
-/

@[expose] public section

open CategoryTheory

add_to_stacks 003H Bicategory.Strict

add_to_stacks 003L "An adjoint equivalence in a bicategory, denoted `X ≌ Y`." Bicategory.Equivalence
add_to_stacks 003L "A constructor for adjoint equivalences from the data of plain equivalences."
  Bicategory.Equivalence.mkOfAdjointifyCounit

add_to_stacks 003N "Pseudofunctors between bicategories." Pseudofunctor
add_to_stacks 003N "The instance giving every strict bicategory the structure of a category.
  A functor from a category to a bicategory in the sense of this stacks tag is simply a functor
  with respect to this instance." StrictBicategory.category
add_to_stacks 003N "Type synonym for the locally discrete 2-category corresponding to a category.
  A pseudofunctor from a category to a bicategory in the sense of this stacks tag is simply
  a pseudofunctor out of this type synonym." LocallyDiscrete
add_to_stacks 003N "A constructor for pseudofunctors out of a 1-category."
  LocallyDiscrete.mkPseudofunctor
