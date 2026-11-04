module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks tags of chapter 22 (Differential Graded Algebra) covered by Mathlib

Each tag registered here is stated in Mathlib; this file only records the correspondence.

Mathlib splits an `R`-linear structure into an additive part and a scalar part: an `R`-linear
category is a `Preadditive` category with `Linear R`, and an `R`-linear functor is a functor with
`Functor.Additive` and `Functor.Linear R`.
-/

add_to_stacks 09MJ "abelian group structure on Hom sets, composition biadditive"
  CategoryTheory.Preadditive
add_to_stacks 09MJ "R-module structure on Hom sets, composition compatible with scalars"
  CategoryTheory.Linear

add_to_stacks 09MK "F additive on Hom groups" CategoryTheory.Functor.Additive
add_to_stacks 09MK "F compatible with scalars on Hom modules" CategoryTheory.Functor.Linear
