module

public import Mathlib.CategoryTheory.CofilteredSystem
import StacksCore.Tactic.StacksAttribute

/-! # Cofiltered systems

Stacks 086J: a cofiltered limit of finite nonempty sets is nonempty. This is Mathlib's
`nonempty_sections_of_finite_cofiltered_system`, stated there for `F.sections`, which is
the limit of a `Type`-valued functor.
-/

public section

add_to_stacks 086J nonempty_sections_of_finite_cofiltered_system
