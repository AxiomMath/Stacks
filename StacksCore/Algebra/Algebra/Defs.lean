module

public import Mathlib.Algebra.Algebra.Defs
import StacksCore.Tactic.StacksAttribute

/-! Tag the Mathlib `Algebra` typeclass as the formalisation of Stacks 09FV. -/

@[expose] public section

add_to_stacks 09FV Algebra
