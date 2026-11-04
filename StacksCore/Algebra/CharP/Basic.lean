module

import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.Finiteness.Attr
import StacksCore.Tactic.StacksAttribute

/-! Characteristic of a ring -/

@[expose] public section

add_to_stacks 09FR "for the literal formulation of `ringChar R = 0`, use `ringChar.eq_zero`"
  CharP.charP_iff_prime_eq_zero
