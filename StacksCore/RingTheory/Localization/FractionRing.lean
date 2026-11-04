module

import Mathlib.Data.Finset.Attr
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.SetLike
import StacksCore.Tactic.StacksAttribute

/-! Fraction rings -/

@[expose] public section

add_to_stacks 09FJ FractionRing
add_to_stacks 09FJ "uniqueness is given by IsLocalization.ringHom_ext" IsFractionRing.lift
add_to_stacks 02C5 "3" FractionRing
add_to_stacks 02C5 "4" FractionRing.field
