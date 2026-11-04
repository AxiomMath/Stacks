module

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import StacksCore.Tactic.StacksAttribute

/-! # Rational functions -/

@[expose] public section

add_to_stacks 09FK RatFunc.instIsFractionRingPolynomial
