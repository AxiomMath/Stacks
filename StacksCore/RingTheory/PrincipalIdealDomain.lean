module

import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import StacksCore.Tactic.StacksAttribute

/-! Principal ideal domains -/

@[expose] public section

add_to_stacks 09FI "first part" PrincipalIdealRing.isMaximal_of_irreducible
