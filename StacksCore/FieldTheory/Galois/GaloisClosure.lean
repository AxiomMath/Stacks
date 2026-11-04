module

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import StacksCore.Tactic.StacksAttribute

/-! # Galois closure -/

@[expose] public section

add_to_stacks 0BU2 "1" FiniteGaloisIntermediateField.instLattice
add_to_stacks 0BU2 "2" FiniteGaloisIntermediateField.adjoin
add_to_stacks 0BU2 "3, 4" AlgEquiv.restrictNormalHom_surjective
