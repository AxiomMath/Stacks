module

public import Mathlib.FieldTheory.IsSepClosed
import StacksCore.FieldTheory.Separable
import StacksCore.Tactic.StacksAttribute

/-! # Separable closure -/

@[expose] public section

add_to_stacks 030M "First part of 1" separableClosure.isGalois
add_to_stacks 09H9 "Combine with 09HA, which is covered by `Field.finSepDegree_eq_finrank_iff` and
  `Field.finSepDegree_le_finrank`. Also use `Algebra.IsSeparable.trans` to transfer the separability
  conditions." IntermediateField.isSeparable_adjoin_iff_isSeparable
add_to_stacks 030L "1, Nat-valued version" Field.finSepDegree
add_to_stacks 030L "2, Nat-valued version" Field.finInsepDegree

open IntermediateField

/-- If `K/F` is separable, then the normal closure of `K` inside `L` is separable over `F`. -/
instance (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [Algebra.IsSeparable F K] : Algebra.IsSeparable F (normalClosure F K L) :=
  inferInstanceAs (Algebra.IsSeparable F (⨆ f : K →ₐ[F] L, f.fieldRange :))
