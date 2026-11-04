module

public import Mathlib.Data.Int.Cast.Lemmas

/-! # Cast lemmas for `ℤ` -/

@[expose] public section

/-- **Stacks 09FR** (for the literal formulation of `ringChar R = 0`, use `ringChar.eq_zero`).
A ring `R` has characteristic zero whenever the canonical map `ℤ → R` is injective; that is, the
condition `ℤ ⊂ R` from the Stacks definition of characteristic is equivalent to `CharZero R`. -/
@[stacks 09FR "for the literal formulation of `ringChar R = 0`, use `ringChar.eq_zero`"]
theorem CharZero.of_intCast_injective {R : Type*} [AddGroupWithOne R]
    (h : (Int.cast : ℤ → R).Injective) : CharZero R where
  cast_injective := by
    convert h.comp Nat.cast_injective
    ext; simp
