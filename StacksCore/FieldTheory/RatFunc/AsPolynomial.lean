module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import StacksCore.Tactic.StacksAttribute

/-! # Rational function field — Stacks links -/

@[expose] public section

add_to_stacks 09G1 "transcendental case" RatFunc.algEquivOfTranscendental

namespace RatFunc

@[simp] theorem num_X_pow (F : Type*) [Field F] (n : ℕ) : (X ^ n).num (K := F) = .X ^ n := by
  rw [X, ← map_pow, num_algebraMap]

@[simp] theorem denom_X_pow (F : Type*) [Field F] (n : ℕ) : (X ^ n).denom (K := F) = 1 := by
  rw [X, ← map_pow, denom_algebraMap]

end RatFunc
