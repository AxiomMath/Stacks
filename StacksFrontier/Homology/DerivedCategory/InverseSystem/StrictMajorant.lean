module

public import Mathlib.Order.Monotone.Basic

/-!
# A strictly monotone majorant of a sequence of naturals

Every `b : ℕ → ℕ` is dominated termwise by a strictly monotone sequence.
-/

@[expose] public section

namespace StacksDraft.InverseSystem

/-- Every sequence of naturals is dominated termwise by a strictly monotone one. -/
theorem exists_strict_majorant (b : ℕ → ℕ) :
    ∃ m : ℕ → ℕ, StrictMono m ∧ ∀ n, b n ≤ m n := by
  let m : ℕ → ℕ := Nat.rec (b 0) (fun n k => max (k + 1) (b (n + 1)))
  refine ⟨m, strictMono_nat_of_lt_succ fun n => (Nat.lt_succ_self _).trans_le (le_max_left _ _),
    fun n => ?_⟩
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

end StacksDraft.InverseSystem
