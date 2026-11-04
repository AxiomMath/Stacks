module

public import Mathlib.SetTheory.Cardinal.Basic

/-! # Basic properties of cardinals -/

@[expose] public section

namespace Cardinal

@[simp] theorem one_le_iff_nonempty (α : Type*) : 1 ≤ #α ↔ Nonempty α := by
  rw [← Cardinal.mk_ne_zero_iff, ← pos_iff_ne_zero, ← Order.succ_le_iff, Cardinal.succ_zero]

theorem one_le (α : Type*) [Nonempty α] : 1 ≤ #α := by simpa

end Cardinal
