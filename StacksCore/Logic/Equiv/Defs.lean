module

public import Mathlib.Logic.Equiv.Defs

/-! # Basic equivalences -/

@[expose] public section

/-- The fibre of the second projection `α × β → β` over `y : β` is in bijection with `α`. -/
@[simps] def equivSndEq (α : Type*) {β : Type*} (y : β) : α ≃ { p : α × β // p.2 = y } where
  toFun x := ⟨(x, y), rfl⟩
  invFun p := p.1.1
  left_inv := by grind
  right_inv := by grind
