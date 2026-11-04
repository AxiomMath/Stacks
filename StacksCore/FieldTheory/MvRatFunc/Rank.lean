module

public import Mathlib.FieldTheory.MvRatFunc.Rank
public import StacksCore.FieldTheory.MvRatFunc.Basic

/-! # Dimension of `MvRatFunc` -/

@[expose] public section

open Cardinal

namespace MvRatFunc

@[stacks 0BU1]
theorem not_moduleFinite (F σ : Type*) [Field F] [Nonempty σ] :
    ¬Module.Finite F (MvRatFunc σ F) := by
  rw [← Module.rank_lt_aleph0_iff, rank_eq_max_lift]
  simp

end MvRatFunc
