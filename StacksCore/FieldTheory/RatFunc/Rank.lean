module

public import Mathlib.FieldTheory.MvRatFunc.Rank
public import StacksCore.FieldTheory.MvRatFunc.Basic
import StacksCore.SetTheory.Cardinal.Basic

/-! # Dimension of rational functions -/

@[expose] public section

open Cardinal MvRatFunc

@[stacks 09G6]
theorem RatFunc.rank_eq_max (F : Type*) [Field F] : Module.rank F (RatFunc F) = #F ⊔ ℵ₀ := by
  rw [(ofRatFunc F).toLinearEquiv.rank_eq, rank_eq_max_lift]
  simp [one_le F]
