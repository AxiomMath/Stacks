module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import StacksCore.Tactic.StacksAttribute

/-! # `ℂ` is finite dimensional over `ℝ` -/

@[expose] public section

add_to_stacks 09GD Complex.instFiniteDimensionalReal

open Cardinal IntermediateField

@[stacks 09G0]
theorem Complex.cardinalMk_of_adjoin_Rat_eq_top {s : Set ℂ} (hs : adjoin ℚ s = ⊤) : #s = 𝔠 := by
  rw [← mk_complex]
  refine le_antisymm (mk_set_le s) ?_
  have := cardinalMk_adjoin_le ℚ s
  rw [hs, ← SetLike.coe_sort_coe] at this
  simpa [not_le_of_gt aleph0_lt_continuum]
