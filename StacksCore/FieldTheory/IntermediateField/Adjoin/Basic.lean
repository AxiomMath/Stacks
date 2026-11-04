module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Adjoining elements to a field extension -/

@[expose] public section

add_to_stacks 09GG "2, forward part" IntermediateField.adjoin.finiteDimensional

open IntermediateField

/-- The degree `[K⟮x⟯ : K]` equals the degree of the minimal polynomial of `x` over `K`, with
both sides equal to zero when `x` is not integral over `K`. Generalization of
`IntermediateField.adjoin.finrank`, which assumes `IsIntegral K x`. -/
theorem IntermediateField.finrank_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) : Module.finrank K K⟮x⟯ = (minpoly K x).natDegree := by
  by_cases hx : IsIntegral K x
  · exact adjoin.finrank hx
  have hf : ¬ Module.Finite K K⟮x⟯ := fun _ ↦ by
    let y : K⟮x⟯ := ⟨x, subset_adjoin _ _ <| by simp⟩
    exact hx <| (Algebra.IsIntegral.isIntegral (R := K) y).map K⟮x⟯.val
  rw [Module.finrank_of_not_finite hf, minpoly.eq_zero hx, Polynomial.natDegree_zero]
