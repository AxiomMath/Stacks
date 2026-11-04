module

public import Mathlib.Algebra.Homology.ExactSequence

/-! # Exact sequences: mirror lemmas

Small additions to Mathlib's `ComposableArrows` exactness API used by the filtration development
(Stacks 0127): a three-term sequence is exact iff its two short complexes are.
-/

@[expose] public section

namespace CategoryTheory.ComposableArrows

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- A three-term sequence `X₀ → X₁ → X₂ → X₃` is exact iff both two-term windows are. -/
lemma exact_mk₃_iff {X₀ X₁ X₂ X₃ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (w₁ : a ≫ b = 0) (w₂ : b ≫ c = 0) :
    (mk₃ a b c).Exact ↔ (ShortComplex.mk a b w₁).Exact ∧ (ShortComplex.mk b c w₂).Exact := by
  rw [exact_iff_δ₀, ShortComplex.exact_iff_exact_toComposableArrows,
    ShortComplex.exact_iff_exact_toComposableArrows]
  -- `Precomp.map` reduces on the `Fin` literals; fall back to `exact₂_iff` + `simp [Precomp.map]`
  -- if a Mathlib bump changes that.
  exact Iff.rfl

end CategoryTheory.ComposableArrows
