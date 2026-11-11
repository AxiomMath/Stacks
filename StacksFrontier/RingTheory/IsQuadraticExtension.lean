module

public import StacksCore.RingTheory.IsQuadraticExtension

/-! # Classification of quadratic field extensions

This file states the classification of degree two field extensions `L/K` (Stacks 0BIN):
exactly one of the following happens.
1. `discr' K L = 0`, the characteristic of `K` is `2`, and `L/K` is purely inseparable, obtained
   by adjoining a square root of a non-square `a ∈ K`;
2. `discr' K L = 1`, the characteristic of `K` is `2`, and `L/K` is separable;
3. the discriminant is the class of a non-square `a ∈ K`, the characteristic of `K` is not `2`,
   and `L ≅ K[√a]`, i.e. `L` is obtained by adjoining a square root of the discriminant.
-/

@[expose] public section

open Module QuadraticAlgebra

namespace Algebra.IsQuadraticExtension

/-- A quadratic field extension `L/K` over a field with `2 ≠ 0` is `K`-isomorphic to `K[√a]`
for a non-square `a ∈ K` whose class in `K/(K^*)^2` is the discriminant `discr' K L`. -/
theorem exists_mk_eq_discr'_of_two_ne_zero (K L : Type*) [Field K] [Field L] [Algebra K L]
    [NeZero (2 : K)] [IsQuadraticExtension K L] :
    ∃ a : K, QuotSq.mk K a = discr' K L ∧ ¬IsSquare a ∧
      Nonempty (L ≃ₐ[K] QuadraticAlgebra K a 0) := by
  obtain ⟨-, -, -, a, ha, ⟨e⟩⟩ := of_field_two_ne_zero K L
  refine ⟨a, ?_, ha, ⟨e⟩⟩
  rw [e.discr'_eq, discr'_eq, show (0 : K) ^ 2 + 4 * a = (.mk0 2 (NeZero.ne 2) : Kˣ) ^ 2 * a by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, Units.val_mk0,
      mul_eq_mul_right_iff]
    grind, map_mul, map_pow, QuotSq.mk_unit_sq, one_mul]

/-- **Stacks 0BIN**. Let `L/K` be an extension of fields of degree `2`. Then exactly one of the
following happens:
1. the discriminant is `0`, the characteristic of `K` is `2`, and `L/K` is purely inseparable,
   obtained by taking a square root of a non-square `a ∈ K`;
2. the discriminant is `1`, the characteristic of `K` is `2`, and `L/K` is separable (of the form
   `K[X]/(X^2 + X - a)` with `a` not of the form `x(x+1)`);
3. the discriminant is the class of a non-square `a ∈ K`, the characteristic of `K` is not `2`,
   and `L ≅ K[√a]` is obtained by taking a square root of the discriminant. -/
@[stacks 0BIN "complete classification: the three cases hold in every characteristic and
exclude one another, case (3) with `L ≅ K[√a]` for `a` representing the discriminant"]
theorem classification (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsQuadraticExtension K L] :
    let P₁ := discr' K L = 0 ∧ ringChar K = 2 ∧ IsPurelyInseparable K L ∧
      ∃ a : K, ¬IsSquare a ∧ Nonempty (L ≃ₐ[K] QuadraticAlgebra K a 0)
    let P₂ := discr' K L = 1 ∧ ringChar K = 2 ∧ Algebra.IsSeparable K L ∧
      ∃ a : K, (∀ x : K, x * (x + 1) ≠ a) ∧ Nonempty (L ≃ₐ[K] QuadraticAlgebra K a 1)
    let P₃ := ringChar K ≠ 2 ∧ Algebra.IsSeparable K L ∧
      ∃ a : K, QuotSq.mk K a = discr' K L ∧ ¬IsSquare a ∧
        Nonempty (L ≃ₐ[K] QuadraticAlgebra K a 0)
    (P₁ ∨ P₂ ∨ P₃) ∧ ¬(P₁ ∧ P₂) ∧ ¬(P₁ ∧ P₃) ∧ ¬(P₂ ∧ P₃) := by
  intro P₁ P₂ P₃
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ ?_, fun ⟨h₁, h₃⟩ ↦ h₃.1 h₁.2.1, fun ⟨h₂, h₃⟩ ↦ h₃.1 h₂.2.1⟩
  · by_cases hK : ringChar K = 2
    · have : CharP K 2 := ringChar.of_eq hK
      rcases of_field_char_two K L with h | h
      · exact .inl ⟨h.1, hK, h.2⟩
      · exact .inr (.inl ⟨h.1, hK, h.2⟩)
    · have : NeZero (2 : K) := ⟨Ring.two_ne_zero hK⟩
      exact .inr (.inr ⟨hK, (of_field_two_ne_zero K L).2.2.1,
        exists_mk_eq_discr'_of_two_ne_zero K L⟩)
  · have h01 : (0 : QuotSq K) = 1 := h₁.1.symm.trans h₂.1
    rw [← (QuotSq.mk K).map_one, eq_comm, QuotSq.mk_eq_zero] at h01
    exact one_ne_zero h01

end Algebra.IsQuadraticExtension
