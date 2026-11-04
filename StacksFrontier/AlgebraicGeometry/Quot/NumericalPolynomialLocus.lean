module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The locus of a prescribed Hilbert polynomial is open and closed

Let `T` be a topological space and let `χ : T → ℤ → ℤ` be a family of functions such that for
every `d` the function `t ↦ χ(t, d)` is locally constant, and for every `t` the function
`d ↦ χ(t, d)` is a polynomial of degree at most `n`. Then for every `P : ℤ → ℤ` the locus

`{t ∈ T | χ(t, d) = P(d) for all d ∈ ℤ}`

is open and closed, since a polynomial of degree at most `n` is determined by its values at
`0, …, n` (Example 0DNF, and Remark 0DP6 in the case `I = ℤ` and `E_i = 𝓛^{⊗ i}`).

## Main results

* `AlgebraicGeometry.polynomial_eq_of_natDegree_le_of_eval_range_eq`: two rational polynomials of
  degree at most `n` agreeing at `0, …, n` are equal.
* `AlgebraicGeometry.isClopen_setOf_forall_eq_of_isLocallyConstant`: the locus above is open and
  closed.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
-/

@[expose] public section

open Polynomial

namespace AlgebraicGeometry

/-- Two rational polynomials of degree at most `n` agreeing at `0, …, n` are equal. -/
theorem polynomial_eq_of_natDegree_le_of_eval_range_eq {n : ℕ} {Q₁ Q₂ : ℚ[X]}
    (h₁ : Q₁.natDegree ≤ n) (h₂ : Q₂.natDegree ≤ n)
    (h : ∀ i ∈ Finset.range (n + 1), Q₁.eval (i : ℚ) = Q₂.eval (i : ℚ)) : Q₁ = Q₂ := by
  let s : Finset ℚ := (Finset.range (n + 1)).map ⟨Nat.cast, Nat.cast_injective⟩
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq s ?_ ?_
  · have hle : (Q₁ - Q₂).natDegree ≤ n := (natDegree_sub_le _ _).trans (max_le h₁ h₂)
    rw [Finset.card_map, Finset.card_range]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hle)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hx
    exact h i hi

/-- **The locus of a prescribed Hilbert polynomial is open and closed.** If `t ↦ χ(t, d)` is
locally constant for every `d`, and `d ↦ χ(t, d)` agrees on the integers with a rational
polynomial of degree at most `n` for every `t`, then for every `P : ℤ → ℤ` the set of `t` with
`χ(t, d) = P(d)` for all integers `d` is open and closed. -/
theorem isClopen_setOf_forall_eq_of_isLocallyConstant {T : Type*} [TopologicalSpace T]
    (χ : T → ℤ → ℤ) (hχ : ∀ d, IsLocallyConstant fun t => χ t d) (n : ℕ)
    (hpoly : ∀ t, ∃ Q : ℚ[X], Q.natDegree ≤ n ∧ ∀ d : ℤ, (χ t d : ℚ) = Q.eval (d : ℚ))
    (P : ℤ → ℤ) :
    IsClopen {t | ∀ d, χ t d = P d} := by
  by_cases h : ∃ t₀, ∀ d, χ t₀ d = P d
  · obtain ⟨t₀, ht₀⟩ := h
    obtain ⟨Q₀, hQ₀, hχ₀⟩ := hpoly t₀
    have heq : {t | ∀ d, χ t d = P d} =
        ⋂ i ∈ Finset.range (n + 1), {t | χ t (i : ℤ) = P (i : ℤ)} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      refine ⟨fun ht i _ => ht i, fun ht d => ?_⟩
      obtain ⟨Q, hQ, hχt⟩ := hpoly t
      have hQQ : Q = Q₀ := polynomial_eq_of_natDegree_le_of_eval_range_eq hQ hQ₀ fun i hi => by
        have := hχt (i : ℤ)
        have h0 := hχ₀ (i : ℤ)
        push_cast at this h0
        rw [← this, ← h0, ht i hi, ht₀]
      have h1 := hχt d
      rw [hQQ, ← hχ₀ d] at h1
      exact (Int.cast_injective h1).trans (ht₀ d)
    rw [heq]
    exact isClopen_biInter_finset fun i _ => (hχ (i : ℤ)).isClopen_fiber _
  · rw [Set.eq_empty_iff_forall_notMem.2 fun t ht => h ⟨t, ht⟩]
    exact isClopen_empty

end AlgebraicGeometry
