module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# A weighted degree bound for the resultant

For `Ψ, g ∈ R[X][Y]`, give `Y` the weight `w`. If every monomial of `Ψ` has weighted degree at most
`w · deg_Y Ψ` and every monomial of `g` has weighted degree at most `n`, then the resultant
`Res_Y(Ψ, g) ∈ R[X]` has degree at most `deg_Y Ψ · n`. The proof bounds the degree of each entry of
the Sylvester matrix by a row weight plus a column weight, and the determinant by their sums.

## Main results

* `Polynomial.natDegree_det_le_of_natDegree_le_add`: if the entries of a matrix of polynomials
  satisfy `deg M i j ≤ a i + b j`, the determinant has degree at most `∑ a + ∑ b`.
* `Polynomial.natDegree_resultant_le_of_weightedDegree_le`: the weighted degree bound.
-/

@[expose] public section

open Polynomial


namespace Polynomial

/-- If every nonzero entry `M i j` of a square matrix of polynomials has degree at most
`a i + b j`, then the determinant has degree at most `∑ i, a i + ∑ j, b j`. -/
theorem natDegree_det_le_of_natDegree_le_add {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R[X]) (a b : ι → ℤ)
    (hM : ∀ i j, M i j ≠ 0 → ((M i j).natDegree : ℤ) ≤ a i + b j) :
    M.det.natDegree ≤ (∑ i, a i + ∑ j, b j).toNat := by
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => (natDegree_smul_le _ _).trans ?_
  by_cases h0 : ∃ i, M (σ i) i = 0
  · obtain ⟨i, hi⟩ := h0
    have h : ∏ i, M (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [h, natDegree_zero]
    exact Nat.zero_le _
  push Not at h0
  refine (natDegree_prod_le _ _).trans ?_
  have hsum : ((∑ i, (M (σ i) i).natDegree : ℕ) : ℤ) ≤ ∑ i, a i + ∑ j, b j := by
    push_cast
    calc ∑ i, ((M (σ i) i).natDegree : ℤ) ≤ ∑ i, (a (σ i) + b i) :=
          Finset.sum_le_sum fun i _ => hM _ _ (h0 i)
      _ = ∑ i, a i + ∑ j, b j := by
          rw [Finset.sum_add_distrib, Equiv.sum_comp σ a]
  omega

end Polynomial

namespace Polynomial

/-- **Weighted degree bound for the resultant.** Let `Ψ, g ∈ R[X][Y]`. If the coefficient of `Yⁱ`
in `Ψ` has `X`-degree at most `w (deg_Y Ψ - i)` and that of `Yʲ` in `g` has `X`-degree at most
`n - w j`, then `Res_Y(Ψ, g)` has `X`-degree at most `deg_Y Ψ * n`. -/
theorem natDegree_resultant_le_of_weightedDegree_le {R : Type*} [CommRing R] {Ψ g : R[X][X]}
    {w n : ℕ}
    (hΨw : ∀ i, Ψ.coeff i ≠ 0 → (Ψ.coeff i).natDegree + w * i ≤ w * Ψ.natDegree)
    (hgw : ∀ j, g.coeff j ≠ 0 → (g.coeff j).natDegree + w * j ≤ n) :
    (resultant Ψ g).natDegree ≤ Ψ.natDegree * n := by
  classical
  set m := Ψ.natDegree
  set k := g.natDegree
  let a : Fin (m + k) → ℤ := fun i => -((w : ℤ) * (i : ℕ))
  let b : Fin (m + k) → ℤ := fun j => j.addCases (fun j₁ => (n : ℤ) + w * (j₁ : ℕ))
    (fun j₁ => (w : ℤ) * m + w * (j₁ : ℕ))
  have hbound := natDegree_det_le_of_natDegree_le_add (sylvester Ψ g m k) a b ?_
  · refine hbound.trans (le_of_eq ?_)
    have hsum : ∑ i, a i + ∑ j, b j = ((m * n : ℕ) : ℤ) := by
      simp [a, b, Fin.sum_univ_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    rw [hsum]; exact Int.toNat_natCast _
  · have key : ∀ (p : R[X][X]) (c d : ℕ), (∀ j, p.coeff j ≠ 0 → (p.coeff j).natDegree + w * j ≤ c) →
        ∀ i j : ℕ, (if i ∈ Set.Icc j (j + d) then p.coeff (i - j) else 0) ≠ 0 →
          ((if i ∈ Set.Icc j (j + d) then p.coeff (i - j) else 0).natDegree : ℤ) ≤
            -(w * i) + (c + w * j) := by
      intro p c d hp i j hij
      split_ifs at hij ⊢ with hi
      · have h' := hp _ hij
        zify [hi.1] at h'
        linarith
      · exact absurd rfl hij
    intro i j hij
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left, b, a] at hij ⊢
      exact key g n k hgw _ _ hij
    | right j₁ =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right, b, a] at hij ⊢
      exact key Ψ (w * m) m hΨw _ _ hij

end Polynomial
