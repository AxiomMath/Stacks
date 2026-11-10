module
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Dehomogenization

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.Polynomial.Vieta
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveProjectiveSmoothPoint

/-!
# A homogeneous polynomial does not vanish at the coefficients of a generic split polynomial

Let `R` be a domain and let `r₀, …, rₙ` be indeterminates. The coefficients `c₀, …, c_{n+1}` of
the split polynomial `∏ᵢ (T + rᵢ)` are, up to order, the elementary symmetric polynomials in the
`rᵢ`, with `c_{n+1} = 1`. This file proves that **a nonzero homogeneous polynomial
`F(Z₀, …, Z_{n+1})` does not vanish at `(c₀, …, c_{n+1})`**: dehomogenizing at the last variable
loses nothing for a homogeneous `F` (`Stacks.Curves.dehomCoeff_ne_zero`), and the
elementary symmetric polynomials are algebraically independent (the fundamental theorem of
symmetric polynomials, `MvPolynomial.esymmAlgHom_fin_injective`).

Geometrically: the point `(c₀ : ⋯ : c_{n+1})` of `ℙⁿ⁺¹` over `R[r₀, …, rₙ]` is the image of the
point `((r₀ : 1), …, (rₙ : 1))` of `(ℙ¹)ⁿ⁺¹` under the morphism multiplying binary forms, and the
statement says that this point lies in every nonempty standard open `D₊(F)`, i.e. that the
multiplication morphism is dominant.

## Main results

* `Stacks.ProjectiveChart.coeff_prod_X_add_C_X`: the `k`-th coefficient of `∏ᵢ (T + rᵢ)` is the
  elementary symmetric polynomial of degree `n + 1 - k`.
* `Stacks.ProjectiveChart.aeval_coeff_prod_X_add_C_ne_zero`: **a nonzero homogeneous polynomial
  does not vanish at the coefficients of `∏ᵢ (T + rᵢ)`.**
-/

@[expose] public section

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveChart

variable {R : Type u} [CommRing R]

/-- **Vieta's formula over the polynomial ring in the roots.** The `k`-th coefficient of
`∏ᵢ (T + rᵢ)`, the product running over `n + 1` indeterminates, is the elementary symmetric
polynomial of degree `n + 1 - k`. -/
theorem coeff_prod_X_add_C_X (n : ℕ) {k : ℕ} (hk : k ≤ n + 1) :
    (∏ i : Fin (n + 1), (Polynomial.X + Polynomial.C (X i : MvPolynomial (Fin (n + 1)) R))).coeff
        k = esymm (Fin (n + 1)) R (n + 1 - k) := by
  have hcard : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_X_add_C_coeff _ _ (hcard.symm ▸ hk), hcard]
  rfl

/-- The leading coefficient: `∏ᵢ (T + rᵢ)` is monic of degree `n + 1`. -/
theorem coeff_prod_X_add_C_X_self (n : ℕ) :
    (∏ i : Fin (n + 1), (Polynomial.X + Polynomial.C (X i : MvPolynomial (Fin (n + 1)) R))).coeff
        (n + 1) = 1 := by
  rw [coeff_prod_X_add_C_X n le_rfl, Nat.sub_self, esymm_zero]

/-- **A nonzero homogeneous polynomial does not vanish at the coefficients of a generic split
polynomial.** For `F ∈ R[Z₀, …, Z_{n+1}]` homogeneous and nonzero over a domain, evaluating `Zₖ`
at the `k`-th coefficient of `∏ᵢ (T + rᵢ)` gives a nonzero element of `R[r₀, …, rₙ]`. -/
theorem aeval_coeff_prod_X_add_C_ne_zero [IsDomain R] {n d : ℕ}
    {F : MvPolynomial (Fin (n + 2)) R}
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 2)) R d) (hF0 : F ≠ 0) :
    aeval (fun k : Fin (n + 2) =>
      (∏ i : Fin (n + 1),
        (Polynomial.X + Polynomial.C (X i : MvPolynomial (Fin (n + 1)) R))).coeff k) F ≠ 0 := by
  set c : Fin (n + 2) → MvPolynomial (Fin (n + 1)) R := fun k =>
    (∏ i : Fin (n + 1),
      (Polynomial.X + Polynomial.C (X i : MvPolynomial (Fin (n + 1)) R))).coeff k with hc
  have hG := Stacks.Curves.dehomCoeff_ne_zero (Fin.last (n + 1)) F (by simpa using hF) hF0
  -- evaluating `F` is evaluating its dehomogenization, because `c (last) = 1`
  have hdehom : aeval c F = aeval (c ∘ Fin.castSucc) (dehomCoeff R (Fin.last (n + 1)) F) := by
    rw [dehomCoeff_eq_aeval]
    have hcomp := congrArg (fun φ : MvPolynomial (Fin (n + 2)) R →ₐ[R]
        MvPolynomial (Fin (n + 1)) R => φ F)
      (MvPolynomial.comp_aeval (R := R)
        (fun k => (finSuccEquiv' (Fin.last (n + 1)) k).elim 1 X)
        (aeval (c ∘ Fin.castSucc)))
    simp only [AlgHom.comp_apply] at hcomp
    rw [hcomp]
    congr 2
    funext k
    induction k using Fin.lastCases with
    | last =>
        rw [finSuccEquiv'_at, Option.elim_none, map_one]
        simp only [hc, Fin.val_last]
        exact coeff_prod_X_add_C_X_self n
    | cast j =>
        simp [finSuccEquiv'_last_apply_castSucc]
  -- the dehomogenized values are the elementary symmetric polynomials, in reverse order
  have hrev : c ∘ Fin.castSucc =
      (fun i : Fin (n + 1) => esymm (Fin (n + 1)) R ((i : ℕ) + 1)) ∘ Fin.rev := by
    funext j
    simp only [Function.comp_apply, hc, Fin.val_castSucc, Fin.val_rev]
    rw [coeff_prod_X_add_C_X n (by omega)]
    congr 1
    omega
  rw [hdehom, hrev, ← aeval_rename, ← esymmAlgHom_apply]
  intro h0
  have h1 : esymmAlgHom (Fin (n + 1)) R (n + 1)
      (rename Fin.rev (dehomCoeff R (Fin.last (n + 1)) F)) = 0 :=
    Subtype.ext h0
  rw [← map_zero (esymmAlgHom (Fin (n + 1)) R (n + 1))] at h1
  have h2 := esymmAlgHom_fin_injective R le_rfl h1
  rw [← map_zero (rename (R := R) (Fin.rev : Fin (n + 1) → Fin (n + 1)))] at h2
  exact hG (rename_injective _ Fin.rev_injective h2)

end Stacks.ProjectiveChart

end
