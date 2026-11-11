module

public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The chain rule for partial derivatives of a substitution

Let `F ∈ R[X_i : i ∈ σ]` with `σ` finite and let `g : σ → R[Y_a : a ∈ τ]`. Substituting `g` into
`F` and differentiating with respect to `Y_a` obeys the chain rule

`∂/∂Y_a (F(g)) = ∑ᵢ (∂F/∂Xᵢ)(g) · ∂gᵢ/∂Y_a`.

## Main results

* `MvPolynomial.pderiv_aeval`: the chain rule.
-/

@[expose] public noncomputable section

open Finset

namespace MvPolynomial

variable {R : Type*} [CommSemiring R] {σ τ : Type*} [Fintype σ]

/-- **The chain rule for `MvPolynomial.pderiv`.** For a substitution `g : σ → R[τ]` of
polynomials for the finitely many variables of `F`,
`∂/∂Y_a (F(g)) = ∑ᵢ (∂F/∂Xᵢ)(g) · ∂gᵢ/∂Y_a`. -/
theorem pderiv_aeval (g : σ → MvPolynomial τ R) (F : MvPolynomial σ R) (a : τ) :
    pderiv a (aeval g F) = ∑ i, aeval g (pderiv i F) * pderiv a (g i) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_mul, sum_add_distrib]
  | mul_X p j hp =>
    have h1 : ∀ i, aeval g (pderiv i (p * X j)) * pderiv a (g i) =
        g j * (aeval g (pderiv i p) * pderiv a (g i)) +
          aeval g p * (aeval g (Pi.single (M := fun _ => MvPolynomial σ R) i 1 j) *
            pderiv a (g i)) := by
      intro i
      simp only [Derivation.leibniz, smul_eq_mul, pderiv_X, map_add, map_mul, aeval_X]
      ring
    have h2 : ∑ i, aeval g (Pi.single (M := fun _ => MvPolynomial σ R) i 1 j) * pderiv a (g i) =
        pderiv a (g j) := by
      rw [sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    rw [sum_congr rfl fun i _ => h1 i, sum_add_distrib, ← mul_sum, ← mul_sum, map_mul, aeval_X,
      Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp, h2]
    ring

end MvPolynomial

end
