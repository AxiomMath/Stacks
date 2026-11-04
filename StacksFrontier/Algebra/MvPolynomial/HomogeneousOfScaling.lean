module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Combinatorics.Nullstellensatz
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# A polynomial which scales like a homogeneous one is homogeneous

Let `P` be a polynomial with rational coefficients in finitely many variables. If
`P (m • c) = m ^ N * P c` for all integers `m` and all integral points `c`, then `P` is
homogeneous of degree `N`.

## Main results

* `MvPolynomial.IsHomogeneous.eval_smul'` — `P (c • x) = c ^ N * P x` for `P` homogeneous.
* `MvPolynomial.isHomogeneous_of_eval_intCast_mul` — the criterion.
-/

@[expose] public noncomputable section

open Finset

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R]

/-- A homogeneous polynomial of degree `N` scales by `c ^ N`. -/
theorem IsHomogeneous.eval_smul' [Finite σ] {P : MvPolynomial σ R} {N : ℕ} (hP : P.IsHomogeneous N)
    (c : R) (x : σ → R) : eval (c • x) P = c ^ N * eval x P := by
  rw [eval_eq, eval_eq, mul_sum]
  refine sum_congr rfl fun s hs => ?_
  have hdeg : ∑ i ∈ s.support, s i = N := by
    have := hP (mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hdeg]
  ring

/-- A polynomial over `ℚ` vanishing at every integral point is zero. -/
theorem eq_zero_of_eval_intCast_eq_zero [Finite σ] {P : MvPolynomial σ ℚ}
    (h : ∀ c : σ → ℤ, eval (fun i => (c i : ℚ)) P = 0) : P = 0 := by
  classical
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun _ => (range (P.totalDegree + 1)).image (fun n : ℕ => (n : ℚ))) (fun i => ?_) ?_
  · rw [card_image_of_injective _ Nat.cast_injective, card_range]
    exact Nat.lt_succ_of_le (degreeOf_le_totalDegree P i)
  · intro x hx
    choose n _ hn using fun i => mem_image.mp (hx i)
    have : x = fun i => ((n i : ℤ) : ℚ) := _root_.funext fun i => by rw [← hn i]; simp
    rw [this]
    exact h fun i => (n i : ℤ)

/-- **A polynomial which scales like a homogeneous polynomial of degree `N` on integral points
is homogeneous of degree `N`.** -/
theorem isHomogeneous_of_eval_intCast_mul [Finite σ] {P : MvPolynomial σ ℚ} {N : ℕ}
    (h : ∀ (m : ℤ) (c : σ → ℤ),
      eval (fun i => ((m * c i : ℤ) : ℚ)) P = (m : ℚ) ^ N * eval (fun i => (c i : ℚ)) P) :
    P.IsHomogeneous N := by
  classical
  set T := P.totalDegree
  have hout : ∀ d, d ∉ range (T + 1) → homogeneousComponent d P = 0 := fun d hd =>
    homogeneousComponent_eq_zero d P (by simp at hd; omega)
  have hvan : ∀ d, d ≠ N → ∀ c : σ → ℤ,
      eval (fun i => (c i : ℚ)) (homogeneousComponent d P) = 0 := by
    intro d hd c
    let Q : Polynomial ℚ :=
      ∑ e ∈ range (T + 1), Polynomial.C (eval (fun i => (c i : ℚ)) (homogeneousComponent e P)) *
        Polynomial.X ^ e - Polynomial.C (eval (fun i => (c i : ℚ)) P) * Polynomial.X ^ N
    have hQ : ∀ m : ℤ, Q.eval (m : ℚ) = 0 := by
      intro m
      have h1 : eval (fun i => ((m * c i : ℤ) : ℚ)) P =
          ∑ e ∈ range (T + 1),
            (m : ℚ) ^ e * eval (fun i => (c i : ℚ)) (homogeneousComponent e P) := by
        conv_lhs => rw [← sum_homogeneousComponent P]
        rw [map_sum]
        refine sum_congr rfl fun e _ => ?_
        have : (fun i => ((m * c i : ℤ) : ℚ)) = (m : ℚ) • fun i => (c i : ℚ) :=
          _root_.funext fun i => by simp
        rw [this, (homogeneousComponent_isHomogeneous e P).eval_smul']
      simp only [Q, Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [sub_eq_zero, mul_comm (eval _ P), ← h m c, h1]
      exact sum_congr rfl fun e _ => mul_comm _ _
    have hQ0 : Q = 0 := by
      refine Polynomial.eq_of_infinite_eval_eq Q 0 ?_
      refine Set.infinite_of_injective_forall_mem (f := fun m : ℤ => (m : ℚ)) Int.cast_injective ?_
      intro m
      simp [hQ m]
    by_cases hdT : d ∈ range (T + 1)
    · have hc := congrArg (fun F => Polynomial.coeff F d) hQ0
      simp only [Q, Polynomial.coeff_sub, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hc
      rw [sum_eq_single d (fun e _ he => by simp [Ne.symm he]) (fun h' => absurd hdT h'),
        if_pos rfl, if_neg hd, mul_zero, sub_zero, mul_one] at hc
      exact hc
    · rw [hout d hdT]
      simp
  have hzero : ∀ d, d ≠ N → homogeneousComponent d P = 0 := fun d hd =>
    eq_zero_of_eval_intCast_eq_zero (hvan d hd)
  have hP : P = homogeneousComponent N P := by
    conv_lhs => rw [← sum_homogeneousComponent P]
    exact sum_eq_single N (fun d _ hd => hzero d hd) (hout N)
  rw [hP]
  exact homogeneousComponent_isHomogeneous N P

end MvPolynomial
