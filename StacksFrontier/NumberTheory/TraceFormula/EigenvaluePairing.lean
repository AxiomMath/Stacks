module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Eigenvalues of a matrix preserving a form up to a scalar

Let `A` and `J` be square matrices over a field with `J` invertible and `Aᵀ J A = q J`, `q ≠ 0`
(the Frobenius matrix on `H¹` of a curve and the matrix of the cup product pairing, which
Frobenius multiplies by `q`). Then the reciprocal roots `α_i` of `det(1 - T A) = ∏ (1 - α_i T)`
come in pairs `α_i α_j = q`.

Indeed `Aᵀ = q J A⁻¹ J⁻¹`, so for `s ≠ 0`
`det(1 - s A) = det(1 - s Aᵀ) = det(1 - s q A⁻¹) = det A⁻¹ · (-s q)ⁿ · det(1 - (s q)⁻¹ A)`,
and the root `s = α_i⁻¹` of the left side gives the root `α_i / q` of `det(1 - T A)`.

## Main results

* `Stacks.TraceFormula.exists_mul_eq_of_transpose_mul_mul_eq`
-/

@[expose] public noncomputable section

open Polynomial Matrix

namespace Stacks.TraceFormula

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant `det(1 - s A)` at a scalar `s`, as the evaluation of `det(1 - T A)`. -/
theorem eval_det_one_sub_smul (A : Matrix n n K) (s : K) :
    ((1 - (X : K[X]) • A.map C).det).eval s = (1 - s • A).det := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, Matrix.smul_apply]
  split_ifs <;> simp [mul_comm]

/-- A matrix preserving an invertible form up to a nonzero scalar is invertible. -/
private theorem det_ne_zero_of_transpose_mul_mul_eq {A J : Matrix n n K} {q : K} (hq : q ≠ 0)
    (hJ : J.det ≠ 0) (h : Aᵀ * J * A = q • J) : A.det ≠ 0 := by
  intro hA
  have := congrArg Matrix.det h
  rw [det_mul, det_mul, det_transpose, hA, det_smul] at this
  simp only [mul_zero, zero_mul] at this
  exact hJ ((mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ hq))

/-- **The functional equation of `det(1 - T A)`** for `Aᵀ J A = q J`. -/
theorem det_one_sub_smul_eq_zero_iff {A J : Matrix n n K} {q : K} (hq : q ≠ 0)
    (hJ : J.det ≠ 0) (h : Aᵀ * J * A = q • J) {s : K} (hs : s ≠ 0) :
    (1 - s • A).det = 0 ↔ (1 - (s * q)⁻¹ • A).det = 0 := by
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero_of_transpose_mul_mul_eq hq hJ h)
  -- `Aᵀ = q J A⁻¹ J⁻¹`
  have hT : Aᵀ = q • (J * A⁻¹ * J⁻¹) := by
    have h1 : Aᵀ * J * A * A⁻¹ * J⁻¹ = q • J * A⁻¹ * J⁻¹ := by rw [h]
    rw [Matrix.mul_assoc (Aᵀ * J), mul_nonsing_inv _ hAu, Matrix.mul_one,
      Matrix.mul_assoc, mul_nonsing_inv _ hJu, Matrix.mul_one] at h1
    rw [h1, Matrix.smul_mul, Matrix.smul_mul]
  have hkey : (1 - s • A).det =
      A⁻¹.det * (-(s * q)) ^ Fintype.card n * (1 - (s * q)⁻¹ • A).det := by
    calc (1 - s • A).det = (1 - s • A)ᵀ.det := (det_transpose _).symm
      _ = (J * (1 - (s * q) • A⁻¹) * J⁻¹).det := by
          congr 1
          rw [transpose_sub, transpose_one, transpose_smul, hT, Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_one, mul_nonsing_inv _ hJu, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      _ = (1 - (s * q) • A⁻¹).det := by
          rw [det_mul, det_mul, mul_comm (J.det), mul_assoc, ← det_mul, mul_nonsing_inv _ hJu,
            det_one, mul_one]
      _ = (A⁻¹ * (A - (s * q) • 1)).det := by
          congr 1
          rw [Matrix.mul_sub, nonsing_inv_mul _ hAu, Matrix.mul_smul, Matrix.mul_one]
      _ = A⁻¹.det * (-(s * q)) ^ Fintype.card n * (1 - (s * q)⁻¹ • A).det := by
          rw [det_mul, mul_assoc]
          congr 1
          rw [← det_smul]
          congr 1
          rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ (mul_ne_zero hs hq)]
          simp only [neg_smul, one_smul]
          abel
  rw [hkey, mul_eq_zero, or_iff_right (mul_ne_zero (isUnit_nonsing_inv_det A hAu).ne_zero
    (pow_ne_zero _ (neg_ne_zero.2 (mul_ne_zero hs hq))))]

/-- The reciprocal roots of `det(1 - T A)` are nonzero when `A` is invertible. -/
private theorem ne_zero_of_det_one_sub_smul_eq_prod {A : Matrix n n K} (hA : A.det ≠ 0) (α : n → K)
    (hα : (1 - (X : K[X]) • A.map C).det = ∏ i, (1 - C (α i) * X)) (j : n) : α j ≠ 0 := by
  -- all the `α_j` are nonzero: compare the coefficients of `T ^ #n`
  have hcoeff := congrArg (fun P : K[X] => P.coeff (Fintype.card n)) hα
  have h1 : (∏ i, (1 - C (α i) * X)).coeff (Fintype.card n) = ∏ i, (-α i) := by
    have := coeff_prod_of_natDegree_le (s := Finset.univ) (fun i => 1 - C (α i) * X) 1
      (fun i _ => by
        refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
        exact (natDegree_C_mul_le _ _).trans natDegree_X_le)
    rw [Finset.card_univ, mul_one] at this
    rw [this]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [coeff_one]
  have h2 : (1 - (X : K[X]) • A.map C).det.coeff (Fintype.card n) =
      (-1) ^ Fintype.card n * A.det := by
    have hrev := A.reverse_charpoly
    rw [Matrix.charpolyRev] at hrev
    rw [← hrev, coeff_reverse, charpoly_natDegree_eq_dim, revAt_le le_rfl, Nat.sub_self,
      det_eq_sign_charpoly_coeff, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_mul]
  rw [h1, h2] at hcoeff
  have hne : ∏ i, (-α i) ≠ 0 := by
    rw [← hcoeff]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hA
  intro hj
  exact hne (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, neg_zero]))

/-- **The eigenvalues of a matrix preserving a form up to `q` are paired.** If `J` is invertible,
`Aᵀ J A = q J` with `q ≠ 0`, and `det(1 - T A) = ∏_i (1 - α_i T)`, then every `α_i` has a partner
`α_j` with `α_i α_j = q`. -/
theorem exists_mul_eq_of_transpose_mul_mul_eq {A J : Matrix n n K} {q : K} (hq : q ≠ 0)
    (hJ : J.det ≠ 0) (h : Aᵀ * J * A = q • J) (α : n → K)
    (hα : (1 - (X : K[X]) • A.map C).det = ∏ i, (1 - C (α i) * X)) (i : n) :
    ∃ j, α i * α j = q := by
  classical
  have hα0 := ne_zero_of_det_one_sub_smul_eq_prod (det_ne_zero_of_transpose_mul_mul_eq hq hJ h)
    α hα
  -- `α_i⁻¹` is a root of `det(1 - T A)`, hence so is `α_i / q`
  have hroot : ∀ t : K, (1 - t • A).det = ∏ j, (1 - α j * t) := by
    intro t
    rw [← eval_det_one_sub_smul, hα, eval_prod]
    simp
  have hs : (1 - (α i)⁻¹ • A).det = 0 := by
    rw [hroot]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [mul_inv_cancel₀ (hα0 i), sub_self])
  have h' := (det_one_sub_smul_eq_zero_iff hq hJ h (inv_ne_zero (hα0 i))).1 hs
  rw [hroot] at h'
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h'
  refine ⟨j, ?_⟩
  have hαi := hα0 i
  rw [_root_.mul_inv_rev, inv_inv, sub_eq_zero] at hj
  field_simp at hj
  linear_combination -hj

end Stacks.TraceFormula

end
