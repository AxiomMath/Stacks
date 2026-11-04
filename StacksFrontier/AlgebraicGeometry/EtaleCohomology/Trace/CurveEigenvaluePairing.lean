module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalCharPolynomial
public import StacksFrontier.NumberTheory.TraceFormula.EigenvaluePairing

/-!
# Pairing of the Frobenius eigenvalues from a form multiplied by `q`

If the Frobenius matrix `A` on `H¹` and an invertible matrix `J` (the cup product pairing) satisfy
`Aᵀ J A = q J`, then the reciprocal roots `α_i` of `det(1 - A T)`, read in a field through
`φ : Λ → Ω`, are paired: `α_i α_j = q`. This is the hypothesis `hpair` of
`Stacks.BombieriStepanov.norm_eq_sqrt_of_smooth`.

## Main results

* `Stacks.EtaleCohomology.exists_mul_eq_of_localCharPolynomial`
-/

@[expose] public noncomputable section

open Polynomial Matrix

namespace Stacks.EtaleCohomology

/-- **The eigenvalues of `π_X^*` on `H¹` are paired by a form multiplied by `q`.** -/
theorem exists_mul_eq_of_localCharPolynomial {Λ : Type*} [CommRing Λ] {Ω : Type*} [Field Ω]
    (φ : Λ →+* Ω) {n : Type*} [Fintype n] [DecidableEq n] (A J : Matrix n n Λ) (q : ℕ)
    (hq : (q : Ω) ≠ 0) (hJ : IsUnit J.det) (h : Aᵀ * J * A = (q : Λ) • J) (α : n → Ω)
    (hα : (localCharPolynomial A 1).map φ = ∏ i, (1 - C (α i) * X)) (i : n) :
    ∃ j, α i * α j = q := by
  have hJ' : (J.map φ).det ≠ 0 := by
    have := RingHom.map_det φ J
    rw [RingHom.mapMatrix_apply] at this
    rw [← this]
    exact (hJ.map φ).ne_zero
  have h' : (A.map φ)ᵀ * J.map φ * A.map φ = (q : Ω) • J.map φ := by
    have := congrArg (fun M : Matrix n n Λ => M.map φ) h
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    rw [this]
    ext a b
    simp
  have hα' : (1 - (X : Ω[X]) • (A.map φ).map C).det = ∏ i, (1 - C (α i) * X) := by
    rw [← hα, localCharPolynomial, localCharPolyMatrix, pow_one, ← Polynomial.coe_mapRingHom,
      RingHom.map_det]
    congr 1
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  exact Stacks.TraceFormula.exists_mul_eq_of_transpose_mul_mul_eq hq hJ' h' α hα' i

end Stacks.EtaleCohomology

end
