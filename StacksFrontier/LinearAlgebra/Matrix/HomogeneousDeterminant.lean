module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The determinant of a matrix of forms is a form

The determinant of a square matrix of size `N` whose entries are homogeneous polynomials of
degree `d` is homogeneous of degree `N * d`: the Leibniz expansion is a signed sum of products
of `N` entries, one from each column.

## Main results

* `Matrix.IsHomogeneous.det`: the determinant of a matrix of homogeneous polynomials of
  degree `d` indexed by a finite type is homogeneous of degree `Fintype.card * d`.
-/

@[expose] public section

namespace Matrix

/-- The determinant of a square matrix whose entries are homogeneous polynomials of degree `d`
is homogeneous of degree `Fintype.card ι * d`. -/
protected theorem IsHomogeneous.det {ι R σ : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {d : ℕ} (M : Matrix ι ι (MvPolynomial σ R)) (hM : ∀ i j, (M i j).IsHomogeneous d) :
    M.det.IsHomogeneous (Fintype.card ι * d) := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun p _ ↦ ?_
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i ↦ M (p i) i) (fun _ ↦ d)
    fun i _ ↦ hM _ _
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  simpa using h.C_mul ((Equiv.Perm.sign p : ℤ) : R)

end Matrix

end
