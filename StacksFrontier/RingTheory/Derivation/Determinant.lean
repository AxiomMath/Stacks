module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Jacobi's formula for a derivation

A derivation `D` of a commutative ring `A` differentiates the determinant of a square matrix
`M` over `A` by Jacobi's formula

`D (det M) = trace (adjugate M * D M)`,

where `D M` denotes the entrywise image of `M`.  The determinant is multilinear in the columns,
so differentiating the Leibniz expansion replaces one column at a time by its derivative; the
cofactor expansion of a determinant with a replaced column is Cramer's rule, which turns the
sum of those determinants into the trace against the adjugate.

## Main results

* `Derivation.map_finsetProd`: the Leibniz rule for a finite product.
* `Derivation.map_det`: Jacobi's formula.
-/

@[expose] public section

open Finset Matrix

namespace Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A)

/-- The Leibniz rule for a finite product: a derivation of a product over a finite set is the
sum, over the factors, of the product of the remaining factors with the derivative of that
factor. -/
theorem map_finsetProd {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have key : ∀ i ∈ s, (∏ j ∈ (insert a s).erase i, f j) * D (f i)
          = f a * ((∏ j ∈ s.erase i, f j) * D (f i)) := by
        intro i hi
        rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hi ha).symm, Finset.prod_insert
          (fun h => ha (Finset.mem_of_mem_erase h))]
        ring
      rw [Finset.prod_insert ha, Derivation.leibniz, Finset.sum_insert ha,
        Finset.sum_congr rfl key, Finset.erase_insert ha, ih]
      simp only [smul_eq_mul, Finset.mul_sum]
      ring

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Leibniz expansion of a determinant one of whose columns has been replaced: only the
entries of the other columns and the new column occur. -/
private lemma det_updateCol_eq (M : Matrix n n A) (v : n → A) (i : n) :
    (M.updateCol i v).det = ∑ σ : Equiv.Perm n,
      (Equiv.Perm.sign σ : A) * ((∏ j ∈ Finset.univ.erase i, M (σ j) j) * v (σ i)) := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h : ∀ j ∈ Finset.univ.erase i, (M.updateCol i v) (σ j) j = M (σ j) j := fun j hj => by
    simp [Finset.ne_of_mem_erase hj]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Finset.prod_congr rfl h]
  simp

/-- **Jacobi's formula**.  A derivation of the determinant of a square matrix is the trace of
the adjugate against the entrywise derivative. -/
theorem map_det (M : Matrix n n A) : D M.det = (M.adjugate * M.map D).trace := by
  have hr : (M.adjugate * M.map D).trace
      = ∑ i : n, (M.updateCol i fun j => D (M j i)).det := by
    refine (Finset.sum_congr rfl fun i _ => ?_).symm
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
  rw [hr, Matrix.det_apply']
  simp only [det_updateCol_eq, ← zsmul_eq_mul, map_sum, map_zsmul, map_finsetProd,
    Finset.smul_sum]
  rw [Finset.sum_comm]

end Derivation

end
