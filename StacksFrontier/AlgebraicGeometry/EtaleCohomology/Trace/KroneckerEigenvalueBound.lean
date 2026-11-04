module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeightsFromTraceGrowth

/-!
# Eigenvalue bounds for Kronecker products

Read along a field embedding `ι : K → ℂ`, if every eigenvalue of `A` has absolute value at most
`R` and every eigenvalue of `B` at most `S`, then every eigenvalue of the Kronecker product
`A ⊗ B` has absolute value at most `R S`.

## Main results

* `Stacks.EtaleCohomology.norm_map_trace_pow_le_of_forall_isRoot`: if the eigenvalues of `A` have
  absolute value at most `R ≥ 0`, then `|ι Tr(A ^ n)| ≤ a R ^ n`.
* `Stacks.EtaleCohomology.norm_le_mul_of_isRoot_charpoly_kroneckerMonoidHom`: the eigenvalues of
  `A ⊗ B` have absolute value at most `R S`.
-/

@[expose] public noncomputable section

open Matrix Filter Asymptotics
open scoped Kronecker

namespace Stacks.EtaleCohomology

variable {K : Type*} [Field K] (ι : K →+* ℂ)

/-- If every eigenvalue of `A`, read along `ι`, has absolute value at most `R ≥ 0`, then
`|ι Tr(A ^ n)| ≤ a R ^ n`. -/
public theorem norm_map_trace_pow_le_of_forall_isRoot {a : ℕ} (A : Matrix (Fin a) (Fin a) K)
    {R : ℝ} (hR : 0 ≤ R) (hA : ∀ z : ℂ, (A.charpoly.map ι).IsRoot z → ‖z‖ ≤ R) (n : ℕ) :
    ‖ι (A ^ n).trace‖ ≤ a * R ^ n := by
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow, map_trace_pow_eq_sum_roots_map_pow,
    Matrix.charpoly_toLin']
  refine (norm_multiset_sum_le _).trans ?_
  rw [Multiset.map_map]
  have hle : ∀ z ∈ (A.charpoly.map ι).roots, ‖(z ^ n : ℂ)‖ ≤ R ^ n := fun z hz => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg z) (hA z ((Polynomial.mem_roots'.1 hz).2)) n
  calc ((A.charpoly.map ι).roots.map ((‖·‖) ∘ (· ^ n))).sum
      ≤ ((A.charpoly.map ι).roots.map fun _ => R ^ n).sum :=
        Multiset.sum_map_le_sum_map _ _ fun z hz => hle z hz
    _ = Multiset.card (A.charpoly.map ι).roots * R ^ n := by simp
    _ ≤ a * R ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hR n)
        have := Polynomial.card_roots' (A.charpoly.map ι)
        rw [Polynomial.natDegree_map, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
        exact_mod_cast this

/-- Reindexing a square matrix on `Fin a × Fin b` along `finProdFinEquiv` preserves its trace. -/
theorem trace_reindex_finProdFinEquiv {a b : ℕ} (M : Matrix (Fin a × Fin b) (Fin a × Fin b) K) :
    (Matrix.reindex finProdFinEquiv finProdFinEquiv M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact finProdFinEquiv.symm.sum_comp fun i => M i i

/-- **Eigenvalues of a Kronecker product.** If every eigenvalue of `A`, read along `ι`, has
absolute value at most `R ≥ 0` and every eigenvalue of `B` at most `S ≥ 0`, then every eigenvalue
of `A ⊗ B` has absolute value at most `R S`. -/
public theorem norm_le_mul_of_isRoot_charpoly_kroneckerMonoidHom {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) {R S : ℝ} (hR : 0 ≤ R)
    (hS : 0 ≤ S) (hA : ∀ z : ℂ, (A.charpoly.map ι).IsRoot z → ‖z‖ ≤ R)
    (hB : ∀ z : ℂ, (B.charpoly.map ι).IsRoot z → ‖z‖ ≤ S) (z : ℂ)
    (hz : ((kroneckerMonoidHom (A, B)).charpoly.map ι).IsRoot z) : ‖z‖ ≤ R * S := by
  set M := kroneckerMonoidHom (A, B) with hM
  have htr : ∀ n : ℕ, (M ^ n).trace = (A ^ n).trace * (B ^ n).trace := fun n => by
    rw [hM, ← map_pow, Prod.pow_mk, kroneckerMonoidHom_apply, trace_reindex_finProdFinEquiv,
      Matrix.trace_kronecker]
  have hbig : (fun n : ℕ => ((M.charpoly.map ι).roots.map (· ^ n)).sum - (0 : Multiset ℂ).sum)
      =O[atTop] fun n => (R * S) ^ n := by
    refine IsBigO.of_bound ((a : ℝ) * b) (Eventually.of_forall fun n => ?_)
    rw [Multiset.sum_zero, sub_zero, ← Matrix.charpoly_toLin', ← map_trace_pow_eq_sum_roots_map_pow,
      ← Matrix.toLin'_pow, Matrix.trace_toLin'_eq, htr, map_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (mul_nonneg hR hS) n), mul_pow]
    calc ‖ι (A ^ n).trace‖ * ‖ι (B ^ n).trace‖ ≤ (a * R ^ n) * (b * S ^ n) :=
          mul_le_mul (norm_map_trace_pow_le_of_forall_isRoot ι A hR hA n)
            (norm_map_trace_pow_le_of_forall_isRoot ι B hS hB n) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR n))
      _ = (a : ℝ) * b * (R ^ n * S ^ n) := by ring
  refine norm_le_of_isBigO_multiset_sum_pow_sub (B := 0) (mul_nonneg hR hS) (by simp) hbig z ?_
  exact (Polynomial.mem_roots ((Matrix.charpoly_monic M).map ι).ne_zero).2 hz

end Stacks.EtaleCohomology

end
