module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepContinuity
public import Mathlib.RingTheory.Discriminant

/-!
# Restriction of scalars and transposition: the trace Gram matrix

Let `E / F` be a finite extension with basis `b` and `T = (Tr(bₗ bₗ'))` its trace Gram matrix.
Multiplication by `a ∈ E` is self-adjoint for the trace form, `T L_a = L_aᵀ T`
(`Stacks.EtaleCohomology.traceMatrix_mul_leftMulMatrix`). Hence the block-diagonal matrix
`G = diag(T, …, T)` relates the restriction of scalars of a transpose to the transpose of a
restriction of scalars: `G · Res_b(Mᵀ) = Res_b(M)ᵀ · G`
(`Stacks.EtaleCohomology.restrictScalarsTraceGram_mul_transpose`), and `G` is invertible when
`E / F` is separable. Consequently `Res_b(σ^∨)` is conjugate to `(Res_b σ)^∨` by `G`, and `G`
carries the transposed action of `E` to its action by restriction of scalars.

## Main definitions

* `Stacks.EtaleCohomology.finProdBlockDiagonal`: the block-diagonal matrix `diag(T, …, T)`.
* `Stacks.EtaleCohomology.restrictScalarsTraceGram`: the matrix `G = diag(T, …, T)` for the trace
  Gram matrix `T`.

## Main results

* `Stacks.EtaleCohomology.restrictScalarsTraceGram_mul_transpose`: `G · Res_b(Mᵀ) = Res_b(M)ᵀ · G`.
* `Stacks.EtaleCohomology.isUnit_restrictScalarsTraceGram`: `G` is invertible when `E / F` is
  separable.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

section Block

variable {F : Type*} [CommRing F] {d : ℕ} (m : ℕ)

/-- The block-diagonal matrix `diag(T, …, T)` (`m` blocks), indexed as the restrictions of
scalars, by `finProdFinEquiv` on `Fin m × Fin d`. -/
public def finProdBlockDiagonal (T : Matrix (Fin d) (Fin d) F) :
    Matrix (Fin (m * d)) (Fin (m * d)) F :=
  Matrix.of fun p q => if (finProdFinEquiv.symm p).1 = (finProdFinEquiv.symm q).1 then
    T (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm q).2 else 0

/-- The entries of `diag(T, …, T)`: the `(i, l), (j, l')` entry is `T l l'` if `i = j` and `0`
otherwise. -/
@[simp]
public theorem finProdBlockDiagonal_apply (T : Matrix (Fin d) (Fin d) F) (i j : Fin m)
    (l l' : Fin d) :
    finProdBlockDiagonal m T (finProdFinEquiv (i, l)) (finProdFinEquiv (j, l')) =
      if i = j then T l l' else 0 := by
  simp only [finProdBlockDiagonal, Matrix.of_apply, Equiv.symm_apply_apply]

/-- `diag(T, …, T) · diag(T', …, T') = diag(T T', …, T T')`. -/
public theorem finProdBlockDiagonal_mul (T T' : Matrix (Fin d) (Fin d) F) :
    finProdBlockDiagonal m T * finProdBlockDiagonal m T' = finProdBlockDiagonal m (T * T') := by
  ext p q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [Matrix.mul_apply, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [finProdBlockDiagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.mul_apply]
  · simp [hij]

/-- `diag(1, …, 1) = 1`. -/
public theorem finProdBlockDiagonal_one :
    finProdBlockDiagonal m (1 : Matrix (Fin d) (Fin d) F) = 1 := by
  ext p q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [finProdBlockDiagonal_apply]
  by_cases hij : i = j <;> by_cases hll : l = l' <;>
    simp [hij, hll, Matrix.one_apply, finProdFinEquiv.injective.eq_iff]

end Block

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/-- **Multiplication by `a` is self-adjoint for the trace form**: `T L_a = L_aᵀ T` for the trace
Gram matrix `T` of `b` and the matrix `L_a` of multiplication by `a`. -/
public theorem traceMatrix_mul_leftMulMatrix (a : E) :
    Algebra.traceMatrix F b * Algebra.leftMulMatrix b a =
      (Algebra.leftMulMatrix b a)ᵀ * Algebra.traceMatrix F b := by
  have key : ∀ (l : Fin d) (y : E),
      ∑ k, Algebra.trace F E (b l * b k) * b.repr y k = Algebra.trace F E (b l * y) := by
    intro l y
    conv_rhs => rw [← b.sum_repr y]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  ext l l'
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.transpose_apply,
    Algebra.leftMulMatrix_eq_repr_mul]
  rw [key l (a * b l')]
  have h2 : ∑ k, b.repr (a * b l) k * Algebra.trace F E (b k * b l') =
      ∑ k, Algebra.trace F E (b l' * b k) * b.repr (a * b l) k :=
    Finset.sum_congr rfl fun k _ => by rw [mul_comm, mul_comm (b k)]
  rw [h2, key l' (a * b l)]
  congr 1
  ring

/-- **The trace Gram matrix of the restriction of scalars**, `diag(T, …, T)` with `m` blocks. -/
public abbrev restrictScalarsTraceGram (m : ℕ) : Matrix (Fin (m * d)) (Fin (m * d)) F :=
  finProdBlockDiagonal m (Algebra.traceMatrix F b)

/-- **`G · Res_b(Mᵀ) = Res_b(M)ᵀ · G`** for the trace Gram matrix `G` of the restriction of
scalars. -/
public theorem restrictScalarsTraceGram_mul_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) E) :
    restrictScalarsTraceGram b m * restrictScalarsMatrix b Mᵀ =
      (restrictScalarsMatrix b M)ᵀ * restrictScalarsTraceGram b m := by
  ext p q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [Matrix.mul_apply, Matrix.mul_apply, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [finProdBlockDiagonal_apply, Matrix.transpose_apply, restrictScalarsMatrix_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h := congrFun (congrFun (traceMatrix_mul_leftMulMatrix b (M j i)) l) l'
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  simpa only [Matrix.transpose_apply] using h

variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- The trace Gram matrix of a separable extension is invertible. -/
public theorem isUnit_traceMatrix : IsUnit (Algebra.traceMatrix F b) := by
  rw [Matrix.isUnit_iff_isUnit_det, ← Algebra.discr_def]
  exact isUnit_iff_ne_zero.2 (Algebra.discr_not_zero_of_basis F b)

/-- **The trace Gram matrix of the restriction of scalars is invertible**, `E / F` separable. -/
public theorem isUnit_restrictScalarsTraceGram (m : ℕ) :
    IsUnit (restrictScalarsTraceGram b m) := by
  obtain ⟨T, hT⟩ := isUnit_traceMatrix b
  have h : restrictScalarsTraceGram b m *
      finProdBlockDiagonal m (↑T⁻¹ : Matrix (Fin d) (Fin d) F) = 1 := by
    rw [restrictScalarsTraceGram, finProdBlockDiagonal_mul, ← hT, Units.mul_inv,
      finProdBlockDiagonal_one]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h)

end Stacks.EtaleCohomology

end
