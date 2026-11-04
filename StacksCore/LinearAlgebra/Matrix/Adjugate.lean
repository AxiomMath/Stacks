module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # The adjugate against a row-partitioned matrix

Stacks 080R: for `A` written in blocks as `A₁` over `A₂` with `A₁` square, multiplying by the
adjugate of `A₁` gives `det A₁ • 1` on top and, underneath, entries that are `m × m` minors of
the stacked matrix. Mathlib has `Matrix.mul_adjugate` for the square top block; what is missing
is the entrywise description of the bottom block.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [CommRing R] {m p : Type*} [Fintype m] [DecidableEq m]

/-- Row-vector times adjugate, entrywise: the `j`th entry of `v ᵥ* adjugate A` is the
determinant of `A` with its `j`th row replaced by `v`. -/
theorem vecMul_adjugate_apply (A : Matrix m m R) (v : m → R) (j : m) :
    (v ᵥ* adjugate A) j = (A.updateRow j v).det := by
  rw [← Matrix.mulVec_transpose, Matrix.adjugate_transpose,
    ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_transpose_apply]

/-- Entrywise form of `Matrix.mul_adjugate` for a rectangular left factor. -/
theorem mul_adjugate_apply_of_fromRows (A₁ : Matrix m m R) (A₂ : Matrix p m R)
    (i : p) (j : m) : (A₂ * adjugate A₁) i j = (A₁.updateRow j (A₂ i)).det :=
  vecMul_adjugate_apply A₁ (A₂ i) j

/-- **Stacks 080R.** -/
@[stacks 080R]
theorem fromRows_mul_adjugate (A₁ : Matrix m m R) (A₂ : Matrix p m R) :
    fromRows A₁ A₂ * adjugate A₁ =
      fromRows (A₁.det • (1 : Matrix m m R))
        (Matrix.of fun (i : p) (j : m) => (A₁.updateRow j (A₂ i)).det) := by
  rw [Matrix.fromRows_mul, Matrix.mul_adjugate]
  simpa [← Matrix.ext_iff] using mul_adjugate_apply_of_fromRows A₁ A₂

/-- **Stacks 080R**, identifying the bottom block's entries as `m × m` minors of the stacked
matrix — with no sign, taking the rows in the order `1, …, ĵ, …, m` with `i` at slot `j`. -/
@[stacks 080R]
theorem fromRows_mul_adjugate_apply_inr (A₁ : Matrix m m R)
    (A₂ : Matrix p m R) (i : p) (j : m) :
    (fromRows A₁ A₂ * adjugate A₁) (Sum.inr i) j =
      ((fromRows A₁ A₂).submatrix (Function.update Sum.inl j (Sum.inr i)) id).det := by
  rw [Matrix.fromRows_mul_adjugate]
  simp only [fromRows_apply_inr, Matrix.of_apply]
  congr 1
  ext r c
  rcases eq_or_ne r j with h | h <;> simp [h]

end Matrix
