module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GradedCompoundMatrices
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerTensorComparison

/-!
# Kronecker powers and compound matrices: multiplicativity, base change and gradings

`A ↦ A^{⊗ j}` (`Stacks.EtaleCohomology.kronPowMatrix`) is multiplicative and commutes with ring
homomorphisms applied entrywise, as do compound matrices.  For a graded upper triangular `A`, the
Kronecker power is graded upper triangular for the sum grading, with graded diagonal part the
Kronecker power of the graded diagonal part; gradings move along reindexings.  With
`Stacks.EtaleCohomology.gradedDiag_compound` this says that the semisimplification of a flag
commutes with the tensor constructions `(⋀ᵏ -)^{⊗ j}`.

## Main results

* `Stacks.EtaleCohomology.kronPowMatrix_mul`, `Stacks.EtaleCohomology.kronPowMatrix_map`,
  `Stacks.EtaleCohomology.compoundMonoidHom_map`.
* `Stacks.EtaleCohomology.IsGradedUpper.kronPowMatrix`,
  `Stacks.EtaleCohomology.gradedDiag_kronPowMatrix`.
-/

@[expose] public noncomputable section

open Matrix
open scoped Kronecker

namespace Stacks.EtaleCohomology

variable {R S : Type*} [CommRing R] [CommRing S] {s : ℕ}

/-- One step of the Kronecker power: reindex the Kronecker product with `A`. -/
private theorem kronPowMatrix_succ (A : Matrix (Fin s) (Fin s) R) (j : ℕ) :
    kronPowMatrix A (j + 1) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (kronPowMatrix A j ⊗ₖ A) := rfl

/-- The Kronecker power of the identity matrix is the identity matrix. -/
public theorem kronPowMatrix_one (j : ℕ) : kronPowMatrix (1 : Matrix (Fin s) (Fin s) R) j = 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [kronPowMatrix_succ, ih, one_kronecker_one]
    exact (Matrix.reindexAlgEquiv R R finProdFinEquiv).map_one

/-- The Kronecker power is multiplicative: `(A * B)^{⊗ j} = A^{⊗ j} * B^{⊗ j}`. -/
public theorem kronPowMatrix_mul (A B : Matrix (Fin s) (Fin s) R) (j : ℕ) :
    kronPowMatrix (A * B) j = kronPowMatrix A j * kronPowMatrix B j := by
  induction j with
  | zero => exact (Matrix.mul_one 1).symm
  | succ j ih =>
    simp only [kronPowMatrix_succ]
    rw [ih, mul_kronecker_mul]
    exact (Matrix.reindexAlgEquiv R R finProdFinEquiv).map_mul _ _

/-- The Kronecker power commutes with applying a ring homomorphism entrywise. -/
public theorem kronPowMatrix_map (f : R →+* S) (A : Matrix (Fin s) (Fin s) R) (j : ℕ) :
    (kronPowMatrix A j).map f = kronPowMatrix (A.map f) j := by
  ext I J
  rw [Matrix.map_apply, kronPowMatrix_apply, kronPowMatrix_apply, map_prod]
  rfl

/-- The compound matrix commutes with applying a ring homomorphism entrywise. -/
public theorem compoundMonoidHom_map (f : R →+* S) {n : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    (compoundMonoidHom k A).map f = compoundMonoidHom k (A.map f) := by
  ext T U
  rw [Matrix.map_apply, compoundMonoidHom_apply_apply, compoundMonoidHom_apply_apply,
    RingHom.map_det]
  rfl

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
/-- Reindexing a graded upper triangular matrix along `e` gives a graded upper triangular matrix
for the transported grading `d ∘ e.symm`. -/
public theorem IsGradedUpper.reindex {d : ι → ℤ} {T : Matrix ι ι R} (hT : IsGradedUpper d T)
    (e : ι ≃ κ) : IsGradedUpper (d ∘ e.symm) (Matrix.reindex e e T) :=
  fun _ _ h => hT _ _ h

omit [Fintype ι] [Fintype κ] in
/-- The graded diagonal part commutes with reindexing, for the transported grading. -/
public theorem gradedDiag_reindex (d : ι → ℤ) (T : Matrix ι ι R) (e : ι ≃ κ) :
    gradedDiag (d ∘ e.symm) (Matrix.reindex e e T) = Matrix.reindex e e (gradedDiag d T) := by
  ext i j
  rfl

/-- The grading of `Fin (s ^ j)` induced by a grading of `Fin s`: the sum over the coordinates. -/
public def kronPowGrading (d : Fin s → ℤ) : (j : ℕ) → Fin (s ^ j) → ℤ
  | 0 => fun _ => 0
  | j + 1 => (fun p : Fin (s ^ j) × Fin s => kronPowGrading d j p.1 + d p.2) ∘ finProdFinEquiv.symm

/-- The Kronecker power of a graded upper triangular matrix is graded upper triangular for the
sum grading `kronPowGrading d j`. -/
public theorem IsGradedUpper.kronPowMatrix {d : Fin s → ℤ} {A : Matrix (Fin s) (Fin s) R}
    (hA : IsGradedUpper d A) (j : ℕ) : IsGradedUpper (kronPowGrading d j) (kronPowMatrix A j) := by
  induction j with
  | zero => intro i j h; exact absurd h (lt_irrefl 0)
  | succ j ih => exact (ih.kronecker hA).reindex finProdFinEquiv

/-- The graded diagonal part of the Kronecker power of a graded upper triangular matrix is the
Kronecker power of its graded diagonal part. -/
public theorem gradedDiag_kronPowMatrix {d : Fin s → ℤ} {A : Matrix (Fin s) (Fin s) R}
    (hA : IsGradedUpper d A) (j : ℕ) :
    gradedDiag (kronPowGrading d j) (kronPowMatrix A j) = kronPowMatrix (gradedDiag d A) j := by
  induction j with
  | zero =>
    ext I J
    simp [gradedDiag, kronPowGrading, kronPowMatrix]
  | succ j ih =>
    rw [kronPowMatrix_succ, kronPowMatrix_succ]
    change gradedDiag (_ ∘ finProdFinEquiv.symm) _ = _
    rw [gradedDiag_reindex, gradedDiag_kronecker ((IsGradedUpper.kronPowMatrix hA) j) hA, ih]

end Stacks.EtaleCohomology

end
