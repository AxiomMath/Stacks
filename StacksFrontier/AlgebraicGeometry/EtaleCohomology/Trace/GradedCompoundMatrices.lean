module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GradedTriangularMatrices
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerRepresentation

/-!
# Determinants, characteristic polynomials and compound matrices of graded triangular matrices

The determinant of a graded upper triangular matrix is that of its graded diagonal part, so the
two have the same characteristic polynomial: a representation and its semisimplification along a
flag have the same Frobenius characteristic polynomials.  The `k`-th compound matrix of a graded
upper triangular matrix is graded upper triangular for the grading `S ↦ ∑_{s ∈ S} d s` of the
`k`-element subsets, and its graded diagonal part is the compound matrix of the graded diagonal
part: exterior powers commute with semisimplification.

## Main results

* `Stacks.EtaleCohomology.det_eq_det_ite_of_sum_eq`,
  `Stacks.EtaleCohomology.det_eq_zero_of_sum_lt`: determinants of matrices graded by a row and a
  column grading.
* `Stacks.EtaleCohomology.charpoly_gradedDiag`: a graded upper triangular matrix and its graded
  diagonal part have the same characteristic polynomial.
* `Stacks.EtaleCohomology.IsGradedUpper.compound`: the compound matrix of a graded upper
  triangular matrix is graded upper triangular.
* `Stacks.EtaleCohomology.gradedDiag_compound`: the graded diagonal part of the compound matrix
  is the compound matrix of the graded diagonal part.
-/

@[expose] public noncomputable section

open Matrix Polynomial Set.powersetCard

namespace Stacks.EtaleCohomology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]

omit [DecidableEq ι] in
/-- If `B` is graded by `a` on rows and `b` on columns and every factor of the Leibniz term of
`σ` is nonzero, then `a (σ i) ≤ b i` for all `i`. -/
theorem le_of_prod_ne_zero {a b : ι → ℤ} {B : Matrix ι ι R} (hB : ∀ i j, b j < a i → B i j = 0)
    {σ : Equiv.Perm ι} (h : ∏ i, B (σ i) i ≠ 0) (i : ι) : a (σ i) ≤ b i := by
  by_contra hlt
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) (hB _ _ (not_le.mp hlt)))

/-- If `∑ b ≤ ∑ a` and a Leibniz term of a matrix graded by `a` and `b` is nonzero, then the
permutation matches the grades: `a (σ i) = b i` for all `i`. -/
private theorem grade_eq_of_prod_ne_zero {κ : Type*} [Fintype κ] {a b : κ → ℤ}
    {B : Matrix κ κ R} (hB : ∀ i j, b j < a i → B i j = 0) (h : ∑ i, b i ≤ ∑ i, a i)
    {σ : Equiv.Perm κ} (hσ : ∏ i, B (σ i) i ≠ 0) (i : κ) : a (σ i) = b i :=
  (Finset.sum_eq_sum_iff_of_le fun i _ => le_of_prod_ne_zero hB hσ i).1
    (le_antisymm (Finset.sum_le_sum fun i _ => le_of_prod_ne_zero hB hσ i)
      (by rwa [Equiv.sum_comp σ a])) i (Finset.mem_univ i)

/-- **A determinant graded by rows and columns with `∑ b < ∑ a` vanishes.** -/
public theorem det_eq_zero_of_sum_lt {a b : ι → ℤ} {B : Matrix ι ι R}
    (hB : ∀ i j, b j < a i → B i j = 0) (h : ∑ i, b i < ∑ i, a i) : B.det = 0 := by
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  by_cases hp : ∏ i, B (σ i) i = 0
  · rw [hp, smul_zero]
  · have : ∑ i, a (σ i) = ∑ i, b i :=
      Finset.sum_congr rfl fun i _ => grade_eq_of_prod_ne_zero hB h.le hp i
    rw [Equiv.sum_comp σ a] at this
    omega

/-- **A determinant graded by rows and columns with `∑ a = ∑ b` only sees the entries of matching
grades.** -/
public theorem det_eq_det_ite_of_sum_eq {a b : ι → ℤ} {B : Matrix ι ι R}
    (hB : ∀ i j, b j < a i → B i j = 0) (h : ∑ i, a i = ∑ i, b i) :
    B.det = (Matrix.of fun i j => if a i = b j then B i j else 0).det := by
  rw [Matrix.det_apply, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases heq : ∀ i, a (σ i) = b i
  · congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [heq i]
  · push Not at heq
    obtain ⟨i, hi⟩ := heq
    have hM : ∏ j, (Matrix.of fun i j => if a i = b j then B i j else 0) (σ j) j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    have hBp : ∏ i, B (σ i) i = 0 :=
      not_not.1 fun hp => hi (grade_eq_of_prod_ne_zero hB h.ge hp i)
    rw [hM, hBp]

/-- The determinant of a matrix of matching grades vanishes unless `∑ a = ∑ b`. -/
public theorem det_ite_eq_zero_of_sum_ne {a b : ι → ℤ} {B : Matrix ι ι R}
    (h : ∑ i, a i ≠ ∑ i, b i) :
    (Matrix.of fun i j => if a i = b j then B i j else 0).det = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · refine det_eq_zero_of_sum_lt (a := fun i => -a i) (b := fun j => -b j) (fun i j hij => ?_) ?_
    · rw [Matrix.of_apply, ite_eq_right (by omega)]
    · simp only [Finset.sum_neg_distrib]
      omega
  · exact det_eq_zero_of_sum_lt (a := a) (b := b)
      (fun i j hij => by rw [Matrix.of_apply, ite_eq_right (by omega)]) h

variable {d : ι → ℤ}

/-- **The determinant of a graded upper triangular matrix is that of its graded diagonal part.** -/
public theorem det_gradedDiag {T : Matrix ι ι R} (hT : IsGradedUpper d T) :
    (gradedDiag d T).det = T.det :=
  (det_eq_det_ite_of_sum_eq hT rfl).symm

/-- **A graded upper triangular matrix and its graded diagonal part have the same characteristic
polynomial.** -/
public theorem charpoly_gradedDiag {T : Matrix ι ι R} (hT : IsGradedUpper d T) :
    (gradedDiag d T).charpoly = T.charpoly := by
  have hc : IsGradedUpper d T.charmatrix := by
    intro i j hij
    have hne : i ≠ j := fun h => (lt_irrefl _) (h ▸ hij)
    rw [Matrix.charmatrix_apply_ne _ _ _ hne, hT i j hij, map_zero, neg_zero]
  have he : gradedDiag d T.charmatrix = (gradedDiag d T).charmatrix := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [gradedDiag, Matrix.charmatrix_apply_eq]
    · rw [Matrix.charmatrix_apply_ne _ _ _ hij]
      simp only [gradedDiag]
      split_ifs <;> simp [Matrix.charmatrix_apply_ne _ _ _ hij]
  rw [Matrix.charpoly, Matrix.charpoly, ← he, det_gradedDiag hc]

section Compound

variable {n : ℕ} (k : ℕ) {d : Fin n → ℤ}

/-- The grading of the `k`-element subsets: `S ↦ ∑_{s ∈ S} d s`. -/
public def subsetGrading (d : Fin n → ℤ) (S : Set.powersetCard (Fin n) k) : ℤ :=
  ∑ s ∈ (S : Finset (Fin n)), d s

/-- The sum of `d` over the increasing enumeration of a `k`-element subset `S` is the grading of
`S`. -/
theorem sum_ofFinEmbEquiv_symm (S : Set.powersetCard (Fin n) k) :
    ∑ i, d (ofFinEmbEquiv.symm S i) = subsetGrading k d S := by
  rw [subsetGrading, ofFinEmbEquiv_symm_apply]
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ (S : Finset (Fin n)) S.2, Finset.sum_map]
  rfl

/-- **The compound matrix of a graded upper triangular matrix is graded upper triangular** for the
grading `S ↦ ∑_{s ∈ S} d s`. -/
public theorem IsGradedUpper.compound {A : Matrix (Fin n) (Fin n) R} (hA : IsGradedUpper d A) :
    IsGradedUpper (subsetGrading k d) (compoundMonoidHom k A) := by
  intro T S hTS
  rw [compoundMonoidHom_apply_apply]
  refine det_eq_zero_of_sum_lt (a := fun i => d (ofFinEmbEquiv.symm T i))
    (b := fun j => d (ofFinEmbEquiv.symm S j)) (fun i j hij => hA _ _ hij) ?_
  simp only [sum_ofFinEmbEquiv_symm]
  exact hTS

/-- **Exterior powers commute with semisimplification**: the graded diagonal part of the compound
matrix of a graded upper triangular matrix is the compound matrix of its graded diagonal part. -/
public theorem gradedDiag_compound {A : Matrix (Fin n) (Fin n) R} (hA : IsGradedUpper d A) :
    gradedDiag (subsetGrading k d) (compoundMonoidHom k A) =
      compoundMonoidHom k (gradedDiag d A) := by
  ext T S
  rw [compoundMonoidHom_apply_apply]
  have hsub : (gradedDiag d A).submatrix (ofFinEmbEquiv.symm T) (ofFinEmbEquiv.symm S) =
      Matrix.of fun i j => if d (ofFinEmbEquiv.symm T i) = d (ofFinEmbEquiv.symm S j) then
        A.submatrix (ofFinEmbEquiv.symm T) (ofFinEmbEquiv.symm S) i j else 0 := by
    ext i j
    rfl
  rw [hsub]
  simp only [gradedDiag]
  split_ifs with h
  · rw [compoundMonoidHom_apply_apply]
    exact det_eq_det_ite_of_sum_eq (a := fun i => d (ofFinEmbEquiv.symm T i))
      (b := fun j => d (ofFinEmbEquiv.symm S j)) (fun i j hij => hA _ _ hij)
      (by simp only [sum_ofFinEmbEquiv_symm]; exact h)
  · exact (det_ite_eq_zero_of_sum_ne (a := fun i => d (ofFinEmbEquiv.symm T i))
      (b := fun j => d (ofFinEmbEquiv.symm S j))
      (by simp only [sum_ofFinEmbEquiv_symm]; exact h)).symm

end Compound

end Stacks.EtaleCohomology

end
