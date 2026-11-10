module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdealCochainModel

/-!
# Homotopy equivalence of complexes of finite free modules, in matrices

A homotopy equivalence between the cochain complexes presented by two
`Stacks.FittingComplex.FreeData` is, written out in the standard bases, four families of
matrices — the two comparison maps and the two homotopies — satisfying four families of
identities. This file records that data as `Stacks.FittingComplex.FreeData.MatrixHtpy`, extracts
it from a homotopy equivalence of the complexes, and proves the three operations on it that the
proof of [Stacks, Tag 0ESP] performs: composition, transport along a degreewise invertible change
of basis, and the cancellation of a contractible direct summand.

Matrices rather than morphisms, because the one step that is not formal — cancelling the trivial
two-term complex that [Stacks, Tag 00MT] splits off — is a computation with block matrices, and
because `Stacks.FittingComplex.FreeData.directSum` is block-diagonal on the nose, with no
reindexing of the ranks to transport.

## Main definitions

* `Stacks.FittingComplex.FreeData.MatrixHtpy`: the matrix data of a homotopy equivalence.
* `Stacks.FittingComplex.FreeData.IsMatrixContractible`: a matrix contraction of a complex, i.e.
  matrices `h` with `h_{i+1} d_{i+1} + d_i h_i = 1`.

## Main results

* `Stacks.FittingComplex.FreeData.MatrixHtpy.ofHomotopyEquiv`: the data of a homotopy equivalence
  of the cochain complexes.
* `Stacks.FittingComplex.FreeData.MatrixHtpy.symm` and `.trans`: the data is symmetric and
  composes.
* `Stacks.FittingComplex.FreeData.MatrixHtpy.ofConj`: a degreewise invertible change of basis
  intertwining the differentials gives such data.
* `Stacks.FittingComplex.FreeData.isMatrixContractible_trivialComplex`: the trivial two-term
  complex is contractible.
* `Stacks.FittingComplex.FreeData.MatrixHtpy.cancelLeftDirectSum`: a complex is related to
  anything its direct sum with a contractible complex is related to. This is the step that
  removes the summand [Stacks, Tag 00MT] splits off.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
* [Stacks Project, Tag 00MT](https://stacks.math.columbia.edu/tag/00MT)
-/

@[expose] public section

open CategoryTheory Matrix

namespace Stacks.FittingComplex.FreeData

universe u

variable {R : Type u} [CommRing R]

/-- The matrix data of a homotopy equivalence between the complexes presented by two
`FreeData`: the matrices `toMat` and `invMat` of the two comparison maps, and the matrices
`htpy₁`, `htpy₂` of the two homotopies, with `htpy i` sitting in the slot where a homotopy of a
cochain complex can be nonzero, from degree `i + 1` to degree `i`. -/
structure MatrixHtpy (C₁ C₂ : FreeData R) where
  /-- The matrix of the comparison map `C₁ → C₂` in degree `i`. -/
  toMat : ∀ i : ℤ, Matrix (Fin (C₂.rank i)) (Fin (C₁.rank i)) R
  /-- The matrix of the comparison map `C₂ → C₁` in degree `i`. -/
  invMat : ∀ i : ℤ, Matrix (Fin (C₁.rank i)) (Fin (C₂.rank i)) R
  /-- The matrix of the homotopy from `invMat ∘ toMat` to the identity. -/
  htpy₁ : ∀ i : ℤ, Matrix (Fin (C₁.rank i)) (Fin (C₁.rank (i + 1))) R
  /-- The matrix of the homotopy from `toMat ∘ invMat` to the identity. -/
  htpy₂ : ∀ i : ℤ, Matrix (Fin (C₂.rank i)) (Fin (C₂.rank (i + 1))) R
  /-- `toMat` is a morphism of complexes. -/
  toMat_comm : ∀ i : ℤ, C₂.d i * toMat i = toMat (i + 1) * C₁.d i
  /-- `invMat` is a morphism of complexes. -/
  invMat_comm : ∀ i : ℤ, C₁.d i * invMat i = invMat (i + 1) * C₂.d i
  /-- `invMat ∘ toMat` is homotopic to the identity. -/
  invMat_toMat : ∀ i : ℤ, invMat (i + 1) * toMat (i + 1)
    = htpy₁ (i + 1) * C₁.d (i + 1) + C₁.d i * htpy₁ i + 1
  /-- `toMat ∘ invMat` is homotopic to the identity. -/
  toMat_invMat : ∀ i : ℤ, toMat (i + 1) * invMat (i + 1)
    = htpy₂ (i + 1) * C₂.d (i + 1) + C₂.d i * htpy₂ i + 1

variable {C₁ C₂ C₃ : FreeData R}

/-- The inverse form of a degreewise invertible conjugation of the differentials. -/
theorem conj_inv
    {P : ∀ i : ℤ, Matrix (Fin (C₂.rank i)) (Fin (C₁.rank i)) R}
    {Q : ∀ i : ℤ, Matrix (Fin (C₁.rank i)) (Fin (C₂.rank i)) R}
    (hPQ : ∀ i : ℤ, P i * Q i = 1) (hQP : ∀ i : ℤ, Q i * P i = 1)
    (hconj : ∀ i : ℤ, C₂.d i * P i = P (i + 1) * C₁.d i) (i : ℤ) :
    C₁.d i * Q i = Q (i + 1) * C₂.d i := by
  calc C₁.d i * Q i = 1 * (C₁.d i * Q i) := (Matrix.one_mul _).symm
    _ = Q (i + 1) * P (i + 1) * (C₁.d i * Q i) := by rw [hQP (i + 1)]
    _ = Q (i + 1) * (P (i + 1) * C₁.d i) * Q i := by simp only [Matrix.mul_assoc]
    _ = Q (i + 1) * (C₂.d i * P i) * Q i := by rw [hconj i]
    _ = Q (i + 1) * C₂.d i * (P i * Q i) := by simp only [Matrix.mul_assoc]
    _ = Q (i + 1) * C₂.d i := by rw [hPQ i, Matrix.mul_one]

namespace MatrixHtpy

variable {C₁ C₂ C₃ : FreeData R}

/-- The data is symmetric: exchange the two comparison maps and the two homotopies. -/
def symm (e : MatrixHtpy C₁ C₂) : MatrixHtpy C₂ C₁ where
  toMat := e.invMat
  invMat := e.toMat
  htpy₁ := e.htpy₂
  htpy₂ := e.htpy₁
  toMat_comm := e.invMat_comm
  invMat_comm := e.toMat_comm
  invMat_toMat := e.toMat_invMat
  toMat_invMat := e.invMat_toMat

/-- The matrix data of a homotopy equivalence of the cochain complexes presented by two
`FreeData`. -/
noncomputable def ofHomotopyEquiv {hdd₁ : ∀ i : ℤ, C₁.d (i + 1) * C₁.d i = 0}
    {hdd₂ : ∀ i : ℤ, C₂.d (i + 1) * C₂.d i = 0}
    (e : HomotopyEquiv (C₁.toCochain hdd₁) (C₂.toCochain hdd₂)) : MatrixHtpy C₁ C₂ where
  toMat i := matrixOfHom (e.hom.f i)
  invMat i := matrixOfHom (e.inv.f i)
  htpy₁ i := matrixOfHom (e.homotopyHomInvId.hom (i + 1) i)
  htpy₂ i := matrixOfHom (e.homotopyInvHomId.hom (i + 1) i)
  toMat_comm i := matrixOfHom_d_comm C₁ C₂ hdd₁ hdd₂ e.hom i
  invMat_comm i := matrixOfHom_d_comm C₂ C₁ hdd₂ hdd₁ e.inv i
  invMat_toMat i := matrixOfHom_comp_eq C₁ C₂ hdd₁ hdd₂ e.hom e.inv e.homotopyHomInvId i
  toMat_invMat i := matrixOfHom_comp_eq C₂ C₁ hdd₂ hdd₁ e.inv e.hom e.homotopyInvHomId i

/-- A degreewise invertible change of basis intertwining the differentials transports the data:
if `C₂` is obtained from `C₁` by conjugating its differentials by `P`, then anything `C₁` is
related to, `C₂` is related to. -/
def ofConj (e : MatrixHtpy C₁ C₃)
    (P : ∀ i : ℤ, Matrix (Fin (C₂.rank i)) (Fin (C₁.rank i)) R)
    (Q : ∀ i : ℤ, Matrix (Fin (C₁.rank i)) (Fin (C₂.rank i)) R)
    (hPQ : ∀ i : ℤ, P i * Q i = 1) (hQP : ∀ i : ℤ, Q i * P i = 1)
    (hconj : ∀ i : ℤ, C₂.d i * P i = P (i + 1) * C₁.d i) : MatrixHtpy C₂ C₃ where
  toMat i := e.toMat i * Q i
  invMat i := P i * e.invMat i
  htpy₁ i := P i * e.htpy₁ i * Q (i + 1)
  htpy₂ := e.htpy₂
  toMat_comm i := by
    rw [← Matrix.mul_assoc, e.toMat_comm, Matrix.mul_assoc, conj_inv hPQ hQP hconj i,
      ← Matrix.mul_assoc]
  invMat_comm i := by
    rw [← Matrix.mul_assoc, hconj, Matrix.mul_assoc, e.invMat_comm, ← Matrix.mul_assoc]
  invMat_toMat i := by
    have hd := conj_inv hPQ hQP hconj (i + 1)
    calc P (i + 1) * e.invMat (i + 1) * (e.toMat (i + 1) * Q (i + 1))
        = P (i + 1) * (e.invMat (i + 1) * e.toMat (i + 1)) * Q (i + 1) := by
          simp only [Matrix.mul_assoc]
      _ = P (i + 1) * (e.htpy₁ (i + 1) * C₁.d (i + 1) + C₁.d i * e.htpy₁ i + 1) * Q (i + 1) := by
          rw [e.invMat_toMat i]
      _ = P (i + 1) * e.htpy₁ (i + 1) * (C₁.d (i + 1) * Q (i + 1))
            + P (i + 1) * C₁.d i * (e.htpy₁ i * Q (i + 1)) + P (i + 1) * Q (i + 1) := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.one_mul]
      _ = P (i + 1) * e.htpy₁ (i + 1) * Q (i + 1 + 1) * C₂.d (i + 1)
            + C₂.d i * (P i * e.htpy₁ i * Q (i + 1)) + 1 := by
          rw [hd, ← hconj i, hPQ (i + 1)]
          simp only [Matrix.mul_assoc]
  toMat_invMat i := by
    calc e.toMat (i + 1) * Q (i + 1) * (P (i + 1) * e.invMat (i + 1))
        = e.toMat (i + 1) * (Q (i + 1) * P (i + 1)) * e.invMat (i + 1) := by
          simp only [Matrix.mul_assoc]
      _ = e.toMat (i + 1) * e.invMat (i + 1) := by rw [hQP (i + 1), Matrix.mul_one]
      _ = e.htpy₂ (i + 1) * C₃.d (i + 1) + C₃.d i * e.htpy₂ i + 1 := e.toMat_invMat i

end MatrixHtpy

/-! ### The direct sum with a contractible complex

The ranks of `Stacks.FittingComplex.FreeData.directSum` are sums, and the index types below are
written as such sums rather than as `(C.directSum T).rank i`: the two are the same by definition,
but only the first form lets the block lemmas about `Matrix.fromBlocks` and `finSumFinEquiv`
apply. The data of a `MatrixHtpy` for `C.directSum T` is accepted in that spelling, the
conversion being by definition.
-/

variable (C T : FreeData R)

/-- The inclusion of the first summand of a direct sum, as a matrix. -/
def inclMat (i : ℤ) : Matrix (Fin (C.rank i + T.rank i)) (Fin (C.rank i)) R :=
  (Matrix.fromRows (1 : Matrix (Fin (C.rank i)) (Fin (C.rank i)) R)
    (0 : Matrix (Fin (T.rank i)) (Fin (C.rank i)) R)).submatrix finSumFinEquiv.symm id

/-- The projection onto the first summand of a direct sum, as a matrix. -/
def projMat (i : ℤ) : Matrix (Fin (C.rank i)) (Fin (C.rank i + T.rank i)) R :=
  (Matrix.fromCols (1 : Matrix (Fin (C.rank i)) (Fin (C.rank i)) R)
    (0 : Matrix (Fin (C.rank i)) (Fin (T.rank i)) R)).submatrix id finSumFinEquiv.symm

/-- A contraction of the second summand, read on the direct sum. -/
def contrMat (h : ∀ i : ℤ, Matrix (Fin (T.rank i)) (Fin (T.rank (i + 1))) R) (i : ℤ) :
    Matrix (Fin (C.rank i + T.rank i)) (Fin (C.rank (i + 1) + T.rank (i + 1))) R :=
  (Matrix.fromBlocks 0 0 0 (h i)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- The differential of a direct sum, with its ranks written as sums. It is the differential of
`Stacks.FittingComplex.FreeData.directSum` by definition. -/
def directSumD (i : ℤ) :
    Matrix (Fin (C.rank (i + 1) + T.rank (i + 1))) (Fin (C.rank i + T.rank i)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (C.d i) 0 0 (T.d i))

/-- `directSumD C T` is the differential of `C.directSum T`. -/
theorem directSumD_eq (i : ℤ) : directSumD C T i = (C.directSum T).d i := rfl

/-- Reindexing along `finSumFinEquiv.symm` is additive. -/
private theorem submatrix_finSumFinEquiv_add {a b c d : ℕ}
    (A B : Matrix (Fin a ⊕ Fin b) (Fin c ⊕ Fin d) R) :
    A.submatrix finSumFinEquiv.symm finSumFinEquiv.symm
      + B.submatrix finSumFinEquiv.symm finSumFinEquiv.symm
      = (A + B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl

/-- The projection onto the first summand is a left inverse of the inclusion. -/
@[simp]
theorem projMat_mul_inclMat (i : ℤ) : projMat C T i * inclMat C T i = 1 := by
  rw [projMat, inclMat, Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows]
  simp

/-- The inclusion of the first summand is a morphism of complexes. -/
theorem directSumD_mul_inclMat (i : ℤ) :
    directSumD C T i * inclMat C T i = inclMat C T (i + 1) * C.d i := by
  have h₁ : directSumD C T i * inclMat C T i
      = (Matrix.fromRows (C.d i) (0 : Matrix (Fin (T.rank (i + 1))) (Fin (C.rank i)) R)).submatrix
        finSumFinEquiv.symm id := by
    rw [directSumD, Matrix.reindex_apply, inclMat, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_mul_fromRows]
    simp
  have h₂ : inclMat C T (i + 1) * C.d i
      = (Matrix.fromRows (C.d i) (0 : Matrix (Fin (T.rank (i + 1))) (Fin (C.rank i)) R)).submatrix
        finSumFinEquiv.symm id := by
    rw [inclMat, ← Matrix.submatrix_id_id (C.d i),
      ← Matrix.submatrix_mul _ _ _ (id : Fin (C.rank (i + 1)) → Fin (C.rank (i + 1))) _
        Function.bijective_id, Matrix.fromRows_mul]
    simp
  rw [h₁, h₂]

/-- The projection onto the first summand is a morphism of complexes. -/
theorem d_mul_projMat (i : ℤ) :
    C.d i * projMat C T i = projMat C T (i + 1) * directSumD C T i := by
  have h₁ : C.d i * projMat C T i
      = (Matrix.fromCols (C.d i) (0 : Matrix (Fin (C.rank (i + 1))) (Fin (T.rank i)) R)).submatrix
        id finSumFinEquiv.symm := by
    rw [projMat, ← Matrix.submatrix_id_id (C.d i),
      ← Matrix.submatrix_mul _ _ _ (id : Fin (C.rank i) → Fin (C.rank i)) _
        Function.bijective_id, Matrix.mul_fromCols]
    simp
  have h₂ : projMat C T (i + 1) * directSumD C T i
      = (Matrix.fromCols (C.d i) (0 : Matrix (Fin (C.rank (i + 1))) (Fin (T.rank i)) R)).submatrix
        id finSumFinEquiv.symm := by
    rw [directSumD, Matrix.reindex_apply, projMat, Matrix.submatrix_mul_equiv,
      Matrix.fromCols_mul_fromBlocks]
    simp
  rw [h₁, h₂]

/-- The composite of the projection after the inclusion is the identity minus the part of the
identity that a contraction of the second summand realizes as a boundary. -/
theorem inclMat_mul_projMat (h : ∀ i : ℤ, Matrix (Fin (T.rank i)) (Fin (T.rank (i + 1))) R)
    (hT : ∀ i : ℤ, h (i + 1) * T.d (i + 1) + T.d i * h i = 1) (i : ℤ) :
    inclMat C T (i + 1) * projMat C T (i + 1)
      + (contrMat C T h (i + 1) * directSumD C T (i + 1)
        + directSumD C T i * contrMat C T h i) = 1 := by
  have h₁ : inclMat C T (i + 1) * projMat C T (i + 1)
      = (Matrix.fromBlocks (1 : Matrix (Fin (C.rank (i + 1))) (Fin (C.rank (i + 1))) R) 0 0
          (0 : Matrix (Fin (T.rank (i + 1))) (Fin (T.rank (i + 1))) R)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [inclMat, projMat,
      ← Matrix.submatrix_mul _ _ _ (id : Fin (C.rank (i + 1)) → Fin (C.rank (i + 1))) _
        Function.bijective_id, Matrix.fromRows_mul_fromCols]
    simp
  have h₂ : contrMat C T h (i + 1) * directSumD C T (i + 1)
      + directSumD C T i * contrMat C T h i
      = (Matrix.fromBlocks (0 : Matrix (Fin (C.rank (i + 1))) (Fin (C.rank (i + 1))) R) 0 0
          (1 : Matrix (Fin (T.rank (i + 1))) (Fin (T.rank (i + 1))) R)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [contrMat, contrMat, directSumD, directSumD, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, submatrix_finSumFinEquiv_add, Matrix.fromBlocks_add]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hT i]
  rw [h₁, h₂, submatrix_finSumFinEquiv_add, Matrix.fromBlocks_add]
  simp

/-! ### The trivial two-term complex is contractible -/

/-- The contraction of the trivial two-term complex: the identity, in coordinates, from degree
`i + 1` to degree `i`, and zero elsewhere. -/
def trivialContr (i : ℤ) (m : ℕ) (j : ℤ) :
    Matrix (Fin ((trivialComplex R i m).rank j)) (Fin ((trivialComplex R i m).rank (j + 1))) R :=
  if j = i then Matrix.of fun x y => if (x : ℕ) = (y : ℕ) then 1 else 0 else 0

/-- In the one degree where it is nonzero, the contraction of the trivial two-term complex is the
identity matrix, in coordinates. -/
private theorem trivialContr_self_apply (i : ℤ) (m : ℕ)
    (x : Fin ((trivialComplex R i m).rank i)) (y : Fin ((trivialComplex R i m).rank (i + 1))) :
    trivialContr (R := R) i m i x y = if (x : ℕ) = (y : ℕ) then (1 : R) else 0 := by
  rw [trivialContr, ite_eq_left rfl]
  rfl

/-- Outside that degree the contraction vanishes. -/
private theorem trivialContr_eq_zero (i : ℤ) (m : ℕ) {j : ℤ} (hj : j ≠ i) :
    trivialContr (R := R) i m j = 0 := ite_eq_right hj

/-- The two ranks of the trivial two-term complex that its differential connects are both `m`. -/
private theorem trivialComplex_rank_eq (i : ℤ) (m : ℕ) :
    (trivialComplex R i m).rank i = m ∧ (trivialComplex R i m).rank (i + 1) = m := by
  constructor <;> simp

/-- The differential of the trivial two-term complex composed with its contraction is the
identity. -/
private theorem trivialComplex_d_mul_trivialContr (i : ℤ) (m : ℕ) :
    (trivialComplex R i m).d i * trivialContr (R := R) i m i = 1 := by
  obtain ⟨h2, h1⟩ := trivialComplex_rank_eq (R := R) i m
  refine Matrix.ext fun x y => ?_
  have hxi : ((x : ℕ)) < (trivialComplex R i m).rank i := by have := x.isLt; omega
  have hzero : ∀ b : Fin ((trivialComplex R i m).rank i),
      b ≠ (⟨(x : ℕ), hxi⟩ : Fin ((trivialComplex R i m).rank i)) →
      (trivialComplex R i m).d i x b * trivialContr (R := R) i m i b y = 0 := by
    intro b hb
    rw [trivialComplex_d_self_apply, ite_eq_right fun hc => hb (Fin.ext hc.symm), zero_mul]
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem
      (⟨(x : ℕ), hxi⟩ : Fin ((trivialComplex R i m).rank i)) (Finset.mem_univ _)
      (fun b _ hb => hzero b hb),
    trivialComplex_d_self_apply, trivialContr_self_apply, ite_eq_left rfl, one_mul,
    Matrix.one_apply]
  exact if_congr (show ((x : ℕ)) = ((y : ℕ)) ↔ x = y from Fin.val_eq_val x y) rfl rfl

/-- The contraction of the trivial two-term complex composed with its differential is the
identity. -/
private theorem trivialContr_mul_trivialComplex_d (i : ℤ) (m : ℕ) :
    trivialContr (R := R) i m i * (trivialComplex R i m).d i = 1 := by
  obtain ⟨h2, h1⟩ := trivialComplex_rank_eq (R := R) i m
  refine Matrix.ext fun x y => ?_
  have hxi : ((x : ℕ)) < (trivialComplex R i m).rank (i + 1) := by have := x.isLt; omega
  have hzero : ∀ b : Fin ((trivialComplex R i m).rank (i + 1)),
      b ≠ (⟨(x : ℕ), hxi⟩ : Fin ((trivialComplex R i m).rank (i + 1))) →
      trivialContr (R := R) i m i x b * (trivialComplex R i m).d i b y = 0 := by
    intro b hb
    rw [trivialContr_self_apply, ite_eq_right fun hc => hb (Fin.ext hc.symm), zero_mul]
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem
      (⟨(x : ℕ), hxi⟩ : Fin ((trivialComplex R i m).rank (i + 1))) (Finset.mem_univ _)
      (fun b _ hb => hzero b hb),
    trivialContr_self_apply, trivialComplex_d_self_apply, ite_eq_left rfl, one_mul,
    Matrix.one_apply]
  exact if_congr (show ((x : ℕ)) = ((y : ℕ)) ↔ x = y from Fin.val_eq_val x y) rfl rfl

/-- **The trivial two-term complex is contractible**: its identity is the boundary of the
contraction. -/
theorem trivialContr_spec (i : ℤ) (m : ℕ) (j : ℤ) :
    trivialContr (R := R) i m (j + 1) * (trivialComplex R i m).d (j + 1)
      + (trivialComplex R i m).d j * trivialContr (R := R) i m j = 1 := by
  by_cases hj : j = i
  · subst hj
    rw [trivialContr_eq_zero j m (by omega), Matrix.zero_mul, zero_add,
      trivialComplex_d_mul_trivialContr]
  · by_cases hj' : j + 1 = i
    · obtain rfl : i = j + 1 := hj'.symm
      rw [show (trivialComplex R (j + 1) m).d j = 0 from
          Matrix.ext fun x y => trivialComplex_d_eq_zero (j + 1) j m hj x y,
        Matrix.zero_mul, add_zero, trivialContr_mul_trivialComplex_d]
    · have hzero : (trivialComplex R i m).rank (j + 1) = 0 :=
        trivialRank_eq_zero m hj' (by omega)
      exact Matrix.ext fun x y => absurd x.isLt (by omega)

/-- **Cancelling a contractible direct summand.** The data of a homotopy equivalence between
`C ⊕ T` and `Z`, with `T` contractible, gives one between `C` and `Z`: compose with the inclusion
and the projection, and correct the homotopy on the `Z` side by the contraction of `T`.

The data is taken unbundled so that the ranks of the direct sum can be written as sums, which is
what the block lemmas need; a `MatrixHtpy (C.directSum T) Z` provides it, its fields having that
type by definition. -/
def MatrixHtpy.ofDirectSum (Z : FreeData R)
    (F : ∀ i : ℤ, Matrix (Fin (Z.rank i)) (Fin (C.rank i + T.rank i)) R)
    (G : ∀ i : ℤ, Matrix (Fin (C.rank i + T.rank i)) (Fin (Z.rank i)) R)
    (H₁ : ∀ i : ℤ, Matrix (Fin (C.rank i + T.rank i))
      (Fin (C.rank (i + 1) + T.rank (i + 1))) R)
    (H₂ : ∀ i : ℤ, Matrix (Fin (Z.rank i)) (Fin (Z.rank (i + 1))) R)
    (hF : ∀ i : ℤ, Z.d i * F i = F (i + 1) * directSumD C T i)
    (hG : ∀ i : ℤ, directSumD C T i * G i = G (i + 1) * Z.d i)
    (hGF : ∀ i : ℤ, G (i + 1) * F (i + 1)
      = H₁ (i + 1) * directSumD C T (i + 1) + directSumD C T i * H₁ i + 1)
    (hFG : ∀ i : ℤ, F (i + 1) * G (i + 1) = H₂ (i + 1) * Z.d (i + 1) + Z.d i * H₂ i + 1)
    (h : ∀ i : ℤ, Matrix (Fin (T.rank i)) (Fin (T.rank (i + 1))) R)
    (hT : ∀ i : ℤ, h (i + 1) * T.d (i + 1) + T.d i * h i = 1) : MatrixHtpy C Z where
  toMat i := F i * inclMat C T i
  invMat i := projMat C T i * G i
  htpy₁ i := projMat C T i * H₁ i * inclMat C T (i + 1)
  htpy₂ i := H₂ i - F i * contrMat C T h i * G (i + 1)
  toMat_comm i := by
    rw [← Matrix.mul_assoc, hF, Matrix.mul_assoc, directSumD_mul_inclMat, ← Matrix.mul_assoc]
  invMat_comm i := by
    rw [← Matrix.mul_assoc, d_mul_projMat, Matrix.mul_assoc, hG, ← Matrix.mul_assoc]
  invMat_toMat i := by
    calc projMat C T (i + 1) * G (i + 1) * (F (i + 1) * inclMat C T (i + 1))
        = projMat C T (i + 1) * (G (i + 1) * F (i + 1)) * inclMat C T (i + 1) := by
          simp only [Matrix.mul_assoc]
      _ = projMat C T (i + 1)
            * (H₁ (i + 1) * directSumD C T (i + 1) + directSumD C T i * H₁ i + 1)
            * inclMat C T (i + 1) := by rw [hGF i]
      _ = projMat C T (i + 1) * H₁ (i + 1) * (directSumD C T (i + 1) * inclMat C T (i + 1))
            + projMat C T (i + 1) * directSumD C T i * (H₁ i * inclMat C T (i + 1))
            + projMat C T (i + 1) * inclMat C T (i + 1) := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_one]
      _ = projMat C T (i + 1) * H₁ (i + 1) * inclMat C T (i + 1 + 1) * C.d (i + 1)
            + C.d i * (projMat C T i * H₁ i * inclMat C T (i + 1)) + 1 := by
          rw [directSumD_mul_inclMat, ← d_mul_projMat, projMat_mul_inclMat]
          simp only [Matrix.mul_assoc]
  toMat_invMat i := by
    have hincl : inclMat C T (i + 1) * projMat C T (i + 1)
        = 1 - (contrMat C T h (i + 1) * directSumD C T (i + 1)
          + directSumD C T i * contrMat C T h i) :=
      eq_sub_of_add_eq (inclMat_mul_projMat C T h hT i)
    calc F (i + 1) * inclMat C T (i + 1) * (projMat C T (i + 1) * G (i + 1))
        = F (i + 1) * (inclMat C T (i + 1) * projMat C T (i + 1)) * G (i + 1) := by
          simp only [Matrix.mul_assoc]
      _ = F (i + 1) * (1 - (contrMat C T h (i + 1) * directSumD C T (i + 1)
            + directSumD C T i * contrMat C T h i)) * G (i + 1) := by rw [hincl]
      _ = F (i + 1) * G (i + 1)
            - (F (i + 1) * contrMat C T h (i + 1) * (directSumD C T (i + 1) * G (i + 1))
              + F (i + 1) * directSumD C T i * (contrMat C T h i * G (i + 1))) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
            Matrix.mul_one, Matrix.mul_assoc]
      _ = (H₂ (i + 1) - F (i + 1) * contrMat C T h (i + 1) * G (i + 1 + 1)) * Z.d (i + 1)
            + Z.d i * (H₂ i - F i * contrMat C T h i * G (i + 1)) + 1 := by
          rw [hFG i, hG (i + 1), ← hF i]
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
          abel

end Stacks.FittingComplex.FreeData

end
