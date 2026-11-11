module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Block matrices indexed by `Fin (n + m)`

For square matrices indexed by `Fin (n + m)` we write `(A, B; C, D)` for the block matrix whose
first `m` rows and columns carry `A`, and record the facts on products, determinants, upper
triangularity and integrality of entries used in the reduction theory of `GL_n` of the adeles:

* `Stacks.Adeles.GeneralLinear.blockEquiv` — `Fin m ⊕ Fin n ≃ Fin (n + m)`;
* `Stacks.Adeles.GeneralLinear.blockMat` — the block matrix `(A, B; C, D)`;
* `Stacks.Adeles.GeneralLinear.blockLeftGL`, `Stacks.Adeles.GeneralLinear.blockRightGL` — the
  embeddings `g ↦ (g, 0; 0, 1)` and `g ↦ (1, 0; 0, g)` of general linear groups;
* `Stacks.Adeles.GeneralLinear.mem_range_map_subtype_iff` — an invertible matrix comes from
  `GL_n(S)`, `S` a subring, exactly when it and its inverse have entries in `S`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.Adeles.GeneralLinear

variable {R : Type*} {m n : ℕ}

variable (m n) in
/-- `Fin m ⊕ Fin n ≃ Fin (n + m)`: the first `m` indices, then the last `n`. -/
public def blockEquiv : Fin m ⊕ Fin n ≃ Fin (n + m) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm m n))

/-- The index `inl i` is `i`. -/
@[simp]
public theorem blockEquiv_inl_val (i : Fin m) : (blockEquiv m n (Sum.inl i) : ℕ) = i := rfl

/-- The index `inr j` is `m + j`. -/
@[simp]
public theorem blockEquiv_inr_val (j : Fin n) : (blockEquiv m n (Sum.inr j) : ℕ) = m + j := rfl

/-- The block matrix `(A, B; C, D)`, indexed by `Fin (n + m)`. -/
public def blockMat (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin m) R) (D : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + m)) (Fin (n + m)) R :=
  reindex (blockEquiv m n) (blockEquiv m n) (fromBlocks A B C D)

section Apply

variable (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
  (C : Matrix (Fin n) (Fin m) R) (D : Matrix (Fin n) (Fin n) R)

/-- The `(inl i, inl j)` entry of `(A, B; C, D)` is `A i j`. -/
@[simp]
public theorem blockMat_inl_inl (i j : Fin m) :
    blockMat A B C D (blockEquiv m n (Sum.inl i)) (blockEquiv m n (Sum.inl j)) = A i j := by
  simp [blockMat]

/-- The `(inl i, inr j)` entry of `(A, B; C, D)` is `B i j`. -/
@[simp]
public theorem blockMat_inl_inr (i : Fin m) (j : Fin n) :
    blockMat A B C D (blockEquiv m n (Sum.inl i)) (blockEquiv m n (Sum.inr j)) = B i j := by
  simp [blockMat]

/-- The `(inr i, inl j)` entry of `(A, B; C, D)` is `C i j`. -/
@[simp]
public theorem blockMat_inr_inl (i : Fin n) (j : Fin m) :
    blockMat A B C D (blockEquiv m n (Sum.inr i)) (blockEquiv m n (Sum.inl j)) = C i j := by
  simp [blockMat]

/-- The `(inr i, inr j)` entry of `(A, B; C, D)` is `D i j`. -/
@[simp]
public theorem blockMat_inr_inr (i j : Fin n) :
    blockMat A B C D (blockEquiv m n (Sum.inr i)) (blockEquiv m n (Sum.inr j)) = D i j := by
  simp [blockMat]

end Apply

/-- Every matrix indexed by `Fin (n + m)` is the block matrix of its four blocks. -/
public theorem eq_blockMat (M : Matrix (Fin (n + m)) (Fin (n + m)) R) :
    M = blockMat (of fun i j => M (blockEquiv m n (Sum.inl i)) (blockEquiv m n (Sum.inl j)))
      (of fun i j => M (blockEquiv m n (Sum.inl i)) (blockEquiv m n (Sum.inr j)))
      (of fun i j => M (blockEquiv m n (Sum.inr i)) (blockEquiv m n (Sum.inl j)))
      (of fun i j => M (blockEquiv m n (Sum.inr i)) (blockEquiv m n (Sum.inr j))) := by
  ext i j
  obtain ⟨s, rfl⟩ := (blockEquiv m n).surjective i
  obtain ⟨t, rfl⟩ := (blockEquiv m n).surjective j
  rcases s with s | s <;> rcases t with t | t
  · rw [blockMat_inl_inl, of_apply]
  · rw [blockMat_inl_inr, of_apply]
  · rw [blockMat_inr_inl, of_apply]
  · rw [blockMat_inr_inr, of_apply]

variable [CommRing R]

/-- Block matrices multiply blockwise. -/
public theorem blockMat_mul (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin m) R) (D : Matrix (Fin n) (Fin n) R)
    (A' : Matrix (Fin m) (Fin m) R) (B' : Matrix (Fin m) (Fin n) R)
    (C' : Matrix (Fin n) (Fin m) R) (D' : Matrix (Fin n) (Fin n) R) :
    blockMat A B C D * blockMat A' B' C' D' =
      blockMat (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  simp only [blockMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]

/-- `(1, 0; 0, 1) = 1`. -/
public theorem blockMat_one :
    blockMat (1 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin m) (Fin n) R) 0 1 = 1 := by
  simp only [blockMat, fromBlocks_one, reindex_apply, submatrix_one_equiv]

/-- `det (A, B; 0, D) = det A · det D`. -/
public theorem det_blockMat_zero (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (D : Matrix (Fin n) (Fin n) R) : (blockMat A B 0 D).det = A.det * D.det := by
  rw [blockMat, det_reindex_self, det_fromBlocks_zero₂₁]

/-- `(A, B; 0, D)` is upper triangular when `A` and `D` are. -/
public theorem blockMat_upperTriangular {A : Matrix (Fin m) (Fin m) R}
    (B : Matrix (Fin m) (Fin n) R) {D : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i j, j < i → A i j = 0) (hD : ∀ i j, j < i → D i j = 0) :
    ∀ i j, j < i → blockMat A B 0 D i j = 0 := by
  intro i j hij
  obtain ⟨s, rfl⟩ := (blockEquiv m n).surjective i
  obtain ⟨t, rfl⟩ := (blockEquiv m n).surjective j
  rw [Fin.lt_def] at hij
  rcases s with s | s <;> rcases t with t | t
  · rw [blockMat_inl_inl]
    exact hA s t (Fin.lt_def.2 (by simpa using hij))
  · simp only [blockEquiv_inl_val, blockEquiv_inr_val] at hij
    omega
  · simp
  · rw [blockMat_inr_inr]
    exact hD s t (Fin.lt_def.2 (by simp only [blockEquiv_inr_val] at hij; omega))

/-- A `1 × 1` matrix is upper triangular. -/
public theorem upperTriangular_fin_one (A : Matrix (Fin 1) (Fin 1) R) :
    ∀ i j, j < i → A i j = 0 := fun i j h =>
  absurd h (by rw [Subsingleton.elim i j]; exact lt_irrefl _)

/-- The entries of `(A, B; C, D)` lie in a subring when those of the four blocks do. -/
public theorem blockMat_mem {S : Subring R} {A : Matrix (Fin m) (Fin m) R}
    {B : Matrix (Fin m) (Fin n) R} {C : Matrix (Fin n) (Fin m) R} {D : Matrix (Fin n) (Fin n) R}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (hC : ∀ i j, C i j ∈ S)
    (hD : ∀ i j, D i j ∈ S) : ∀ i j, blockMat A B C D i j ∈ S := by
  intro i j
  obtain ⟨s, rfl⟩ := (blockEquiv m n).surjective i
  obtain ⟨t, rfl⟩ := (blockEquiv m n).surjective j
  rcases s with s | s <;> rcases t with t | t <;> simp [hA, hB, hC, hD]

/-- The entries of `1` lie in every subring. -/
public theorem one_mem_entries {ι : Type*} [DecidableEq ι] (S : Subring R) (i j : ι) :
    (1 : Matrix ι ι R) i j ∈ S := by
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

/-- The entries of `0` lie in every subring. -/
public theorem zero_mem_entries {ι κ : Type*} (S : Subring R) (i : ι) (j : κ) :
    (0 : Matrix ι κ R) i j ∈ S := S.zero_mem

/-- The entries of a product lie in a subring when those of the factors do. -/
public theorem mul_mem_entries {ι κ μ : Type*} [Fintype κ] {S : Subring R} {M : Matrix ι κ R}
    {N : Matrix κ μ R} (hM : ∀ i j, M i j ∈ S) (hN : ∀ i j, N i j ∈ S) :
    ∀ i j, (M * N) i j ∈ S := fun i j =>
  S.sum_mem fun l _ => S.mul_mem (hM i l) (hN l j)

variable (R m n) in
/-- `g ↦ (g, 0; 0, 1)` on matrices. -/
public def blockLeft : Matrix (Fin m) (Fin m) R →* Matrix (Fin (n + m)) (Fin (n + m)) R where
  toFun g := blockMat g 0 0 1
  map_one' := blockMat_one
  map_mul' g g' := by rw [blockMat_mul]; simp

variable (R m n) in
/-- `g ↦ (1, 0; 0, g)` on matrices. -/
public def blockRight : Matrix (Fin n) (Fin n) R →* Matrix (Fin (n + m)) (Fin (n + m)) R where
  toFun g := blockMat 1 0 0 g
  map_one' := blockMat_one
  map_mul' g g' := by rw [blockMat_mul]; simp

variable (R m n) in
/-- `g ↦ (g, 0; 0, 1)` on general linear groups. -/
public def blockLeftGL : GL (Fin m) R →* GL (Fin (n + m)) R := Units.map (blockLeft R m n)

variable (R m n) in
/-- `g ↦ (1, 0; 0, g)` on general linear groups. -/
public def blockRightGL : GL (Fin n) R →* GL (Fin (n + m)) R := Units.map (blockRight R m n)

/-- The matrix of `blockLeftGL g` is `(g, 0; 0, 1)`. -/
@[simp]
public theorem coe_blockLeftGL (g : GL (Fin m) R) :
    ((blockLeftGL R m n g : GL (Fin (n + m)) R) : Matrix (Fin (n + m)) (Fin (n + m)) R) =
      blockMat (g : Matrix (Fin m) (Fin m) R) 0 0 1 := rfl

/-- The matrix of `blockRightGL g` is `(1, 0; 0, g)`. -/
@[simp]
public theorem coe_blockRightGL (g : GL (Fin n) R) :
    ((blockRightGL R m n g : GL (Fin (n + m)) R) : Matrix (Fin (n + m)) (Fin (n + m)) R) =
      blockMat 1 0 0 (g : Matrix (Fin n) (Fin n) R) := rfl

/-- An element of `GL_ι(R)` comes from `GL_ι(S)`, `S` a subring, exactly when it and its inverse
have all their entries in `S`. -/
public theorem mem_range_map_subtype_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Subring R)
    (g : GL ι R) : g ∈ (GeneralLinearGroup.map S.subtype).range ↔
      (∀ i j, (g : Matrix ι ι R) i j ∈ S) ∧ ∀ i j, ((g⁻¹ : GL ι R) : Matrix ι ι R) i j ∈ S := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Matrix.GeneralLinearGroup.map_apply]; exact (h i j).2
    · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]; exact (h⁻¹ i j).2
  · rintro ⟨h1, h2⟩
    let M : Matrix ι ι S := Matrix.of fun i j => ⟨_, h1 i j⟩
    let M' : Matrix ι ι S := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hinj : Function.Injective (S.subtype.mapMatrix : Matrix ι ι S →+* Matrix ι ι R) :=
      fun P Q hPQ => by
        ext i j
        exact congrFun (congrFun hPQ i) j
    have hM : S.subtype.mapMatrix M = (g : Matrix ι ι R) := by ext; rfl
    have hM' : S.subtype.mapMatrix M' = ((g⁻¹ : GL ι R) : Matrix ι ι R) := by ext; rfl
    have e1 : M * M' = 1 := hinj (by rw [map_mul, map_one, hM, hM']; exact g.mul_inv)
    have e2 : M' * M = 1 := hinj (by rw [map_mul, map_one, hM, hM']; exact g.inv_mul)
    refine ⟨⟨M, M', e1, e2⟩, Units.ext ?_⟩
    rw [← hM]
    rfl

/-- A square matrix whose entries below the diagonal vanish has a unit on the diagonal at every
index, when it is invertible. -/
public theorem isUnit_diag_of_upperTriangular {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : GL ι R) (hb : ∀ i j, j < i → (b : Matrix ι ι R) i j = 0) (i : ι) :
    IsUnit ((b : Matrix ι ι R) i i) := by
  have hdet : IsUnit (b : Matrix ι ι R).det := (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
  rw [det_of_isUpperTriangular (fun i j h => hb i j h)] at hdet
  exact IsUnit.prod_univ_iff.1 hdet i

end Stacks.Adeles.GeneralLinear

end
