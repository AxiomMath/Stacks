module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Linear algebra over commutative semirings

`Matrix.Nonsingular` and the resulting `StrongRankCondition` instance for nontrivial
commutative semirings used to live here; they are now in Mathlib, phrased via
`Matrix.IsDetpBalanced`. What remains are the `SubRegular` API and the permutation and
signed-part determinant lemmas that Mathlib does not carry, plus
`Matrix.nonsingular_iff_subRegular` relating the two formulations. -/

@[expose] public section

open Module Matrix Finset Equiv Perm

attribute [simp] isRegular_one

/-- Unfolding of `Equiv.arrowCongr` as composition with `e₂` on the left and `e₁.symm` on
the right. -/
@[simp] theorem Equiv.arrowCongr_apply' {α₁ β₁ α₂ β₂ : Sort*}
    (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (f : α₁ → β₁) : e₁.arrowCongr e₂ f = e₂ ∘ f ∘ e₁.symm :=
  rfl

/-- `SubRegular p q` is the semiring-friendly version of "`p - q` is right-regular" (i.e. a
non-zero-divisor): the implication `a * p + b * q = b * p + a * q → a = b` for all `a, b`.
Over a ring this is equivalent to `IsRightRegular (p - q)`; in the symmetrized-semiring
literature (Plus 1990, Butkovič–Gaubert 1999) this corresponds to `p` and `q` being
"unbalanced" in the symmetrized semiring `R²`. -/
@[grind] def SubRegular {R : Type*} [Add R] [Mul R] (p q : R) : Prop :=
  ∀ {a b}, a * p + b * q = b * p + a * q → a = b

namespace SubRegular

/-- If `p` and `q` are sub-regular in a nontrivial semiring then `p ≠ q`. -/
@[grind ., simp] theorem ne {R : Type*} [NonAssocSemiring R] [Nontrivial R] {p q : R}
    (h : SubRegular p q) : p ≠ q :=
  fun heq ↦ one_ne_zero <| h <| by grind

/-- Over a subsingleton carrier, every pair is sub-regular vacuously. -/
@[grind ., simp] theorem of_subsingleton {R : Type*} [Subsingleton R] [Add R] [Mul R] {p q : R} :
    SubRegular p q := fun _ ↦ Subsingleton.elim _ _

/-- Sub-regularity is symmetric: `SubRegular p q → SubRegular q p`. -/
@[grind .] theorem symm {R : Type*} [AddCommMagma R] [Mul R] {p q : R} (h : SubRegular p q) :
    SubRegular q p := fun {a b} heq ↦ h <| by grind [add_comm]

/-- Sub-regularity is symmetric in `p` and `q`. -/
@[grind .] theorem comm {R : Type*} [AddCommMagma R] [Mul R] (p q : R) :
    SubRegular p q ↔ SubRegular q p := ⟨symm, symm⟩

end SubRegular

/-- Over a ring, sub-regularity of `(p, q)` reduces to sub-regularity of `(p - q, 0)`. -/
theorem subRegular_iff_sub {R : Type*} [NonUnitalNonAssocRing R] (p q : R) :
    SubRegular p q ↔ SubRegular (p - q) 0 := by
  simp [SubRegular, mul_sub, eq_sub_iff_add_eq, sub_add_eq_add_sub]
  grind

/-- `SubRegular p 0` is exactly `IsRightRegular p`. -/
@[simp] theorem subRegular_zero_right_iff_rightRegular {R : Type*} [NonUnitalNonAssocSemiring R]
    (p : R) : SubRegular p 0 ↔ IsRightRegular p := by
  simp [SubRegular, IsRightRegular, Function.Injective]

/-- `SubRegular 0 p` is exactly `IsRightRegular p`. -/
@[simp] theorem subRegular_zero_left_iff_rightRegular {R : Type*} [NonUnitalNonAssocSemiring R]
    (p : R) : SubRegular 0 p ↔ IsRightRegular p := by
  rw [SubRegular.comm, subRegular_zero_right_iff_rightRegular]

/-- Over a ring, `SubRegular p q` is exactly `IsRightRegular (p - q)`. -/
@[simp] theorem subRegular_iff_rightRegular_sub {R : Type*} [NonUnitalNonAssocRing R]
    (p q : R) : SubRegular p q ↔ IsRightRegular (p - q) := by
  rw [subRegular_iff_sub, subRegular_zero_right_iff_rightRegular]

/-- `SubRegular p p` holds only in a trivial ring: equal elements cannot be sub-regular unless
the underlying semiring is a subsingleton. -/
@[simp] theorem subRegular_self_iff_subsingleton {R : Type*} [NonUnitalNonAssocSemiring R] (p : R) :
    SubRegular p p ↔ Subsingleton R :=
  ⟨fun h ↦ ⟨fun x y ↦ h <| by simp [← add_mul, add_comm]⟩, fun _ ↦ by simp⟩

namespace Equiv.Perm
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- On a subsingleton type, the set of even permutations is the singleton `{1}`. -/
@[simp] theorem ofSign_one_of_subsingleton [Subsingleton α] : ofSign (α := α) 1 = {1} := by
  simp [Finset.ext_iff, subsingleton_eq_refl]

/-- On a subsingleton type, the set of odd permutations is empty. -/
@[simp] theorem ofSign_neg_one_of_subsingleton [Subsingleton α] : ofSign (α := α) (-1) = ∅ := by
  simp [Finset.ext_iff, subsingleton_eq_refl]

/-- Left-multiplying by a permutation `σ` carries `ofSign s` to `ofSign (s * σ.sign)`. -/
@[simp] theorem map_mulLeft_ofSign (σ : Perm α) (s : ℤˣ) :
    (ofSign s).map (Equiv.mulLeft σ).toEmbedding = ofSign (s * σ.sign) := by
  ext; simp [← div_eq_one, div_eq_mul_inv, mul_assoc, mul_left_comm]

/-- Left-multiplying by a permutation `σ` carries `ofSign (s * σ.sign)` to `ofSign s`. -/
theorem map_mulLeft_ofSign' (σ : Perm α) (s : ℤˣ) :
    (ofSign (s * σ.sign)).map (Equiv.mulLeft σ).toEmbedding = ofSign s := by
  simp [mul_assoc]

/-- Right-multiplying by a permutation `σ` carries `ofSign s` to `ofSign (s * σ.sign)`. -/
@[simp] theorem map_mulRight_ofSign (σ : Perm α) (s : ℤˣ) :
    (ofSign s).map (Equiv.mulRight σ).toEmbedding = ofSign (s * σ.sign) := by
  ext; simp [← div_eq_one, div_eq_mul_inv, mul_assoc]

/-- Right-multiplying by a permutation `σ` carries `ofSign (s * σ.sign)` to `ofSign s`. -/
theorem map_mulRight_ofSign' (σ : Perm α) (s : ℤˣ) :
    (ofSign (s * σ.sign)).map (Equiv.mulRight σ).toEmbedding = ofSign s := by
  simp [mul_assoc]

/-- Inversion preserves the sign-class of a permutation. -/
@[simp] theorem map_inv_ofSign (s : ℤˣ) :
    (ofSign (α := α) s).map (Equiv.inv _).toEmbedding = ofSign s := by ext; simp

/-- Conjugation by a type equivalence preserves the sign-class of a permutation. -/
@[simp] theorem map_conj_ofSign {β : Type*} [Fintype β] [DecidableEq β] (e : α ≃ β) (s : ℤˣ) :
    (ofSign s).map e.permCongr.toEmbedding = ofSign s := by ext; simp

/-- A variant of `Equiv.Perm.decomposeFin`: the bijection
`Perm (Fin n.succ) ≃ Fin n.succ × Perm (Fin n)` whose inverse sends `(i, e)` to the permutation that
maps `0 ↦ i` and `j.succ ↦ i.succAbove (e j)`. -/
def decomposeFinSucc (n : ℕ) : Perm (Fin n.succ) ≃ Fin n.succ × Perm (Fin n) :=
  decomposeFin.trans <| prodCongrRight <| Fin.cases (.refl _) fun i ↦ Equiv.mulLeft i.cycleRange

/-- The permutation `(decomposeFinSucc n).symm (i, e)` sends `0` to `i`. -/
theorem symm_decomposeFinSucc_zero {n : ℕ} (e : Perm (Fin n)) (i : Fin n.succ) :
    (decomposeFinSucc n).symm (i, e) 0 = i := by simp [decomposeFinSucc]

/-- Pair-form of `symm_decomposeFinSucc_zero`. -/
@[simp] theorem symm_decomposeFinSucc_zero' {n : ℕ} (p : Fin n.succ × Perm (Fin n)) :
    (decomposeFinSucc n).symm p 0 = p.1 := symm_decomposeFinSucc_zero _ _

/-- The permutation `(decomposeFinSucc n).symm (i, e)` sends `j.succ` to `i.succAbove (e j)`. -/
theorem symm_decomposeFinSucc_succ {n : ℕ} (e : Perm (Fin n)) (i : Fin n.succ) (j : Fin n) :
    (decomposeFinSucc n).symm (i, e) j.succ = i.succAbove (e j) := by
  cases i using Fin.cases
  · simp [decomposeFinSucc]
  obtain _ | n := n
  · subsingleton
  generalize hj : e j = j'
  cases j' using Fin.cases
  · simp [decomposeFinSucc, hj]
  · simp [decomposeFinSucc, hj, swap_apply_def]

/-- Pair-form of `symm_decomposeFinSucc_succ`. -/
@[simp] theorem symm_decomposeFinSucc_succ' {n : ℕ} (p : Fin n.succ × Perm (Fin n)) (j : Fin n) :
    (decomposeFinSucc n).symm p j.succ = p.1.succAbove (p.2 j) := symm_decomposeFinSucc_succ _ _ _

/-- The sign of `(decomposeFinSucc n).symm (i, e)` is `e.sign * (-1) ^ i.1`. -/
theorem sign_symm_decomposeFinSucc {n : ℕ} (e : Perm (Fin n)) (i : Fin n.succ) :
    ((decomposeFinSucc n).symm (i, e)).sign = e.sign * (-1) ^ i.1 := by
  cases i using Fin.cases
  · simp [decomposeFinSucc]
  · simp [decomposeFinSucc, pow_succ, mul_comm]

/-- Pair-form of `sign_symm_decomposeFinSucc`. -/
@[simp] theorem sign_symm_decomposeFinSucc' {n : ℕ} (p : Fin n.succ × Perm (Fin n)) :
    ((decomposeFinSucc n).symm p).sign = p.2.sign * (-1) ^ p.1.1 := sign_symm_decomposeFinSucc _ _

/-- Image of `ofSign s` under `decomposeFinSucc`: a pair `(p, e)` lies in the image iff `e ∈ ofSign
(s * (-1) ^ p.1.1)`, parametrizing sign-`s` permutations of `Fin n.succ` by `(pivot, rest)`. -/
theorem map_decomposeFinSucc_ofSign (n : ℕ) (s : ℤˣ) :
    (ofSign s).map (decomposeFinSucc n).toEmbedding =
    {p ∈ univ (α := (Fin n.succ × Perm (Fin n))) | p.2 ∈ ofSign (s * (-1) ^ p.1.1)} := by
  ext ⟨p, e⟩
  simp [← div_eq_one, div_eq_mul_inv, mul_assoc]

end Equiv.Perm

namespace Matrix
variable {R : Type*} [CommSemiring R] {m n : Type*}

/-- For an injective column-reindex `j : o → n`, `(M.submatrix id j) *ᵥ x` equals `M` applied to
the extension of `x` by zero along `j`. -/
theorem submatrix_id_mulVec {o : Type*} [Fintype n] [Fintype o]
    (M : Matrix m n R) {j : o → n} (hj : j.Injective) (x : o → R) :
    M.submatrix id j *ᵥ x = M *ᵥ j.extend x 0 := funext fun i ↦ by
  classical
  simpa [mulVec_eq_sum] using Fintype.sum_of_injective _ hj _ _
    (by simp +contextual [Function.extend_apply']) (by simp [hj.extend_apply])

/-- Reindexing the columns of `M` by a bijection `j` and then applying to `x` is the same as
applying `M` to `x ∘ j`. -/
theorem reindex_refl_mulVec {o : Type*} [Fintype n] [Fintype o]
    (M : Matrix m n R) (j : n ≃ o) (x : o → R) :
    M.reindex (.refl _) j *ᵥ x = M *ᵥ x ∘ j := funext fun i ↦ by
  simp [mulVec_eq_sum, ← j.sum_comp]

section detp
variable [Fintype n] [DecidableEq n]

/-- For a singleton-indexed matrix, `detp 1 M` is just the unique entry. -/
@[simp] theorem detp_one_of_unique [Unique n] (M : Matrix n n R) :
    M.detp 1 = M default default := by simp [detp]

/-- The negative-sign determinant `detp (-1)` of a subsingleton-indexed matrix is `0`,
since there are no odd permutations of a subsingleton. -/
@[simp] theorem detp_neg_one_of_subsingleton [Subsingleton n] (M : Matrix n n R) :
    M.detp (-1) = 0 := by simp [detp]

/-- Reindexing both rows and columns of `M` by equivalences `e₁, e₂ : n ≃ m` multiplies the
sign of the sign-`s` determinant by `sign (e₁.trans e₂.symm)`. -/
theorem detp_reindex {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix n n R) (e₁ e₂ : n ≃ m)
    (s : ℤˣ) : detp s (M.reindex e₁ e₂) = detp (s * Perm.sign (e₁.trans e₂.symm)) M := by
  rw [detp, detp, ← map_conj_ofSign e₂, ← map_mulRight_ofSign, sum_map, sum_map]
  simp [← e₁.symm.prod_comp]

/-- Variant of `detp_reindex` with the sign-correction pre-applied to the source side. -/
theorem detp_reindex' {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix n n R) (e₁ e₂ : n ≃ m)
    (s : ℤˣ) : detp (s * Perm.sign (e₁.trans e₂.symm)) (M.reindex e₁ e₂) = detp s M := by
  rw [detp_reindex]
  simp [mul_assoc]

/-- If two columns of `M` are equal (hence the column function is not injective), then the
positive and negative determinant parts agree: swapping the equal columns transports the even
and odd permutations into each other while leaving the matrix entries fixed. -/
@[simp] theorem detp_eq_of_not_injective_col {M : Matrix n n R}
    (hM : ¬M.col.Injective) : M.detp 1 = M.detp (-1) := by
  obtain ⟨i, j, hMij, hij⟩ := Function.not_injective_iff.mp hM
  simp_rw [funext_iff, col_apply] at hMij
  rw [← M.detp_reindex' (.refl n) (Equiv.swap i j)]
  simp [hij, show M.submatrix id ⇑(Equiv.swap i j) = M by ext; simp; grind]

/-- Row-version of `detp_eq_of_not_injective_col`. -/
@[simp] theorem detp_eq_of_not_injective_row {M : Matrix n n R}
    (hM : ¬M.row.Injective) : M.detp 1 = M.detp (-1) := by
  rw [← detp_transpose, detp_eq_of_not_injective_col (by simpa), detp_transpose]

/-- The `(i, j)`-entry of `adjp s` of a matrix whose `j`-th row has been replaced by the
indicator `Pi.single i 1` agrees with the `(i, j)`-entry of the original `adjp s`. -/
theorem adjp_updateRow_single (M : Matrix n n R) (s : ℤˣ) (i j : n) :
    (M.updateRow j (Pi.single i 1)).adjp s i j = M.adjp s i j := by
  refine sum_congr rfl fun σ hσ ↦ prod_congr rfl fun i hi ↦ ?_
  rw [updateRow_apply, ite_eq_right <| by simpa using hi]

/-- The `(i, j)`-cofactor `adjp s i j` equals the signed-part determinant of the row-replaced
matrix `M.updateRow j (Pi.single i 1)`. -/
theorem adjp_eq_detp_updateRow (M : Matrix n n R) (s : ℤˣ) (i j : n) :
    M.adjp s i j = (M.updateRow j (Pi.single i 1)).detp s := by
  rw [← adjp_updateRow_single, ← mul_adjp_apply_eq _ _ j, mul_apply]
  simp [updateRow_apply, Pi.single_apply]

/-- Cofactor expansion of `detp s` along the zeroth row. -/
theorem detp_fin_succ_row_zero {n : ℕ} (M : Matrix (Fin n.succ) (Fin n.succ) R) (s : ℤˣ) :
    M.detp s = ∑ j, M 0 j * (M.submatrix Fin.succ j.succAbove).detp (s * (-1) ^ j.1) := by
  rw [detp, ← sum_map_equiv (decomposeFinSucc n), map_decomposeFinSucc_ofSign,
    ← filter_univ_mem (filter _ _), sum_filter, Fintype.sum_prod_type]
  simp_rw +singlePass [detp, mul_sum, ← filter_univ_mem (ofSign _), sum_filter]
  simp [Fin.prod_univ_succ]

/-- Cofactor expansion of `detp s` along an arbitrary row `i`. -/
theorem detp_fin_succ_row {n : ℕ} (M : Matrix (Fin n.succ) (Fin n.succ) R)
    (i : Fin n.succ) (s : ℤˣ) : M.detp s =
      ∑ j, M i j * (M.submatrix i.succAbove j.succAbove).detp (s * (-1) ^ (i.1 + j.1)) := by
  rw [← M.detp_reindex' i.cycleRange (.refl _), detp_fin_succ_row_zero]
  simp [pow_add, Function.comp_def, mul_assoc]

/-- Computation of the `(i, j)`-entry of `adjp s` as the signed-part determinant of the
`(j, i)`-minor with the appropriate sign correction. -/
theorem adjp_fin_succ (n : ℕ) (M : Matrix (Fin n.succ) (Fin n.succ) R) (i j : Fin n.succ) (s : ℤˣ) :
    M.adjp s i j = (M.submatrix j.succAbove i.succAbove).detp (s * (-1) ^ (j.1 + i.1)) := by
  simp [adjp_eq_detp_updateRow, detp_fin_succ_row _ j, Pi.single_apply]

end detp

/-- Mathlib's `Matrix.Nonsingular` is exactly sub-regularity of the signed-part determinant
pair `(detp 1, detp (-1))`: unfolding `Matrix.IsDetpBalanced` turns the two statements into the
same implication, up to explicitness of the binders. -/
theorem nonsingular_iff_subRegular [Fintype n] [DecidableEq n] (M : Matrix n n R) :
    M.Nonsingular ↔ SubRegular (M.detp 1) (M.detp (-1)) :=
  ⟨fun h _ _ hab ↦ h _ _ hab, fun h _ _ hab ↦ h hab⟩

end Matrix
