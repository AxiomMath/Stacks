module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsFiltration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GradedTriangularMatrices
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoordinateSubspaceBlocks

/-!
# Block forms of a direct sum

For matrices `A` (size `r`) and `B` (size `r'`), the block diagonal matrix `A ⊕ B` of size
`r + r'` (`Stacks.EtaleCohomology.IsSplitting.blockDiag` for the splitting `Fin r ⊔ Fin r'`)
with the grading `2 d₁ ⊔ (2 d₂ + 1)` is graded upper triangular when `A` and `B` are, its graded
diagonal part is the sum of theirs, and its diagonal blocks are those of `A` (even grades) and of
`B` (odd grades); stable subspaces of a block of `A ⊕ B` are stable subspaces of the corresponding
block of `A` or `B`.

## Main definitions

* `Stacks.EtaleCohomology.sumGrading`: the grading `2 d₁ ⊔ (2 d₂ + 1)` on `Fin (r + r')`.

## Main results

* `Stacks.EtaleCohomology.sumSplitting`: the splitting `Fin (r + r') = Fin r ⊔ Fin r'`.
* `Stacks.EtaleCohomology.IsGradedUpper.sumSplitting_blockDiag`: `A ⊕ B` is graded upper
  triangular.
* `Stacks.EtaleCohomology.gradedDiag_sumSplitting_blockDiag`: the graded diagonal part of `A ⊕ B`.
* `Stacks.EtaleCohomology.eq_coordSubspace_of_coordMatrix`: block irreducibility along a coordinate
  inclusion.
* `Stacks.EtaleCohomology.charpoly_sumSplitting_blockDiag`: the characteristic polynomial of
  `A ⊕ B`.

## References

* Kedlaya, *Fourier transforms and p-adic Weil II*, §6.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {R : Type*} [CommRing R] {r r' : ℕ}

/-- The splitting `Fin (r + r') = Fin r ⊔ Fin r'`. -/
public theorem sumSplitting (r r' : ℕ) :
    IsSplitting (coordMatrix (R := R) (Fin.castAdd r' : Fin r → Fin (r + r')))
      (coordMatrix (Fin.castAdd r'))ᵀ (coordMatrix (Fin.natAdd r : Fin r' → Fin (r + r')))ᵀ
      (coordMatrix (Fin.natAdd r)) :=
  isSplitting_coordMatrix (Fin.castAdd_injective r r') (Fin.natAdd_injective r' r)
    (fun j j' h => by
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      lia)
    (fun i => i.addCases (fun j => Or.inl ⟨j, rfl⟩) (fun j => Or.inr ⟨j, rfl⟩))

/-- The grading `2 d₁` on the first `r` coordinates and `2 d₂ + 1` on the last `r'`. -/
public def sumGrading (d₁ : Fin r → ℤ) (d₂ : Fin r' → ℤ) : Fin (r + r') → ℤ :=
  Fin.append (fun i => 2 * d₁ i) (fun i => 2 * d₂ i + 1)

/-- On the first `r` coordinates, `sumGrading d₁ d₂` takes the value `2 * d₁ i`. -/
@[simp] public theorem sumGrading_castAdd (d₁ : Fin r → ℤ) (d₂ : Fin r' → ℤ) (i : Fin r) :
    sumGrading d₁ d₂ (Fin.castAdd r' i) = 2 * d₁ i := Fin.append_left _ _ _

/-- On the last `r'` coordinates, `sumGrading d₁ d₂` takes the value `2 * d₂ i + 1`. -/
@[simp] public theorem sumGrading_natAdd (d₁ : Fin r → ℤ) (d₂ : Fin r' → ℤ) (i : Fin r') :
    sumGrading d₁ d₂ (Fin.natAdd r i) = 2 * d₂ i + 1 := Fin.append_right _ _ _

section Entries

variable (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin r') (Fin r') R)

/-- An entry of `T` is the matching entry of `(coordMatrix e₂)ᵀ * T * coordMatrix e₁`. -/
private theorem apply_eq_of_transpose_coordMatrix_mul_mul {n a c : ℕ} {e₁ : Fin a → Fin n}
    {e₂ : Fin c → Fin n} {T : Matrix (Fin n) (Fin n) R} {N : Matrix (Fin c) (Fin a) R}
    (h : (coordMatrix (R := R) e₂)ᵀ * T * coordMatrix (R := R) e₁ = N) (i : Fin c) (j : Fin a) :
    T (e₂ i) (e₁ j) = N i j := by
  rw [transpose_coordMatrix_mul_mul_coordMatrix] at h
  exact congrArg (fun M => M i j) h

/-- The top-left block of `A ⊕ B` is `A`. -/
@[simp] public theorem sumSplitting_blockDiag_castAdd_castAdd (i j : Fin r) :
    (sumSplitting (R := R) r r').blockDiag A B (Fin.castAdd r' i) (Fin.castAdd r' j) = A i j :=
  apply_eq_of_transpose_coordMatrix_mul_mul (by
    rw [Matrix.mul_assoc, IsSplitting.blockDiag_mul_J, ← Matrix.mul_assoc,
      (sumSplitting (R := R) r r').left_inv, Matrix.one_mul]) i j

/-- The bottom-right block of `A ⊕ B` is `B`. -/
@[simp] public theorem sumSplitting_blockDiag_natAdd_natAdd (i j : Fin r') :
    (sumSplitting (R := R) r r').blockDiag A B (Fin.natAdd r i) (Fin.natAdd r j) = B i j :=
  apply_eq_of_transpose_coordMatrix_mul_mul (by
    rw [IsSplitting.K_mul_blockDiag, Matrix.mul_assoc, (sumSplitting (R := R) r r').right_inv,
      Matrix.mul_one]) i j

/-- The bottom-left block of `A ⊕ B` is zero. -/
@[simp] public theorem sumSplitting_blockDiag_natAdd_castAdd (i : Fin r') (j : Fin r) :
    (sumSplitting (R := R) r r').blockDiag A B (Fin.natAdd r i) (Fin.castAdd r' j) = 0 :=
  apply_eq_of_transpose_coordMatrix_mul_mul (N := 0) (by
    rw [Matrix.mul_assoc, IsSplitting.blockDiag_mul_J, ← Matrix.mul_assoc,
      (sumSplitting (R := R) r r').comp_zero, Matrix.zero_mul]) i j

/-- The top-right block of `A ⊕ B` is zero. -/
@[simp] public theorem sumSplitting_blockDiag_castAdd_natAdd (i : Fin r) (j : Fin r') :
    (sumSplitting (R := R) r r').blockDiag A B (Fin.castAdd r' i) (Fin.natAdd r j) = 0 :=
  apply_eq_of_transpose_coordMatrix_mul_mul (N := 0) (by
    have hs := sumSplitting (R := R) r r'
    rw [IsSplitting.blockDiag]
    simp only [Matrix.mul_add, Matrix.mul_assoc, hs.left_inv', hs.dual_comp_zero',
      hs.dual_comp_zero, Matrix.mul_zero, add_zero]) i j

end Entries

/-- Induction on a pair of coordinates of `Fin (r + r')`, split into the two blocks. -/
private theorem fin_add_induction {motive : Fin (r + r') → Fin (r + r') → Prop}
    (cc : ∀ i j, motive (Fin.castAdd r' i) (Fin.castAdd r' j))
    (cn : ∀ i j, motive (Fin.castAdd r' i) (Fin.natAdd r j))
    (nc : ∀ i j, motive (Fin.natAdd r i) (Fin.castAdd r' j))
    (nn : ∀ i j, motive (Fin.natAdd r i) (Fin.natAdd r j)) (i j : Fin (r + r')) : motive i j := by
  induction i using Fin.addCases with
  | left i => induction j using Fin.addCases with
    | left j => exact cc i j
    | right j => exact cn i j
  | right i => induction j using Fin.addCases with
    | left j => exact nc i j
    | right j => exact nn i j

section Graded

variable {d₁ : Fin r → ℤ} {d₂ : Fin r' → ℤ} {A : Matrix (Fin r) (Fin r) R}
  {B : Matrix (Fin r') (Fin r') R}

/-- If `A` and `B` are graded upper triangular for `d₁` and `d₂`, then `A ⊕ B` is graded upper
triangular for `sumGrading d₁ d₂`. -/
public theorem IsGradedUpper.sumSplitting_blockDiag (hA : IsGradedUpper d₁ A)
    (hB : IsGradedUpper d₂ B) :
    IsGradedUpper (sumGrading d₁ d₂) ((sumSplitting (R := R) r r').blockDiag A B) := by
  intro i j
  induction i, j using fin_add_induction with
  | cc i j =>
    intro h
    rw [sumSplitting_blockDiag_castAdd_castAdd]
    simp only [sumGrading_castAdd] at h
    exact hA i j (by lia)
  | cn i j => exact fun _ => sumSplitting_blockDiag_castAdd_natAdd A B i j
  | nc i j => exact fun _ => sumSplitting_blockDiag_natAdd_castAdd A B i j
  | nn i j =>
    intro h
    rw [sumSplitting_blockDiag_natAdd_natAdd]
    simp only [sumGrading_natAdd] at h
    exact hB i j (by lia)

/-- The graded diagonal part of `A ⊕ B` for `sumGrading d₁ d₂` is the direct sum of the graded
diagonal parts of `A` and `B`. -/
public theorem gradedDiag_sumSplitting_blockDiag :
    gradedDiag (sumGrading d₁ d₂) ((sumSplitting (R := R) r r').blockDiag A B) =
      (sumSplitting (R := R) r r').blockDiag (gradedDiag d₁ A) (gradedDiag d₂ B) := by
  ext i j
  induction i, j using fin_add_induction with
  | cc i j =>
    simp only [gradedDiag, sumGrading_castAdd, sumSplitting_blockDiag_castAdd_castAdd]
    by_cases h : d₁ i = d₁ j
    · rw [ite_eq_left (by lia), ite_eq_left h]
    · rw [ite_eq_right (by lia), ite_eq_right h]
  | cn i j => simp only [gradedDiag, sumSplitting_blockDiag_castAdd_natAdd, ite_self]
  | nc i j => simp only [gradedDiag, sumSplitting_blockDiag_natAdd_castAdd, ite_self]
  | nn i j =>
    simp only [gradedDiag, sumGrading_natAdd, sumSplitting_blockDiag_natAdd_natAdd]
    by_cases h : d₂ i = d₂ j
    · rw [ite_eq_left (by lia), ite_eq_left h]
    · rw [ite_eq_right (by lia), ite_eq_right h]

end Graded

section Irreducible

variable {K : Type*} [Field K] {d₁ : Fin r → ℤ} {d₂ : Fin r' → ℤ}

/-- For injective `e`, the coordinate `e j` of `coordMatrix e *ᵥ v` is `v j`. -/
public theorem coordMatrix_mulVec_apply {a n : ℕ} {e : Fin a → Fin n} (he : Function.Injective e)
    (v : Fin a → K) (j : Fin a) : (coordMatrix (R := K) e *ᵥ v) (e j) = v j := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j (fun j' _ hj' => by
    simp [coordMatrix, he.eq_iff, Ne.symm hj']) (by simp)]
  simp [coordMatrix]

/-- A coordinate outside the image of `e` of `coordMatrix e *ᵥ v` vanishes. -/
public theorem coordMatrix_mulVec_apply_of_forall_ne {a n : ℕ} {e : Fin a → Fin n} (v : Fin a → K)
    {i : Fin n} (hi : ∀ j, e j ≠ i) : (coordMatrix (R := K) e *ᵥ v) i = 0 := by
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_zero fun j _ => by simp [coordMatrix, Ne.symm (hi j)]

/-- **Transport of block irreducibility along a coordinate inclusion.** Let `e : Fin a → Fin n` be
injective with image exactly the coordinates of grade `t` for `δ`, `M` a family of `n × n`
matrices and `X` a family of `a × a` matrices with `M e = e X`, and suppose the only nonzero
`X`-stable subspace of the coordinates of `X`-grade `s` is all of them. Then the only nonzero
`M`-stable subspace of the coordinates of grade `t` is all of them. -/
public theorem eq_coordSubspace_of_coordMatrix {α : Type*} {a n : ℕ} {e : Fin a → Fin n}
    (he : Function.Injective e) (δ : Fin n → ℤ) (t : ℤ) (δ' : Fin a → ℤ) (s : ℤ)
    (hδ : ∀ i, δ i = t ↔ ∃ j, e j = i ∧ δ' j = s)
    (M : α → Matrix (Fin n) (Fin n) K) (X : α → Matrix (Fin a) (Fin a) K)
    (hMX : ∀ x, M x * coordMatrix e = coordMatrix e * X x)
    (hX : ∀ W' : Submodule K (Fin a → K), W' ≤ coordSubspace (K := K) (fun j => δ' j = s) →
      W' ≠ ⊥ → (∀ x, ∀ v ∈ W', X x *ᵥ v ∈ W') → W' = coordSubspace (K := K) (fun j => δ' j = s))
    (W' : Submodule K (Fin n → K)) (hW : W' ≤ coordSubspace (K := K) (fun i => δ i = t))
    (hW0 : W' ≠ ⊥) (hst : ∀ x, ∀ v ∈ W', M x *ᵥ v ∈ W') :
    W' = coordSubspace (K := K) (fun i => δ i = t) := by
  set L : (Fin a → K) →ₗ[K] (Fin n → K) := (coordMatrix (R := K) e).mulVecLin
  have hrange : ∀ w ∈ coordSubspace (K := K) (fun i => δ i = t), L (fun j => w (e j)) = w := by
    intro w hw
    funext i
    show (coordMatrix (R := K) e *ᵥ fun j => w (e j)) i = w i
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [coordMatrix_mulVec_apply he]
    · rw [coordMatrix_mulVec_apply_of_forall_ne _ fun j h => hi ⟨j, h⟩]
      refine (hw i fun h => ?_).symm
      obtain ⟨j, hj, -⟩ := (hδ i).1 h
      exact hi ⟨j, hj⟩
  have hsupp : ∀ w ∈ coordSubspace (K := K) (fun i => δ i = t),
      (fun j => w (e j)) ∈ coordSubspace (K := K) (fun j => δ' j = s) := by
    intro w hw j hj
    refine hw (e j) fun h => hj ?_
    obtain ⟨j', hj', hs⟩ := (hδ (e j)).1 h
    rwa [he hj'] at hs
  set W₁ := W'.comap L
  have hW₁ : W₁ = coordSubspace (K := K) (fun j => δ' j = s) := by
    refine hX W₁ ?_ ?_ ?_
    · intro v hv
      have hv' : L v ∈ coordSubspace (K := K) (fun i => δ i = t) := hW hv
      have := hsupp _ hv'
      have hLv : (fun j => L v (e j)) = v := funext fun j => coordMatrix_mulVec_apply he v j
      rwa [hLv] at this
    · intro h0
      apply hW0
      rw [eq_bot_iff]
      intro w hw
      have hw' : (fun j => w (e j)) ∈ W₁ := by
        show L _ ∈ W'
        rw [hrange w (hW hw)]
        exact hw
      rw [h0, Submodule.mem_bot] at hw'
      rw [Submodule.mem_bot, ← hrange w (hW hw), hw', map_zero]
    · intro x v hv
      show L (X x *ᵥ v) ∈ W'
      show (coordMatrix (R := K) e *ᵥ (X x *ᵥ v)) ∈ W'
      rw [Matrix.mulVec_mulVec, ← hMX, ← Matrix.mulVec_mulVec]
      exact hst x _ hv
  refine le_antisymm hW fun w hw => ?_
  rw [← hrange w hw]
  exact (hW₁ ▸ hsupp w hw : (fun j => w (e j)) ∈ W₁)

end Irreducible

section Charpoly

/-- `A ⊕ B` is the reindexing of the block matrix `fromBlocks A 0 0 B` along
`finSumFinEquiv`. -/
public theorem sumSplitting_blockDiag_eq_reindex (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin r') (Fin r') R) :
    (sumSplitting (R := R) r r').blockDiag A B =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B) := by
  ext i j
  induction i, j using fin_add_induction <;> simp

/-- The characteristic polynomial of a direct sum is the product. -/
public theorem charpoly_sumSplitting_blockDiag (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin r') (Fin r') R) :
    ((sumSplitting (R := R) r r').blockDiag A B).charpoly = A.charpoly * B.charpoly := by
  rw [sumSplitting_blockDiag_eq_reindex, charpoly_reindex, charpoly_fromBlocks_zero₁₂]

end Charpoly

section Map

/-- Ring homomorphisms commute with direct sums. -/
public theorem sumSplitting_blockDiag_map {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin r') (Fin r') R) :
    ((sumSplitting (R := R) r r').blockDiag A B).map f =
      (sumSplitting (R := S) r r').blockDiag (A.map f) (B.map f) := by
  ext i j
  induction i, j using fin_add_induction <;> simp

end Map

end Stacks.EtaleCohomology

end
