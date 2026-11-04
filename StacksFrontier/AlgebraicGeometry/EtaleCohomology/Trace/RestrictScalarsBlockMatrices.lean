module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonAffineLineLinear

/-!
# Matrices of block decompositions and of extensions of the coefficient field

Two families of matrices between restrictions of scalars of representations, with the identities
which make them intertwiners, retractions and projections:

* for `M (X ⊗ eqv) M⁻¹ = ⨁ Dᵢ` (a conjugation of `X : M_m(E)` to a block diagonal matrix, the
  blocks indexed by `Σ i, Fin (msᵢ)`), the rows `blockConjRow eqv M i` and columns
  `blockConjCol eqv M i` of the conjugating matrix: `rowᵢ X = Dᵢ rowᵢ`, `X colᵢ = colᵢ Dᵢ`,
  `rowᵢ colᵢ = 1`, `rowᵢ colⱼ = 0` for `i ≠ j`, `∑ colᵢ rowᵢ = 1`;
* for a tower `F ⊆ E₁ ⊆ E₂` with bases `b₁` of `E₁` and `b₂` of `E₂` over `F` and a basis `c` of
  `E₂` over `E₁`, the `F`-matrices `restrictScalarsInclusionMatrix` of `E₁ᵐ → E₂ᵐ` and
  `restrictScalarsCoordMatrix c t` of the `t`-th coordinate `E₂ᵐ → E₁ᵐ`, in the bases `b₁`, `b₂`:
  they intertwine `Res_{b₁} X` and `Res_{b₂} (X ⊗ E₂)` and exhibit `E₂ᵐ = E₂ ⊗_{E₁} E₁ᵐ`.

## Main definitions

* `Stacks.EtaleCohomology.blockConjRow`, `Stacks.EtaleCohomology.blockConjCol`.
* `Stacks.EtaleCohomology.restrictScalarsPiBasis`,
  `Stacks.EtaleCohomology.restrictScalarsInclusionMatrix`,
  `Stacks.EtaleCohomology.restrictScalarsCoordMatrix`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

/-! ### Block decompositions -/

section Blocks

variable {E : Type*} [CommRing E] {m r : ℕ} {ms : Fin r → ℕ} (eqv : Fin m ≃ Σ i, Fin (ms i))
  (M : GL (Σ i, Fin (ms i)) E)

/-- The rows of the block `i` of `M`, read on `Fin m` through `eqv`. -/
def blockConjRow (i : Fin r) : Matrix (Fin (ms i)) (Fin m) E :=
  Matrix.of fun a q => (M : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E) ⟨i, a⟩ (eqv q)

/-- The columns of the block `i` of `M⁻¹`, read on `Fin m` through `eqv`. -/
def blockConjCol (i : Fin r) : Matrix (Fin m) (Fin (ms i)) E :=
  Matrix.of fun q a =>
    ((M⁻¹ : GL (Σ i, Fin (ms i)) E) : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E) (eqv q) ⟨i, a⟩

/-- The entries of `blockConjRow eqv M i * blockConjCol eqv M j` are those of the identity matrix
at the indices `⟨i, a⟩`, `⟨j, b⟩`. -/
theorem blockConjRow_mul_blockConjCol_apply (i j : Fin r) (a : Fin (ms i)) (b : Fin (ms j)) :
    (blockConjRow eqv M i * blockConjCol eqv M j) a b =
      (1 : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E) ⟨i, a⟩ ⟨j, b⟩ := by
  simp only [blockConjRow, blockConjCol, Matrix.mul_apply, Matrix.of_apply]
  refine (eqv.sum_comp (fun s => (M : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E) ⟨i, a⟩ s *
    ((M⁻¹ : GL (Σ i, Fin (ms i)) E) : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E) s
      ⟨j, b⟩)).trans ?_
  rw [← Matrix.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- The rows and columns of the same block multiply to the identity: `rowᵢ colᵢ = 1`. -/
theorem blockConjRow_mul_blockConjCol_self (i : Fin r) :
    blockConjRow eqv M i * blockConjCol eqv M i = 1 := by
  ext a b
  rw [blockConjRow_mul_blockConjCol_apply, Matrix.one_apply, Matrix.one_apply]
  simp

/-- The rows and columns of distinct blocks multiply to zero: `rowᵢ colⱼ = 0` for `i ≠ j`. -/
theorem blockConjRow_mul_blockConjCol_of_ne {i j : Fin r} (h : i ≠ j) :
    blockConjRow eqv M i * blockConjCol eqv M j = 0 := by
  ext a b
  rw [blockConjRow_mul_blockConjCol_apply, Matrix.one_apply, if_neg (fun h' => h (congrArg
    Sigma.fst h')), Matrix.zero_apply]

/-- The products `colᵢ rowᵢ` over all blocks sum to the identity: `∑ colᵢ rowᵢ = 1`. -/
theorem sum_blockConjCol_mul_blockConjRow :
    ∑ i, blockConjCol eqv M i * blockConjRow eqv M i = 1 := by
  ext q q'
  simp only [Matrix.sum_apply, blockConjRow, blockConjCol, Matrix.mul_apply, Matrix.of_apply]
  refine (Fintype.sum_sigma (fun s => ((M⁻¹ : GL (Σ i, Fin (ms i)) E) :
    Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E) (eqv q) s *
      (M : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E) s (eqv q'))).symm.trans ?_
  rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp [Matrix.one_apply, eqv.injective.eq_iff]

variable {X : Matrix (Fin m) (Fin m) E} {D : ∀ i, Matrix (Fin (ms i)) (Fin (ms i)) E}
  (hX : (M : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E) * Matrix.reindex eqv eqv X *
    ((M⁻¹ : GL (Σ i, Fin (ms i)) E) : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E) =
      Matrix.blockDiagonal' D)

local notation "MM" => (M : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E)
local notation "MI" =>
  ((M⁻¹ : GL (Σ i, Fin (ms i)) E) : Matrix (Σ i, Fin (ms i)) (Σ i, Fin (ms i)) E)

/-- The entries of `blockDiagonal' D * N` in the rows of block `i` only involve the block `D i` and
the rows of `N` of block `i`. -/
theorem blockDiagonal'_mul_apply {n : Type*} [Fintype n] (N : Matrix (Σ i, Fin (ms i)) n E)
    (i : Fin r) (a : Fin (ms i)) (q : n) :
    (Matrix.blockDiagonal' D * N) ⟨i, a⟩ q = ∑ b, D i a b * N ⟨i, b⟩ q := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single i (fun j _ hji =>
    Finset.sum_eq_zero fun b _ => by rw [Matrix.blockDiagonal'_apply_ne D a b (Ne.symm hji),
      zero_mul]) (by simp)]
  simp only [Matrix.blockDiagonal'_apply_eq]

/-- The entries of `N * blockDiagonal' D` in the columns of block `i` only involve the block `D i`
and the columns of `N` of block `i`. -/
theorem mul_blockDiagonal'_apply {n : Type*} [Fintype n] (N : Matrix n (Σ i, Fin (ms i)) E)
    (q : n) (i : Fin r) (a : Fin (ms i)) :
    (N * Matrix.blockDiagonal' D) q ⟨i, a⟩ = ∑ b, N q ⟨i, b⟩ * D i b a := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single i (fun j _ hji =>
    Finset.sum_eq_zero fun b _ => by rw [Matrix.blockDiagonal'_apply_ne D b a hji, mul_zero])
    (by simp)]
  simp only [Matrix.blockDiagonal'_apply_eq]

include hX in
/-- If `M (X ⊗ eqv) M⁻¹ = blockDiagonal' D`, then `rowᵢ X = Dᵢ rowᵢ`. -/
theorem blockConjRow_mul (i : Fin r) : blockConjRow eqv M i * X = D i * blockConjRow eqv M i := by
  have h : MM * Matrix.reindex eqv eqv X = Matrix.blockDiagonal' D * MM := by
    rw [← hX]
    simp only [Matrix.mul_assoc]
    rw [M.inv_mul, Matrix.mul_one]
  ext a q
  have h' := congrFun (congrFun h ⟨i, a⟩) (eqv q)
  rw [blockDiagonal'_mul_apply, Matrix.mul_apply, ← eqv.sum_comp] at h'
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at h'
  simp only [blockConjRow, Matrix.mul_apply, Matrix.of_apply]
  exact h'

include hX in
/-- If `M (X ⊗ eqv) M⁻¹ = blockDiagonal' D`, then `X colᵢ = colᵢ Dᵢ`. -/
theorem mul_blockConjCol (i : Fin r) : X * blockConjCol eqv M i = blockConjCol eqv M i * D i := by
  have h : Matrix.reindex eqv eqv X * MI = MI * Matrix.blockDiagonal' D := by
    rw [← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, M.inv_mul, Matrix.one_mul]
  ext q a
  have h' := congrFun (congrFun h (eqv q)) ⟨i, a⟩
  rw [mul_blockDiagonal'_apply, Matrix.mul_apply, ← eqv.sum_comp] at h'
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at h'
  simp only [blockConjCol, Matrix.mul_apply, Matrix.of_apply]
  exact h'

end Blocks

/-! ### Restriction of scalars of matrices: sums and scalars -/

section RestrictScalars

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

/-- Restriction of scalars of matrices commutes with finite sums. -/
theorem restrictScalarsMatrix_sum {ι : Type*} (s : Finset ι) {m n : ℕ}
    (A : ι → Matrix (Fin m) (Fin n) E) :
    restrictScalarsMatrix b (∑ t ∈ s, A t) = ∑ t ∈ s, restrictScalarsMatrix b (A t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, restrictScalarsMatrix_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, restrictScalarsMatrix_add, ih]

/-- Restrictions of scalars of `E`-matrices commute with the action of `E`. -/
theorem restrictScalarsMatrix_mul_restrictScalarsScalarAlgHom {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) E) (e : E) :
    restrictScalarsMatrix b A * restrictScalarsScalarAlgHom b n e =
      restrictScalarsScalarAlgHom b m e * restrictScalarsMatrix b A := by
  show restrictScalarsMatrix b A * restrictScalarsMatrix b _ =
    restrictScalarsMatrix b _ * restrictScalarsMatrix b A
  rw [← restrictScalarsMatrix_mul, ← restrictScalarsMatrix_mul]
  congr 1
  ext i j
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]

/-- The basis `(e_i b_l)_{(i, l)}` of `Eᵐ` over `F`, indexed as in `restrictScalarsMatrix`. -/
def restrictScalarsPiBasis (m : ℕ) : Module.Basis (Fin (m * d)) F (Fin m → E) :=
  (Pi.basis fun _ : Fin m => b).reindex ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv)

/-- The basis vector of `restrictScalarsPiBasis b m` at `(i, l)` is `b l` in the coordinate `i`. -/
theorem restrictScalarsPiBasis_apply (m : ℕ) (i : Fin m) (l : Fin d) :
    restrictScalarsPiBasis b m (finProdFinEquiv (i, l)) = Pi.single i (b l) := by
  rw [restrictScalarsPiBasis, Module.Basis.reindex_apply, Pi.basis_apply]
  simp

/-- The `(i, l)` coordinate of `v` in `restrictScalarsPiBasis b m` is the `l`-th coordinate of
`v i` in `b`. -/
theorem restrictScalarsPiBasis_repr (m : ℕ) (v : Fin m → E) (i : Fin m) (l : Fin d) :
    (restrictScalarsPiBasis b m).repr v (finProdFinEquiv (i, l)) = b.repr (v i) l := by
  rw [restrictScalarsPiBasis, Module.Basis.repr_reindex_apply, Pi.basis_repr]
  simp

/-- **`Res_b M` is the matrix of multiplication by `M` on `Eᵐ` over `F`.** -/
theorem restrictScalarsMatrix_eq_toMatrix {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) :
    restrictScalarsMatrix b M = LinearMap.toMatrix (restrictScalarsPiBasis b n)
      (restrictScalarsPiBasis b m) ((Matrix.mulVecLin M).restrictScalars F) := by
  ext p q
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, l'⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [restrictScalarsMatrix_apply, LinearMap.toMatrix_apply, restrictScalarsPiBasis_apply,
    restrictScalarsPiBasis_repr, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_single, Algebra.leftMulMatrix_eq_repr_mul]
  simp [mul_comm]

end RestrictScalars

/-! ### Extension of the coefficient field -/

section Extension

variable {F E₁ E₂ : Type*} [Field F] [Field E₁] [Field E₂] [Algebra F E₁] [Algebra F E₂]
  [Algebra E₁ E₂] [IsScalarTower F E₁ E₂] {d₁ d₂ : ℕ} (b₁ : Module.Basis (Fin d₁) F E₁)
  (b₂ : Module.Basis (Fin d₂) F E₂) {s : Type*} [Fintype s] (c : Module.Basis s E₁ E₂) (m : ℕ)

/-- The `F`-matrix of the inclusion `E₁ᵐ → E₂ᵐ` in the bases of `b₁` and `b₂`. -/
def restrictScalarsInclusionMatrix : Matrix (Fin (m * d₂)) (Fin (m * d₁)) F :=
  LinearMap.toMatrix (restrictScalarsPiBasis b₁ m) (restrictScalarsPiBasis b₂ m)
    ((IsScalarTower.toAlgHom F E₁ E₂).toLinearMap.compLeft (Fin m))

/-- The `F`-matrix of the `t`-th coordinate `E₂ᵐ → E₁ᵐ` along `c`, in the bases of `b₂` and
`b₁`. -/
def restrictScalarsCoordMatrix (t : s) : Matrix (Fin (m * d₁)) (Fin (m * d₂)) F :=
  LinearMap.toMatrix (restrictScalarsPiBasis b₂ m) (restrictScalarsPiBasis b₁ m)
    (((c.coord t).restrictScalars F).compLeft (Fin m))

/-- The inclusion matrix intertwines `Res_{b₁} X` and `Res_{b₂} (X ⊗ E₂)`. -/
theorem restrictScalarsInclusionMatrix_mul (X : Matrix (Fin m) (Fin m) E₁) :
    restrictScalarsInclusionMatrix b₁ b₂ m * restrictScalarsMatrix b₁ X =
      restrictScalarsMatrix b₂ (X.map (algebraMap E₁ E₂)) *
        restrictScalarsInclusionMatrix b₁ b₂ m := by
  rw [restrictScalarsMatrix_eq_toMatrix, restrictScalarsMatrix_eq_toMatrix,
    restrictScalarsInclusionMatrix, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  congr 1
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [LinearMap.comp_apply, LinearMap.compLeft_apply, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply, Function.comp_apply, AlgHom.toLinearMap_apply,
    IsScalarTower.coe_toAlgHom']
  exact RingHom.map_mulVec (algebraMap E₁ E₂) X v i

/-- Each coordinate matrix intertwines `Res_{b₂} (X ⊗ E₂)` and `Res_{b₁} X`. -/
theorem restrictScalarsCoordMatrix_mul (t : s) (X : Matrix (Fin m) (Fin m) E₁) :
    restrictScalarsCoordMatrix b₁ b₂ c m t * restrictScalarsMatrix b₂ (X.map (algebraMap E₁ E₂)) =
      restrictScalarsMatrix b₁ X * restrictScalarsCoordMatrix b₁ b₂ c m t := by
  rw [restrictScalarsMatrix_eq_toMatrix, restrictScalarsMatrix_eq_toMatrix,
    restrictScalarsCoordMatrix, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  congr 1
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [LinearMap.comp_apply, LinearMap.compLeft_apply, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply, Function.comp_apply, Module.Basis.coord_apply, Matrix.mulVec,
    dotProduct, Matrix.map_apply, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_mul, algebraMap_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- The image of the scalar matrix `e` under `algebraMap E₁ E₂` is the scalar matrix of the image
of `e`. -/
theorem scalar_map_algebraMap (e : E₁) :
    (Matrix.scalar (Fin m) e).map (algebraMap E₁ E₂) =
      Matrix.scalar (Fin m) (algebraMap E₁ E₂ e) := by
  ext i j
  by_cases h : i = j <;> simp [h]

/-- The inclusion matrix intertwines the actions of `e ∈ E₁` on `E₁ᵐ` and on `E₂ᵐ`. -/
theorem restrictScalarsInclusionMatrix_mul_scalar (e : E₁) :
    restrictScalarsInclusionMatrix b₁ b₂ m * restrictScalarsScalarAlgHom b₁ m e =
      restrictScalarsScalarAlgHom b₂ m (algebraMap E₁ E₂ e) *
        restrictScalarsInclusionMatrix b₁ b₂ m := by
  have h := restrictScalarsInclusionMatrix_mul b₁ b₂ m (Matrix.scalar (Fin m) e)
  rw [scalar_map_algebraMap] at h
  exact h

/-- Each coordinate matrix intertwines the actions of `e ∈ E₁` on `E₂ᵐ` and on `E₁ᵐ`. -/
theorem restrictScalarsCoordMatrix_mul_scalar (t : s) (e : E₁) :
    restrictScalarsCoordMatrix b₁ b₂ c m t * restrictScalarsScalarAlgHom b₂ m (algebraMap E₁ E₂ e) =
      restrictScalarsScalarAlgHom b₁ m e * restrictScalarsCoordMatrix b₁ b₂ c m t := by
  have h := restrictScalarsCoordMatrix_mul b₁ b₂ c m t (Matrix.scalar (Fin m) e)
  rw [scalar_map_algebraMap] at h
  exact h

/-- Including `E₁ᵐ` into `E₂ᵐ`, multiplying by `c u` and taking the `t`-th coordinate along `c` is
the identity if `t = u` and zero otherwise. -/
theorem restrictScalarsCoordMatrix_mul_scalar_mul_inclusionMatrix [DecidableEq s] (t u : s) :
    restrictScalarsCoordMatrix b₁ b₂ c m t * restrictScalarsScalarAlgHom b₂ m (c u) *
        restrictScalarsInclusionMatrix b₁ b₂ m = if t = u then 1 else 0 := by
  show restrictScalarsCoordMatrix b₁ b₂ c m t * restrictScalarsMatrix b₂ _ *
    restrictScalarsInclusionMatrix b₁ b₂ m = _
  rw [restrictScalarsMatrix_eq_toMatrix, restrictScalarsInclusionMatrix,
    restrictScalarsCoordMatrix, ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  rw [← LinearMap.toMatrix_id (restrictScalarsPiBasis b₁ m), ← map_zero (LinearMap.toMatrix
    (restrictScalarsPiBasis b₁ m) (restrictScalarsPiBasis b₁ m)), ← apply_ite]
  congr 1
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [LinearMap.comp_apply, LinearMap.compLeft_apply, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal, Function.comp_apply,
    AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', Module.Basis.coord_apply]
  rw [mul_comm, ← Algebra.smul_def, map_smul, Module.Basis.repr_self]
  split_ifs with h
  · simp [h]
  · simp [Ne.symm h]

/-- Every vector of `E₂ᵐ` is the sum over `t` of `c t` times the inclusion of its `t`-th coordinate
along `c`: `E₂ᵐ = E₂ ⊗_{E₁} E₁ᵐ`. -/
theorem sum_scalar_mul_inclusionMatrix_mul_coordMatrix :
    ∑ t, restrictScalarsScalarAlgHom b₂ m (c t) * restrictScalarsInclusionMatrix b₁ b₂ m *
        restrictScalarsCoordMatrix b₁ b₂ c m t = 1 := by
  show ∑ t, restrictScalarsMatrix b₂ _ * restrictScalarsInclusionMatrix b₁ b₂ m *
    restrictScalarsCoordMatrix b₁ b₂ c m t = 1
  simp only [restrictScalarsMatrix_eq_toMatrix, restrictScalarsInclusionMatrix,
    restrictScalarsCoordMatrix, ← LinearMap.toMatrix_comp]
  rw [← map_sum, ← LinearMap.toMatrix_id (restrictScalarsPiBasis b₂ m)]
  congr 1
  refine LinearMap.ext fun w => funext fun i => ?_
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.scalar_apply,
    Matrix.mulVec_diagonal, LinearMap.compLeft_apply, Function.comp_apply,
    AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', Module.Basis.coord_apply,
    LinearMap.id_apply]
  conv_rhs => rw [← c.sum_repr (w i)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Algebra.smul_def, mul_comm]

end Extension

end Stacks.EtaleCohomology

end
