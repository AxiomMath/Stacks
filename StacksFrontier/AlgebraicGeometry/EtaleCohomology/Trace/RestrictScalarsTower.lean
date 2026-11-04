module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepresentation
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Restriction of scalars along a tower of fields

For fields `F ⊆ E ⊆ E₂` with bases `b` of `E` over `F` and `c` of `E₂` over `E`, the basis
`(b_l c_k)` of `E₂` over `F` (`Stacks.EtaleCohomology.towerBasis`) turns the restriction of scalars
of `M ⊗_E E₂` into `Res_b M ⊗ 1` (`Stacks.EtaleCohomology.restrictScalarsMatrix_towerBasis_map`).
So a representation `σ` over `E` has `Res_b σ` as a direct summand of `Res (σ ⊗_E E₂)`, through the
inclusion `v ↦ v ⊗ e_{k₀}` and the projection onto that summand
(`Stacks.EtaleCohomology.towerInclusion`, `Stacks.EtaleCohomology.towerProjection`).

## Main results

* `Stacks.EtaleCohomology.restrictScalarsMatrix_towerBasis_map`.
* `Stacks.EtaleCohomology.towerInclusion_mul`, `Stacks.EtaleCohomology.mul_towerProjection`,
  `Stacks.EtaleCohomology.towerProjection_mul_towerInclusion`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

section Tower

variable {F E E₂ : Type*} [Field F] [Field E] [Field E₂] [Algebra F E] [Algebra E E₂]
  [Algebra F E₂] [IsScalarTower F E E₂] {d d' : ℕ} (b : Module.Basis (Fin d) F E)
  (c : Module.Basis (Fin d') E E₂)

/-- The basis `(b_l c_k)_{(l, k)}` of `E₂` over `F`, indexed by `Fin (d * d')`. -/
abbrev towerBasis : Module.Basis (Fin (d * d')) F E₂ :=
  (b.smulTower c).reindex finProdFinEquiv

/-- The reindexing `(i, (l, k)) ↦ ((i, l), k)` of `Fin (m * (d * d'))`. -/
def towerReindex (m d d' : ℕ) : Fin (m * (d * d')) ≃ Fin (m * d) × Fin d' :=
  finProdFinEquiv.symm.trans ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm).trans
    ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr finProdFinEquiv (Equiv.refl _))))

/-- `towerReindex` sends the index of `(i, (l, k))` to `((i, l), k)`. -/
theorem towerReindex_apply {m : ℕ} (i : Fin m) (l : Fin d) (k : Fin d') :
    towerReindex m d d' (finProdFinEquiv (i, finProdFinEquiv (l, k))) =
      (finProdFinEquiv (i, l), k) := by
  simp [towerReindex]

/-- In the basis `towerBasis b c`, multiplication by `x ∈ E` has the matrix `[x]_b ⊗ 1_{d'}`:
its `((l, k), (l', k'))` entry is `[x]_b l l'` if `k = k'`, and `0` otherwise. -/
theorem leftMulMatrix_towerBasis_algebraMap (x : E) (l l' : Fin d) (k k' : Fin d') :
    Algebra.leftMulMatrix (towerBasis b c) (algebraMap E E₂ x) (finProdFinEquiv (l, k))
      (finProdFinEquiv (l', k')) =
        Algebra.leftMulMatrix b x l l' * (1 : Matrix (Fin d') (Fin d') F) k k' := by
  have h : ∀ (b' : Module.Basis (Fin d × Fin d') F E₂) (y : E₂) (p q : Fin d × Fin d'),
      Algebra.leftMulMatrix (b'.reindex finProdFinEquiv) y (finProdFinEquiv p)
        (finProdFinEquiv q) = Algebra.leftMulMatrix b' y p q := by
    intro b' y p q
    simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [h, Algebra.smulTower_leftMulMatrix_algebraMap, blockDiagonal_apply]
  by_cases hk : k = k' <;> simp [hk, Matrix.one_apply]

/-- **Restriction of scalars along a tower `F ⊆ E ⊆ E₂`**: in the basis `(b_l c_k)`, the
restriction of scalars of `M ⊗_E E₂` is `Res_b M ⊗ 1_{d'}`. -/
theorem restrictScalarsMatrix_towerBasis_map {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) :
    restrictScalarsMatrix (towerBasis b c) (M.map (algebraMap E E₂)) =
      (kronecker (restrictScalarsMatrix b M) (1 : Matrix (Fin d') (Fin d') F)).submatrix
        (towerReindex m d d') (towerReindex n d d') := by
  ext p q
  obtain ⟨⟨i, lk⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨l, k⟩, rfl⟩ := finProdFinEquiv.surjective lk
  obtain ⟨⟨j, lk'⟩, rfl⟩ := finProdFinEquiv.surjective q
  obtain ⟨⟨l', k'⟩, rfl⟩ := finProdFinEquiv.surjective lk'
  rw [submatrix_apply, towerReindex_apply, towerReindex_apply]
  show _ = restrictScalarsMatrix b M (finProdFinEquiv (i, l)) (finProdFinEquiv (j, l')) *
    (1 : Matrix (Fin d') (Fin d') F) k k'
  rw [restrictScalarsMatrix_apply, restrictScalarsMatrix_apply]
  simpa using leftMulMatrix_towerBasis_algebraMap b c (M i j) l l' k k'

end Tower

section Summand

variable {F : Type*} [Field F] {N d' : ℕ} (k₀ : Fin d')

/-- The column `e_{k₀}`. -/
def towerColumn : Matrix (Fin d') (Fin 1) F := Matrix.of fun k _ => if k = k₀ then 1 else 0

/-- `e_{k₀}ᵀ e_{k₀} = 1`. -/
theorem transpose_towerColumn_mul_towerColumn :
    (towerColumn (F := F) k₀)ᵀ * towerColumn (F := F) k₀ = 1 := by
  ext a a'
  rw [Subsingleton.elim a a', Matrix.mul_apply, Matrix.one_apply_eq]
  simp [towerColumn, of_apply]

/-- The inclusion `F^N ⟶ F^N ⊗ F^{d'}`, `v ↦ v ⊗ e_{k₀}`. -/
def towerInclusion : Matrix (Fin N × Fin d') (Fin N) F :=
  (kronecker (1 : Matrix (Fin N) (Fin N) F) (towerColumn k₀)).submatrix id
    (Equiv.prodUnique (Fin N) (Fin 1)).symm

/-- The projection `F^N ⊗ F^{d'} ⟶ F^N` onto the summand `F^N ⊗ e_{k₀}`. -/
def towerProjection : Matrix (Fin N) (Fin N × Fin d') F :=
  (kronecker (1 : Matrix (Fin N) (Fin N) F) (towerColumn k₀)ᵀ).submatrix
    (Equiv.prodUnique (Fin N) (Fin 1)).symm id

/-- `R ⊗ 1_1`, reindexed along `Fin N × Fin 1 ≃ Fin N`, is `R`. -/
theorem submatrix_kronecker_one_prodUnique (R : Matrix (Fin N) (Fin N) F) :
    (kronecker R (1 : Matrix (Fin 1) (Fin 1) F)).submatrix (Equiv.prodUnique (Fin N) (Fin 1)).symm
      (Equiv.prodUnique (Fin N) (Fin 1)).symm = R := by
  ext i j
  simp

/-- The inclusion `v ↦ v ⊗ e_{k₀}` intertwines `R` with `R ⊗ 1_{d'}`. -/
theorem towerInclusion_mul (R : Matrix (Fin N) (Fin N) F) :
    towerInclusion k₀ * R = kronecker R (1 : Matrix (Fin d') (Fin d') F) * towerInclusion k₀ := by
  ext ⟨i, k⟩ j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [towerInclusion, towerColumn, submatrix_apply, id, Equiv.prodUnique_symm_apply]
  by_cases hk : k = k₀ <;> simp [hk, ite_mul, mul_ite, Matrix.one_apply]

/-- The projection onto `F^N ⊗ e_{k₀}` intertwines `R ⊗ 1_{d'}` with `R`. -/
theorem mul_towerProjection (R : Matrix (Fin N) (Fin N) F) :
    towerProjection k₀ * kronecker R (1 : Matrix (Fin d') (Fin d') F) = R * towerProjection k₀ := by
  ext i ⟨j, k⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [towerProjection, towerColumn, submatrix_apply, id, Equiv.prodUnique_symm_apply]
  by_cases hk : k = k₀ <;> simp [hk, ite_mul, mul_ite, Matrix.one_apply]

/-- The projection onto `F^N ⊗ e_{k₀}` is a left inverse of the inclusion `v ↦ v ⊗ e_{k₀}`. -/
theorem towerProjection_mul_towerInclusion :
    towerProjection (N := N) (F := F) k₀ * towerInclusion (N := N) (F := F) k₀ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [towerProjection, towerInclusion, towerColumn, submatrix_apply, Matrix.one_apply, id,
    Equiv.prodUnique_symm_apply]
  simp [mul_ite, Matrix.one_apply]

end Summand

section TowerSummand

variable {F E E₂ : Type*} [Field F] [Field E] [Field E₂] [Algebra F E] [Algebra E E₂]
  [Algebra F E₂] [IsScalarTower F E E₂] {d d' : ℕ} (b : Module.Basis (Fin d) F E)
  (c : Module.Basis (Fin d') E E₂) {m : ℕ} (k₀ : Fin d')

/-- `Res_b M ⟶ Res (M ⊗_E E₂)`, `v ↦ v ⊗ e_{k₀}`, in the coordinates of `towerBasis b c`. -/
def towerSummandInclusion : Matrix (Fin (m * (d * d'))) (Fin (m * d)) F :=
  (towerInclusion (N := m * d) (F := F) k₀).submatrix (towerReindex m d d') id

/-- The projection `Res (M ⊗_E E₂) ⟶ Res_b M` onto the summand `e_{k₀}`. -/
def towerSummandProjection : Matrix (Fin (m * d)) (Fin (m * (d * d'))) F :=
  (towerProjection (N := m * d) (F := F) k₀).submatrix id (towerReindex m d d')

/-- The inclusion `Res_b M ⟶ Res (M ⊗_E E₂)` intertwines `Res_b M` with `Res (M ⊗_E E₂)`. -/
theorem towerSummandInclusion_mul (M : Matrix (Fin m) (Fin m) E) :
    towerSummandInclusion (d := d) (F := F) k₀ * restrictScalarsMatrix b M =
      restrictScalarsMatrix (towerBasis b c) (M.map (algebraMap E E₂)) *
        towerSummandInclusion (d := d) (F := F) k₀ := by
  rw [restrictScalarsMatrix_towerBasis_map, towerSummandInclusion,
    submatrix_mul_equiv, ← towerInclusion_mul]
  rfl

/-- The projection `Res (M ⊗_E E₂) ⟶ Res_b M` intertwines `Res (M ⊗_E E₂)` with `Res_b M`. -/
theorem towerSummandProjection_mul (M : Matrix (Fin m) (Fin m) E) :
    towerSummandProjection (d := d) (F := F) k₀ *
        restrictScalarsMatrix (towerBasis b c) (M.map (algebraMap E E₂)) =
      restrictScalarsMatrix b M * towerSummandProjection (d := d) (F := F) k₀ := by
  rw [restrictScalarsMatrix_towerBasis_map, towerSummandProjection, submatrix_mul_equiv,
    mul_towerProjection]
  rfl

/-- `towerSummandProjection` is a left inverse of `towerSummandInclusion`. -/
theorem towerSummandProjection_mul_towerSummandInclusion :
    towerSummandProjection (m := m) (d := d) (F := F) k₀ *
      towerSummandInclusion (m := m) (d := d) (F := F) k₀ = 1 := by
  rw [towerSummandProjection, towerSummandInclusion, submatrix_mul_equiv,
    towerProjection_mul_towerInclusion]
  rfl

end TowerSummand

end Stacks.EtaleCohomology

end
