module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Coordinate subspaces and diagonal blocks of matrices

For a predicate `p` on the index set, the coordinate subspace `{v | v i = 0 for ¬ p i}` of `Kᶥ`
has the basis `(e_i)_{p i}`.  A matrix `M` with `M i j = 0` whenever `p j` and `¬ p i` preserves
it, and the restriction of `M` to it has the matrix `M.toSquareBlockProp p`; so its determinant
and characteristic polynomial are those of the diagonal block.  For a representation in block
diagonal form along a grading, the coordinate subspaces of sets of grades are the sums of the
corresponding constituents.

## Main definitions

* `Stacks.EtaleCohomology.coordSubspace`, `Stacks.EtaleCohomology.coordSubspaceBasis`.

## Main results

* `Stacks.EtaleCohomology.mulVec_mem_coordSubspace`.
* `Stacks.EtaleCohomology.toMatrix_restrict_coordSubspace`,
  `Stacks.EtaleCohomology.det_restrict_coordSubspace`,
  `Stacks.EtaleCohomology.charpoly_restrict_coordSubspace`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] (p : ι → Prop) [DecidablePred p]

/-- The coordinate subspace `{v | v i = 0 for ¬ p i}`. -/
public def coordSubspace : Submodule K (ι → K) where
  carrier := {v | ∀ i, ¬ p i → v i = 0}
  add_mem' ha hb i hi := by rw [Pi.add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c v hv i hi := by rw [Pi.smul_apply, hv i hi, smul_zero]

/-- The coordinate subspace is `K^{p}`. -/
public def coordSubspaceEquiv : coordSubspace (K := K) p ≃ₗ[K] ({i // p i} → K) where
  toFun v i := (v : ι → K) i
  invFun w := ⟨fun i => if h : p i then w ⟨i, h⟩ else 0, fun i hi => by simp [hi]⟩
  left_inv v := by
    ext i
    by_cases h : p i
    · simp [h]
    · simp [h, v.2 i h]
  right_inv w := by
    ext ⟨i, h⟩
    simp [h]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The basis `(e_i)_{p i}` of the coordinate subspace. -/
public def coordSubspaceBasis : Module.Basis {i // p i} K (coordSubspace (K := K) p) :=
  (Pi.basisFun K {i // p i}).map (coordSubspaceEquiv p).symm

variable {p}

omit [DecidableEq ι] [DecidablePred p] in
/-- A matrix with no entries from `p` to `¬ p` preserves the coordinate subspace. -/
public theorem mulVec_mem_coordSubspace {M : Matrix ι ι K} (hM : ∀ i j, p j → ¬ p i → M i j = 0)
    {v : ι → K} (hv : v ∈ coordSubspace (K := K) p) : M *ᵥ v ∈ coordSubspace (K := K) p := by
  intro i hi
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : p j
  · rw [hM i j hj hi, zero_mul]
  · rw [hv j hj, mul_zero]

/-- The restriction of `Matrix.toLin' M` to the coordinate subspace has, in the basis
`coordSubspaceBasis p`, the matrix `M.toSquareBlockProp p`. -/
public theorem toMatrix_restrict_coordSubspace {M : Matrix ι ι K}
    (hM : ∀ v ∈ coordSubspace (K := K) p, Matrix.toLin' M v ∈ coordSubspace (K := K) p) :
    LinearMap.toMatrix (coordSubspaceBasis p) (coordSubspaceBasis p)
        ((Matrix.toLin' M).restrict hM) = M.toSquareBlockProp p := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [LinearMap.toMatrix_apply]
  simp only [coordSubspaceBasis, Module.Basis.map_apply, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_symm, Pi.basisFun_repr, Pi.basisFun_apply]
  show ((Matrix.toLin' M) _) i = _
  rw [Matrix.toLin'_apply, Matrix.toSquareBlockProp_def, Matrix.of_apply]
  simp only [coordSubspaceEquiv, LinearEquiv.coe_symm_mk', Matrix.mulVec, dotProduct,
    Submodule.subtype_apply]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro b _ hb
    by_cases h : p b
    · simp [h, Subtype.ext_iff, hb]
    · simp [h]
  · simp

/-- The determinant of the restriction of `Matrix.toLin' M` to the coordinate subspace is the
determinant of the diagonal block `M.toSquareBlockProp p`. -/
public theorem det_restrict_coordSubspace {M : Matrix ι ι K}
    (hM : ∀ v ∈ coordSubspace (K := K) p, Matrix.toLin' M v ∈ coordSubspace (K := K) p) :
    LinearMap.det ((Matrix.toLin' M).restrict hM) = (M.toSquareBlockProp p).det := by
  rw [← LinearMap.det_toMatrix (coordSubspaceBasis p), toMatrix_restrict_coordSubspace]

/-- The characteristic polynomial of the restriction of `Matrix.toLin' M` to the coordinate
subspace is that of the diagonal block `M.toSquareBlockProp p`. -/
public theorem charpoly_restrict_coordSubspace {M : Matrix ι ι K}
    (hM : ∀ v ∈ coordSubspace (K := K) p, Matrix.toLin' M v ∈ coordSubspace (K := K) p) :
    LinearMap.charpoly ((Matrix.toLin' M).restrict hM) = (M.toSquareBlockProp p).charpoly := by
  rw [← LinearMap.charpoly_toMatrix _ (coordSubspaceBasis p), toMatrix_restrict_coordSubspace]

end Stacks.EtaleCohomology

end
