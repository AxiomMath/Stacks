module

public import Mathlib.RingTheory.Trace.Basic

/-! # The isomorphism `L ⊗[F] K ≅ ((K →ₐ[F] L) → L)` -/

@[expose] public section

open Algebra TensorProduct Matrix

namespace Algebra

/-- For a finite separable field extension `L/K`, the determinant of the trace matrix
of any basis is nonzero. -/
theorem det_traceMatrix_ne_zero {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L) [Algebra.IsSeparable K L] :
    (traceMatrix K b).det ≠ 0 := by
  rw [traceMatrix_of_basis]
  exact det_traceForm_ne_zero b

/-- For a finite separable extension `K/F` with `L` algebraically closed, the determinant of
the matrix `(σⱼ bᵢ)ᵢⱼ` whose entries are the embeddings of a basis applied to elements of
the basis is nonzero. Equivalently, the embeddings of `K` into `L` are linearly independent
over `L`. -/
theorem det_embeddingsMatrixReindex_ne_zero {F K L : Type*}
    [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [FiniteDimensional F K] [Algebra.IsSeparable F K] [IsAlgClosed L]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K) (σ : ι ≃ (K →ₐ[F] L)) :
    (embeddingsMatrixReindex F L b σ).det ≠ 0 := by
  have := (algebraMap F L).injective.ne (det_traceMatrix_ne_zero b)
  rwa [map_zero, RingHom.map_det, RingHom.mapMatrix_apply,
    traceMatrix_eq_embeddingsMatrixReindex_mul_trans (e := σ),
    det_mul, det_transpose, mul_self_ne_zero] at this

/-- The `L`-algebra homomorphism `L ⊗[F] K →ₐ[L] (K →ₐ[F] L) → L` sending a simple tensor
`x ⊗ₜ y` to the function `σ ↦ x * σ y`. -/
def liftEmbeddings (F K L : Type*)
    [CommSemiring F] [Semiring K] [CommSemiring L] [Algebra F K] [Algebra F L] :
    L ⊗[F] K →ₐ[L] (K →ₐ[F] L) → L :=
  lift (ofId _ _) embeddings fun _ _ ↦ .all _ _
where
  /-- The `F`-algebra homomorphism `K →ₐ[F] (K →ₐ[F] L) → L` of evaluation: it sends
  `y : K` to the function `σ ↦ σ y`. -/
  embeddings :=
  { toFun x f := f x
    map_zero' := by ext; simp
    map_add' _ _ := by ext; simp
    map_one' := by ext; simp
    map_mul' _ _ := by ext; simp
    commutes' _ := by ext; simp }

/-- Computation of `liftEmbeddings` on a simple tensor: `(x ⊗ₜ y)` is sent to `σ ↦ x * σ y`. -/
@[simp] theorem liftEmbeddings_tmul_apply {F K L : Type*}
    [CommSemiring F] [Semiring K] [CommSemiring L] [Algebra F K] [Algebra F L]
    (x : L) (y : K) (σ : K →ₐ[F] L) :
    liftEmbeddings F K L (x ⊗ₜ y) σ = x * σ y := rfl

/-- The matrix representing `liftEmbeddings` in the bases `b ⊗ 1` on the source and the
embeddings-indexed standard basis on the target is the transpose of `embeddingsMatrixReindex`. -/
theorem toMatrix_liftEmbeddings_eq {F K L ι : Type*}
    [CommRing F] [CommRing K] [CommRing L] [Algebra F K] [Algebra F L]
    [Fintype ι] [DecidableEq ι] [Finite (K →ₐ[F] L)]
    (b : Module.Basis ι F K) (σ : ι ≃ (K →ₐ[F] L)) :
    (liftEmbeddings F K L).toLinearMap.toMatrix (b.baseChange L)
      ((Pi.basisFun _ _).reindex σ.symm) =
    (embeddingsMatrixReindex F L b σ)ᵀ := Matrix.ext fun i j ↦ by
  simp [embeddingsMatrixReindex, LinearMap.toMatrix_apply]

/-- For a finite separable extension `K/F` with `L` algebraically closed, the matrix
of `liftEmbeddings` w.r.t. the bases `b ⊗ 1` and the embeddings-indexed standard basis has
unit determinant. -/
theorem isUnit_det_toMatrix_liftEmbeddings {F K L ι : Type*}
    [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [FiniteDimensional F K] [Algebra.IsSeparable F K] [IsAlgClosed L]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K) (σ : ι ≃ (K →ₐ[F] L)) :
    IsUnit ((liftEmbeddings F K L).toLinearMap.toMatrix (b.baseChange L)
      ((Pi.basisFun _ _).reindex σ.symm)).det := by
  rw [toMatrix_liftEmbeddings_eq, isUnit_iff_ne_zero, det_transpose]
  exact det_embeddingsMatrixReindex_ne_zero b σ

/-- For a finite separable extension `K/F` with `L` algebraically closed, the map
`liftEmbeddings : L ⊗[F] K →ₐ[L] (K →ₐ[F] L) → L` is bijective. -/
theorem liftEmbeddings_bijective (F K L : Type*)
    [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [FiniteDimensional F K] [Algebra.IsSeparable F K] [IsAlgClosed L] :
    Function.Bijective (liftEmbeddings F K L) :=
  let b := Module.finBasis F K
  let σ := (Fintype.equivFinOfCardEq (AlgHom.card F K L)).symm
  (LinearEquiv.ofIsUnitDet <| isUnit_det_toMatrix_liftEmbeddings b σ).bijective

/-- **Stacks 0CKN**.
For a finite separable extension `K/F` with `L` algebraically closed, the canonical
`L`-algebra map `L ⊗[F] K → (K →ₐ[F] L) → L` sending `x ⊗ₜ y` to `σ ↦ x * σ y` is an
isomorphism. -/
@[stacks 0CKN]
noncomputable def liftEmbeddingsEquiv (F K L : Type*)
    [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [Module.Finite F K] [Algebra.IsSeparable F K] [IsAlgClosed L] :
    L ⊗[F] K ≃ₐ[L] ((K →ₐ[F] L) → L) :=
  .ofBijective (liftEmbeddings F K L) (liftEmbeddings_bijective F K L)

@[simp] theorem liftEmbeddingsEquiv_tmul_apply {F K L : Type*}
    [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [Module.Finite F K] [Algebra.IsSeparable F K] [IsAlgClosed L]
    (x : L) (y : K) (σ : K →ₐ[F] L) :
    liftEmbeddingsEquiv F K L (x ⊗ₜ y) σ = x * σ y := rfl

end Algebra
