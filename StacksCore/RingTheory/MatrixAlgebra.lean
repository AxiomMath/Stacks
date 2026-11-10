module

public import Mathlib.RingTheory.MatrixAlgebra

/-!
## Base change of matrix algebras

We show that base change commutes with forming matrix algebras: for an algebra `L` over a
commutative ring `K` and a `K`-algebra `A`, there is an `L`-algebra isomorphism
`Matrix n n (L ⊗[K] A) ≃ₐ[L] L ⊗[K] Matrix n n A`.
-/

@[expose] public section

universe u u₂ u₃

open scoped TensorProduct

section MatrixBaseChange

variable (K : Type u) (L : Type u₂) [Field K] [Field L] [Algebra K L]

/-- `matrixEquivTensor` upgraded to be linear over an intermediate field `L`: for a ring `C`
that is both a `K`-algebra and an `L`-algebra compatibly, the isomorphism
`Matrix n n C ≃ C ⊗[K] Matrix n n K` is in fact `L`-linear. -/
def matrixEquivTensorL (K : Type u) (L : Type u₂) [CommRing K] [CommRing L] [Algebra K L]
    (n : Type*) [Fintype n] [DecidableEq n]
    (C : Type*) [Ring C] [Algebra K C] [Algebra L C] [IsScalarTower K L C] :
    Matrix n n C ≃ₐ[L] C ⊗[K] Matrix n n K :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n K C).toRingEquiv) fun l => by
    rw [AlgEquiv.coe_toRingEquiv]
    have key : (matrixEquivTensor n K C).symm (algebraMap L C l ⊗ₜ[K] (1 : Matrix n n K))
        = algebraMap L (Matrix n n C) l := by
      rw [matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
        Algebra.algebraMap_eq_smul_one (R := L) (A := Matrix n n C) l,
        IsScalarTower.algebraMap_smul C l (1 : Matrix n n C)]
    rw [Algebra.TensorProduct.algebraMap_apply, ← key, AlgEquiv.apply_symm_apply]

/-- Base change commutes with matrix algebras: `Matrix n n (L ⊗[K] A) ≃ₐ[L] L ⊗[K] Matrix n n A`. -/
def matrixBaseChange (K : Type u) (L : Type u₂) [CommRing K] [CommRing L] [Algebra K L]
    (n : Type*) [Fintype n] [DecidableEq n] (A : Type*) [Ring A] [Algebra K A] :
    Matrix n n (L ⊗[K] A) ≃ₐ[L] L ⊗[K] Matrix n n A :=
  (matrixEquivTensorL K L n (L ⊗[K] A)).trans <|
    (Algebra.TensorProduct.assoc K K L L A (Matrix n n K)).trans <|
      Algebra.TensorProduct.congr AlgEquiv.refl (matrixEquivTensor n K A).symm

end MatrixBaseChange
