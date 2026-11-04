module

public import Mathlib.Algebra.Algebra.Tower

/-! # Tower of algebras -/

@[expose] public section

/-- The underlying function of `AlgEquiv.restrictScalarsHom` is `AlgEquiv.restrictScalars`. -/
@[simp] theorem AlgEquiv.coe_restrictScalarsHom (R S A : Type*)
    [CommSemiring R] [CommSemiring S] [Semiring A]
    [Algebra R A] [Algebra R S] [Algebra S A] [IsScalarTower R S A] :
    ⇑(AlgEquiv.restrictScalarsHom R (S := S) (A := A)) = restrictScalars R := rfl

/-- An `S`-linear map is `R`-semilinear along `algebraMap R S`: it turns an `R`-scalar on the
source into the corresponding `S`-scalar on the target.

This is `map_smul` composed with `IsScalarTower.algebraMap_smul`, and it is the form that fires
when the source carries an `R`-action only through the tower. -/
theorem IsScalarTower.map_smul {R S M N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]
    [AddCommMonoid N] [Module S N] (f : M →ₗ[S] N) (r : R) (m : M) :
    f (r • m) = algebraMap R S r • f m := by
  rw [← IsScalarTower.algebraMap_smul S r m, _root_.map_smul]
