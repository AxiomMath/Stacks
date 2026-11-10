module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor, symmetric and exterior algebras commute with base change

Let `R` be a commutative semiring, `A` a commutative `R`-algebra and `M` an `R`-module (rings
and an additive group for the exterior algebra). Forming the tensor, symmetric and exterior
algebras commutes with base change along `R → A`, sending `ι (a ⊗ₜ m)` to `a ⊗ₜ ι m`.

Taking `A = S⁻¹R` (any `A` with `IsLocalization S A`) gives Stacks 0C6F: `A ⊗[R] M` is a model of
`S⁻¹M` by `IsLocalization.tensorProduct_isLocalizedModule`, and `A ⊗[R] B` is the localization of
an `R`-algebra `B`.
-/

@[expose] public section

open scoped TensorProduct

section Semiring

variable (R : Type*) [CommSemiring R] (A : Type*) [CommSemiring A] [Algebra R A]
    (M : Type*) [AddCommMonoid M] [Module R M]

/-- The tensor algebra of a base change is isomorphic to the base change of the tensor
algebra, sending `ι (1 ⊗ₜ m)` to `1 ⊗ₜ ι m`.
Taking `A = S⁻¹R` gives compatibility with localization. -/
@[stacks 0C6F "(1)"]
theorem TensorAlgebra.exists_algEquiv_baseChange :
    ∃ e : TensorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] TensorAlgebra R M,
      ∀ m : M, e (ι A (1 ⊗ₜ[R] m)) = 1 ⊗ₜ[R] ι R m :=
  ⟨.ofAlgHom (lift A ((ι R).baseChange A))
      (AlgHom.liftEquiv R A _ _ (lift R ((ι A).restrictScalars R ∘ₗ TensorProduct.mk R A M 1)))
      (by ext; simp) (by ext; simp), fun m => by simp⟩

/-- The symmetric algebra of a base change is isomorphic to the base change of the symmetric
algebra, sending `ι (1 ⊗ₜ m)` to `1 ⊗ₜ ι m`.
Taking `A = S⁻¹R` gives compatibility with localization. -/
@[stacks 0C6F "(2)"]
theorem SymmetricAlgebra.exists_algEquiv_baseChange :
    ∃ e : SymmetricAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] SymmetricAlgebra R M,
      ∀ m : M, e (ι A (A ⊗[R] M) (1 ⊗ₜ[R] m)) = 1 ⊗ₜ[R] ι R M m :=
  ⟨.ofAlgHom (lift ((ι R M).baseChange A))
      (AlgHom.liftEquiv R A _ _
        (lift ((ι A (A ⊗[R] M)).restrictScalars R ∘ₗ TensorProduct.mk R A M 1)))
      (by ext; simp) (by ext; simp), fun m => by simp⟩

end Semiring

section helper

variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
  {M : Type*} [AddCommMonoid M] [Module R M] {B : Type*} [Semiring B] [Algebra R B]

/-- If every `f m` squares to zero, so does every value of the base change of `f`. -/
theorem LinearMap.baseChange_mul_self_eq_zero (f : M →ₗ[R] B) (hf : ∀ m, f m * f m = 0)
    (x : A ⊗[R] M) : f.baseChange A x * f.baseChange A x = 0 := by
  have anti (m n : M) : f m * f n + f n * f m = 0 := by
    have := hf (m + n)
    rwa [map_add, add_mul, mul_add, mul_add, hf m, hf n, zero_add, add_zero] at this
  have anti' (x y : A ⊗[R] M) :
      f.baseChange A x * f.baseChange A y + f.baseChange A y * f.baseChange A x = 0 := by
    have h : (LinearMap.mul A (A ⊗[R] B)).compl₁₂ (f.baseChange A) (f.baseChange A) +
        ((LinearMap.mul A (A ⊗[R] B)).compl₁₂ (f.baseChange A) (f.baseChange A)).flip = 0 := by
      ext a m
      simp [← TensorProduct.tmul_add, anti]
    simpa using congr($h x y)
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, hf, TensorProduct.tmul_zero]
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, add_mul, mul_add, mul_add, h₁, h₂, zero_add, add_zero, anti']

end helper

section Ring

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M]

/-- The exterior algebra of a base change is isomorphic to the base change of the exterior
algebra, sending `ι (1 ⊗ₜ m)` to `1 ⊗ₜ ι m`.
Taking `A = S⁻¹R` gives compatibility with localization. -/
@[stacks 0C6F "(3)"]
theorem ExteriorAlgebra.exists_algEquiv_baseChange :
    ∃ e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M,
      ∀ m : M, e (ι A (1 ⊗ₜ[R] m)) = 1 ⊗ₜ[R] ι R m :=
  ⟨.ofAlgHom
      (lift A ⟨(ι R).baseChange A, (ι R).baseChange_mul_self_eq_zero (ι_sq_zero (R := R))⟩)
      (AlgHom.liftEquiv R A _ _ (lift R ⟨(ι A).restrictScalars R ∘ₗ TensorProduct.mk R A M 1,
        fun m => by rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, ι_sq_zero]⟩))
      (by ext; simp) (by ext; simp), fun m => by simp⟩

end Ring
