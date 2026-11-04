module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
## Some lemmas about the tensor product maps
-/

@[expose] public section

variable {R S A B C : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
  [Semiring C] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R S]
  [Algebra S A] [IsScalarTower R S A]

-- note that since `Algebra.TensorProduct.lTensor` is an `abbrev` of `Algebra.TensorProduct.map`,
-- `simp` could already prove the goals, these lemmas are just here for rewrite purposes
lemma Algebra.TensorProduct.lTensor_tmul (f : B →ₐ[R] C) (a : A) (b : B) :
    lTensor (S := S) A f (a ⊗ₜ b) = a ⊗ₜ f b :=
  rfl

lemma Algebra.TensorProduct.lTensor_one_tmul (f : B →ₐ[R] C) (b : B) :
    lTensor (S := S) A f ((1 : A) ⊗ₜ b) = 1 ⊗ₜ f b :=
  lTensor_tmul f 1 b
