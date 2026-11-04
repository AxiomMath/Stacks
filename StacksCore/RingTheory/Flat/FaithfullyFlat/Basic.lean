module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Stacks 0H7K: existence of a common field extension. Given two field extensions
`E/K` and `F/K`, the quotient of `E ⊗[K] F` by a maximal ideal is a field over which
both `E` and `F` embed compatibly with the structure maps from `K`. The Lean
statement is more general (it asks only for `[Nontrivial (E ⊗[K] F)]`), which is
automatic in the field case via `Module.FaithfullyFlat.lTensor_nontrivial`. -/

@[expose] public section

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Stacks Lemma 0H7K**: Given two field extensions E/K and F/K, there exists a common field
extension M/K with K-algebra maps E → M and F → M. (The Lean statement is more general but will
apply where `[Field K] [Field E] [Field F]` by virtue of Mathlib instance
`Module.FaithfullyFlat.lTensor_nontrivial`.) -/
@[stacks 0H7K]
theorem exists_common_extension (K : Type u) (E : Type v) (F : Type w) [CommSemiring K]
    [CommRing E] [CommSemiring F] [Algebra K E] [Algebra K F] [Nontrivial (E ⊗[K] F)] :
    ∃ (M : Type (max v w)) (_ : Field M) (_ : Algebra K M) (_ : Algebra E M) (_ : Algebra F M),
    IsScalarTower K E M ∧ IsScalarTower K F M := by
  let ⟨m, _⟩ := Ideal.exists_maximal (E ⊗[K] F)
  refine ⟨E ⊗[K] F ⧸ m, Ideal.Quotient.field m, ?_, ?_, ?_, ?_, ?_⟩ <;> infer_instance

end
