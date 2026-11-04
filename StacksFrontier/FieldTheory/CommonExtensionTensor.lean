module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# A common extension of two field extensions

Two field extensions `K/k` and `K'/k` embed, compatibly with `k`, into a common field extension
`Ω/k`: the tensor product `K ⊗_k K'` is a nonzero ring, and its quotient by a maximal ideal is such
a field, receiving `K` and `K'` through the two inclusions of the tensor product. The common
extension lies in the same universe as `K` and `K'`.

## Main results

* `exists_field_isScalarTower_isScalarTower`: a common extension field `Ω` of `K/k` and `K'/k`.
-/

@[expose] public section

open scoped TensorProduct

universe u

/-- **Two field extensions of `k` have a common extension.** For field extensions `K/k` and
`K'/k` there is a field `Ω` with `k`-compatible embeddings of `K` and `K'`: a quotient of
`K ⊗_k K'` by a maximal ideal. -/
theorem exists_field_isScalarTower_isScalarTower (k K K' : Type u) [Field k] [Field K]
    [Field K'] [Algebra k K] [Algebra k K'] :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra k Ω) (_ : Algebra K Ω) (_ : Algebra K' Ω),
      IsScalarTower k K Ω ∧ IsScalarTower k K' Ω := by
  have := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k K K'
    (algebraMap k K).injective (algebraMap k K').injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[k] K')
  let := Ideal.Quotient.field m
  let : Algebra K ((K ⊗[k] K') ⧸ m) :=
    ((Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom).toAlgebra
  let : Algebra K' ((K ⊗[k] K') ⧸ m) :=
    ((Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
  refine ⟨(K ⊗[k] K') ⧸ m, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact IsScalarTower.of_algebraMap_eq fun _ => rfl
  · exact IsScalarTower.of_algebraMap_eq fun a =>
      congrArg (Ideal.Quotient.mk m) (Algebra.TensorProduct.algebraMap_apply' a)

end
