module

public import StacksFrontier.Algebra.DifferentialGraded.HomotopyRetractTensor

/-!
# The tensor product of two homomorphisms of differential graded algebras

Let `u : A → A'` and `v : B → B'` be homomorphisms of differential graded algebras over a
commutative ring `R`. Tensoring `u` with the identity of `B` and then the identity of `A'` with
`v` gives the homomorphism
$$u \otimes v : A \otimes_R B \longrightarrow A' \otimes_R B', \qquad
  a \otimes b \longmapsto u(a) \otimes v(b),$$
which is functorial in both arguments and restricts to `u` and to `v` along the two inclusions.

## Main definitions

* `DifferentialGradedAlgebra.tensorHomPair`: the homomorphism `u ⊗ v`.

## Main results

* `DifferentialGradedAlgebra.tensorHomPair_tmul`: its value on a pure tensor.
* `DifferentialGradedAlgebra.tensorHomPair_comp_includeLeft` and
  `DifferentialGradedAlgebra.tensorHomPair_comp_includeRight`: it restricts to `u` and to `v`
  along the two inclusions.
* `DifferentialGradedAlgebra.tensorHomPair_comp_tensorHomPair`: functoriality.
* `DifferentialGradedAlgebra.tensorHomPair_eq_of_eq`: it depends on the two homomorphisms only
  through their underlying algebra homomorphisms.
* `DifferentialGradedAlgebra.tensorHomPair_eq_id`: the tensor product of two homomorphisms
  which are the identity on underlying algebras is the identity.

## Implementation notes

Every identity is proved by `GradedTensorProduct.algHom_ext`, which reduces an equation between
algebra homomorphisms out of a graded tensor product to the two inclusions; the value on a pure
tensor comes from `DifferentialGradedAlgebra.tensorHomLeft_tmul` and
`DifferentialGradedAlgebra.tensorHomRight_tmul`.

## References

* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A A' A'' B B' B'' : DifferentialGradedAlgebra R}

/-- **The tensor product `u ⊗ v : A ⊗_R B → A' ⊗_R B'` of two homomorphisms** of differential
graded algebras. -/
def tensorHomPair (u : A.Hom A') (v : B.Hom B') :
    (tensorProduct A B).Hom (tensorProduct A' B') :=
  (tensorHomLeft u B').comp (tensorHomRight A v)

/-- The tensor product of two homomorphisms applies them to the two factors of a pure tensor. -/
@[simp] theorem tensorHomPair_tmul (u : A.Hom A') (v : B.Hom B') (a : A.A) (b : B.A) :
    (tensorHomPair u v).toAlgebraHom (a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) =
      (u.toAlgebraHom a ᵍ⊗ₜ[R] v.toAlgebraHom b : A'.grading ᵍ⊗[R] B'.grading) := by
  change (tensorHomLeft u B').toAlgebraHom
    ((tensorHomRight A v).toAlgebraHom (a ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading)) = _
  rw [tensorHomRight_tmul, tensorHomLeft_tmul]

/-- The tensor product of two homomorphisms restricts to the first on the first factor. -/
theorem tensorHomPair_comp_includeLeft (u : A.Hom A') (v : B.Hom B') :
    (tensorHomPair u v).toAlgebraHom.comp
        (GradedTensorProduct.includeLeft A.grading B.grading) =
      (GradedTensorProduct.includeLeft A'.grading B'.grading).comp u.toAlgebraHom :=
  AlgHom.ext fun a => by
    change (tensorHomPair u v).toAlgebraHom
      (a ᵍ⊗ₜ[R] (1 : B.A) : A.grading ᵍ⊗[R] B.grading) = _
    rw [tensorHomPair_tmul, map_one]
    rfl

/-- The tensor product of two homomorphisms restricts to the second on the second factor. -/
theorem tensorHomPair_comp_includeRight (u : A.Hom A') (v : B.Hom B') :
    (tensorHomPair u v).toAlgebraHom.comp
        (GradedTensorProduct.includeRight A.grading B.grading) =
      (GradedTensorProduct.includeRight A'.grading B'.grading).comp v.toAlgebraHom :=
  AlgHom.ext fun b => by
    change (tensorHomPair u v).toAlgebraHom
      ((1 : A.A) ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) = _
    rw [tensorHomPair_tmul, map_one]
    rfl

/-- The tensor product of two homomorphisms, on an element of the first factor. -/
theorem tensorHomPair_includeLeft (u : A.Hom A') (v : B.Hom B') (a : A.A) :
    (tensorHomPair u v).toAlgebraHom
        (GradedTensorProduct.includeLeft A.grading B.grading a) =
      GradedTensorProduct.includeLeft A'.grading B'.grading (u.toAlgebraHom a) :=
  congrArg (fun φ => φ a) (tensorHomPair_comp_includeLeft u v)

/-- The tensor product of two homomorphisms, on an element of the second factor. -/
theorem tensorHomPair_includeRight (u : A.Hom A') (v : B.Hom B') (b : B.A) :
    (tensorHomPair u v).toAlgebraHom
        (GradedTensorProduct.includeRight A.grading B.grading b) =
      GradedTensorProduct.includeRight A'.grading B'.grading (v.toAlgebraHom b) :=
  congrArg (fun φ => φ b) (tensorHomPair_comp_includeRight u v)

/-- Algebra homomorphisms out of `A ⊗ B` agreeing on `a ⊗ 1` and `1 ⊗ b` are equal. -/
private theorem tensorProduct_algHom_ext {C : Type*} [Ring C] [Algebra R C]
    {f g : (tensorProduct A B).A →ₐ[R] C}
    (h₁ : ∀ a : A.A, f (a ᵍ⊗ₜ[R] (1 : B.A) : A.grading ᵍ⊗[R] B.grading) =
      g (a ᵍ⊗ₜ[R] (1 : B.A) : A.grading ᵍ⊗[R] B.grading))
    (h₂ : ∀ b : B.A, f ((1 : A.A) ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) =
      g ((1 : A.A) ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading)) : f = g :=
  GradedTensorProduct.algHom_ext A.grading B.grading (AlgHom.ext h₁) (AlgHom.ext h₂)

/-- **Functoriality of the tensor product of homomorphisms.** -/
theorem tensorHomPair_comp_tensorHomPair (u : A.Hom A') (u' : A'.Hom A'') (v : B.Hom B')
    (v' : B'.Hom B'') :
    (tensorHomPair u' v').toAlgebraHom.comp (tensorHomPair u v).toAlgebraHom =
      (tensorHomPair (u'.comp u) (v'.comp v)).toAlgebraHom :=
  tensorProduct_algHom_ext (fun a => by
    simp only [AlgHom.comp_apply, tensorHomPair_tmul, map_one, Hom.comp_toAlgebraHom])
    (fun b => by
      simp only [AlgHom.comp_apply, tensorHomPair_tmul, map_one, Hom.comp_toAlgebraHom])

/-- The tensor product of two homomorphisms depends on them only through the underlying algebra
homomorphisms. -/
theorem tensorHomPair_eq_of_eq {u u₁ : A.Hom A'} {v v₁ : B.Hom B'}
    (hu : u.toAlgebraHom = u₁.toAlgebraHom) (hv : v.toAlgebraHom = v₁.toAlgebraHom) :
    (tensorHomPair u v).toAlgebraHom = (tensorHomPair u₁ v₁).toAlgebraHom :=
  tensorProduct_algHom_ext (fun a => by rw [tensorHomPair_tmul, tensorHomPair_tmul, hu, hv])
    (fun b => by rw [tensorHomPair_tmul, tensorHomPair_tmul, hu, hv])

/-- The tensor product of two homomorphisms which are the identity on underlying algebras is the
identity. -/
theorem tensorHomPair_eq_id {u : A.Hom A} {v : B.Hom B}
    (hu : u.toAlgebraHom = AlgHom.id R A.A) (hv : v.toAlgebraHom = AlgHom.id R B.A) :
    (tensorHomPair u v).toAlgebraHom = AlgHom.id R (tensorProduct A B).A :=
  tensorProduct_algHom_ext (fun a => by rw [tensorHomPair_tmul, hu, hv]; rfl)
    (fun b => by rw [tensorHomPair_tmul, hu, hv]; rfl)

end DifferentialGradedAlgebra
