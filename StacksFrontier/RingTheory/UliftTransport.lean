module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Formal smoothness and pushout squares under universe lifting

A ring `R : Type u` and its universe lift `ULift.{v} R : Type (max u v)` are isomorphic, so no
ring-theoretic property distinguishes them; but a *statement* about `ULift.{v} R` is not a
statement about `R`, and the instances it mentions have to be produced. This file produces two of
them: formal smoothness of the universe lift of a formally smooth ring map, and the pushout
property of the universe lift of a tensor-product square.

## Main results

* `RingHom.FormallySmooth.ulift`: the universe lift `ULift R → ULift S` of a formally smooth ring
  map `R → S` is formally smooth.
* `Algebra.FormallySmooth.ulift`: the same, for the algebra structure on `ULift A` over `ULift R`
  whose structure map is the lift of `algebraMap R A`.
* `Algebra.uliftTensorProductEquiv`: `ULift (A ⊗[R] B)` is `ULift A ⊗[ULift R] ULift B`, as an
  algebra over `ULift A`.
* `Algebra.IsPushout.ulift_tensorProduct`: consequently the universe lift of the square
  `R → A`, `R → B`, `A → A ⊗[R] B`, `B → A ⊗[R] B` is again a pushout square of commutative
  rings.
* `Algebra.uliftTensorProductEquiv'`: the same isomorphism as
  `Algebra.uliftTensorProductEquiv` for an arbitrary `ULift A`-algebra structure on
  `ULift (A ⊗[R] B)` whose structure map is the lift of `A → A ⊗[R] B`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w u₁ u₂

/-! ### Formal smoothness -/

/-- **The universe lift of a formally smooth ring map is formally smooth.** -/
theorem RingHom.FormallySmooth.ulift {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} (hf : f.FormallySmooth) :
    (RingHom.ulift.{u₁, u₂} f).FormallySmooth :=
  RingHom.FormallySmooth.comp
    (RingHom.FormallySmooth.comp
      (RingHom.FormallySmooth.of_bijective
        (f := (ULift.ringEquiv : ULift.{u₁} R ≃+* R).toRingHom)
        (ULift.ringEquiv : ULift.{u₁} R ≃+* R).bijective) hf)
    (RingHom.FormallySmooth.of_bijective
      (f := (ULift.ringEquiv : ULift.{u₂} S ≃+* S).symm.toRingHom)
      (ULift.ringEquiv : ULift.{u₂} S ≃+* S).symm.bijective)

attribute [local instance] ULift.algebra' in
/-- **The universe lift of a formally smooth algebra is formally smooth.** The algebra structure
is `ULift.algebra'`, whose structure map is the lift of `algebraMap R A`. -/
theorem Algebra.FormallySmooth.ulift {R : Type u} [CommRing R] {A : Type v} [CommRing A]
    [Algebra R A] [Algebra.FormallySmooth R A] :
    Algebra.FormallySmooth (ULift.{u₁} R) (ULift.{u₂} A) := by
  rw [← RingHom.formallySmooth_algebraMap]
  exact RingHom.FormallySmooth.ulift.{u, v, u₁, u₂}
    (RingHom.formallySmooth_algebraMap.2 ‹Algebra.FormallySmooth R A›)

/-! ### Pushout squares -/

attribute [local instance] ULift.algebra' Algebra.TensorProduct.rightAlgebra

/-- **`ULift (A ⊗[R] B)` is `ULift A ⊗[ULift R] ULift B` as a `ULift A`-algebra.** The underlying
ring isomorphism is the inverse of `Algebra.TensorProduct.uliftEquiv`. -/
def Algebra.uliftTensorProductEquiv (R : Type u) [CommRing R] (A : Type u) [CommRing A]
    [Algebra R A] (B : Type u) [CommRing B] [Algebra R B] :
    ULift.{v} A ⊗[ULift.{v} R] ULift.{v} B ≃ₐ[ULift.{v} A] ULift.{v} (A ⊗[R] B) :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.uliftEquiv.{v, v, v, v} R A A B).symm.toRingEquiv)
    fun a => by
      change (Algebra.TensorProduct.uliftEquiv.{v, v, v, v} R A A B).symm
          (a ⊗ₜ[ULift.{v} R] (1 : ULift.{v} B)) =
        ULift.up (algebraMap A (A ⊗[R] B) a.down)
      rw [Algebra.TensorProduct.uliftEquiv_symm_tmul]
      rfl

/-- **The universe lift of a tensor-product square of commutative rings is a pushout square.**
For ring maps `R → A` and `R → B`, the square with corners `ULift R`, `ULift A`, `ULift B` and
`ULift (A ⊗[R] B)` is a pushout square: `ULift (A ⊗[R] B)` is the tensor product of `ULift A` and
`ULift B` over `ULift R`. -/
theorem Algebra.IsPushout.ulift_tensorProduct (R : Type u) [CommRing R] (A : Type u) [CommRing A]
    [Algebra R A] (B : Type u) [CommRing B] [Algebra R B] :
    letI : Algebra (ULift.{v} R) (ULift.{v} (A ⊗[R] B)) :=
      ULift.algebra' R (ULift.{v} (A ⊗[R] B))
    letI : Algebra (ULift.{v} A) (ULift.{v} (A ⊗[R] B)) :=
      ULift.algebra' A (ULift.{v} (A ⊗[R] B))
    letI : Algebra (ULift.{v} B) (ULift.{v} (A ⊗[R] B)) :=
      ULift.algebra' B (ULift.{v} (A ⊗[R] B))
    Algebra.IsPushout (ULift.{v} R) (ULift.{v} A) (ULift.{v} B) (ULift.{v} (A ⊗[R] B)) := by
  have key : ∀ (X : Type u) [CommRing X] [Algebra R X] [Algebra X (A ⊗[R] B)]
      [IsScalarTower R X (A ⊗[R] B)],
      IsScalarTower (ULift.{v} R) (ULift.{v} X) (ULift.{v} (A ⊗[R] B)) := fun X _ _ _ _ =>
    IsScalarTower.of_algebraMap_eq fun r =>
      ULift.ext (IsScalarTower.algebraMap_apply R X (A ⊗[R] B) r.down)
  have := key A
  have := key B
  exact Algebra.IsPushout.of_equiv (h := TensorProduct.isPushout)
    (Algebra.uliftTensorProductEquiv.{u, v} R A B) (RingHom.ext fun _ => rfl)

/-- **`Algebra.uliftTensorProductEquiv` for a prescribed algebra structure on the target.** For any
`ULift A`-algebra structure on `ULift (A ⊗[R] B)` whose structure map is the universe lift of
`A → A ⊗[R] B`, the isomorphism `ULift A ⊗[ULift R] ULift B ≃ ULift (A ⊗[R] B)` of
`Algebra.uliftTensorProductEquiv` is an isomorphism of `ULift A`-algebras for that structure. -/
def Algebra.uliftTensorProductEquiv' (R : Type u) [CommRing R] (A : Type u) [CommRing A]
    [Algebra R A] (B : Type u) [CommRing B] [Algebra R B]
    [iAT : Algebra (ULift.{v} A) (ULift.{v} (A ⊗[R] B))]
    (h : ∀ a : ULift.{v} A, algebraMap (ULift.{v} A) (ULift.{v} (A ⊗[R] B)) a =
      ULift.up (algebraMap A (A ⊗[R] B) a.down)) :
    ULift.{v} A ⊗[ULift.{v} R] ULift.{v} B ≃ₐ[ULift.{v} A] ULift.{v} (A ⊗[R] B) :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.uliftEquiv.{v, v, v, v} R A A B).symm.toRingEquiv)
    fun a => by
      rw [h]
      change (Algebra.TensorProduct.uliftEquiv.{v, v, v, v} R A A B).symm
          (a ⊗ₜ[ULift.{v} R] (1 : ULift.{v} B)) =
        ULift.up (algebraMap A (A ⊗[R] B) a.down)
      rw [Algebra.TensorProduct.uliftEquiv_symm_tmul]
      rfl

end
