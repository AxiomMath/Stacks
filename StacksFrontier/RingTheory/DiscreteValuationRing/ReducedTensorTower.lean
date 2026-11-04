module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Functoriality of reduced tensor products

This file contains the canonical maps needed when comparing the reduced composita occurring in
Tags 09EQ and 0GLR.  Importantly, no assertion is made that reduction commutes with a further
tensor product: that assertion is false without additional hypotheses in the inseparable,
nonexcellent case.

## Main definitions

* `ReducedTensorTower.Reduction`: The reduction `A ⧸ nilradical A` of a commutative ring.
* `ReducedTensorTower.reductionMap`: The map of reductions induced by an algebra homomorphism.
* `ReducedTensorTower.reductionEquiv`: The equivalence of reductions induced by an algebra
  equivalence.
* `ReducedTensorTower.reducedTensorMap`: The map of reduced tensor products induced by algebra
  homomorphisms on both factors.

## Main results

* `ReducedTensorTower.reductionMap_id`: Reduction sends the identity to the identity.
* `ReducedTensorTower.reductionMap_comp`: Reduction sends a composite to the composite of the
  reductions.

## Implementation notes

The content is pure commutative algebra — reductions of rings, and the functoriality of the
reduction of a tensor product — and mentions no valuation theory. It lives under
`RingTheory/DiscreteValuationRing/` because that is where its consumers are: the reduced
composita of Tags 09EQ, 0GLR and 09II. Nothing here is derived-categorical.

This module depends on Mathlib alone, and on three specific files rather than on a
whole-library import: the three imports above supply `Ideal.Quotient.mk`, `Ideal.quotientMapₐ`,
`Ideal.quotientEquivAlg`, `nilradical` and the `⧸` notation.
-/

@[expose] public section

open scoped TensorProduct

namespace ReducedTensorTower

universe uR uA uB uC uD

/-- The reduction of a commutative ring. -/
public abbrev Reduction (A : Type uA) [CommRing A] := A ⧸ nilradical A

/-- A homomorphism induces a homomorphism on reductions. -/
public noncomputable def reductionMap
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : Reduction A →ₐ[R] Reduction B :=
  Ideal.quotientMapₐ (nilradical B) f fun x hx => by
    rw [Ideal.mem_comap]
    exact mem_nilradical.mpr ((mem_nilradical.mp hx).map f)

/-- The map `reductionMap f` sends the class of `x` to the class of `f x`. -/
@[simp]
public theorem reductionMap_mk
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (x : A) :
    reductionMap f (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x) := rfl

/-- The identity homomorphism induces the identity on reductions. -/
@[simp]
public theorem reductionMap_id
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A] :
    reductionMap (AlgHom.id R A) = AlgHom.id R (Reduction A) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The map of reductions induced by a composite `g.comp f` is the composite of the maps induced by
`g` and `f`. -/
@[simp]
public theorem reductionMap_comp
    {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (g : B →ₐ[R] C) (f : A →ₐ[R] B) :
    reductionMap (g.comp f) = (reductionMap g).comp (reductionMap f) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- An algebra equivalence induces an equivalence of reductions. -/
public noncomputable def reductionEquiv
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) : Reduction A ≃ₐ[R] Reduction B :=
  Ideal.quotientEquivAlg (nilradical A) (nilradical B) e (by
    have h : Ideal.comap (e : A →+* B) (nilradical B) = nilradical A := by
      ext x
      simp only [Ideal.mem_comap, mem_nilradical]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg e.symm hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg e hn⟩
    rw [← h, Ideal.map_comap_of_surjective (e : A →+* B) e.surjective])

/-- The equivalence `reductionEquiv e` sends the class of `x` to the class of `e x`. -/
@[simp]
public theorem reductionEquiv_mk
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (x : A) :
    reductionEquiv e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (e x) := rfl

/-- The natural map between reduced tensor products induced by maps on both factors. -/
public noncomputable def reducedTensorMap
    {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] B) (g : C →ₐ[R] D) :
    Reduction (A ⊗[R] C) →ₐ[R] Reduction (B ⊗[R] D) :=
  reductionMap (Algebra.TensorProduct.map f g)

/-- The map `reducedTensorMap f g` sends the class of `a ⊗ₜ c` to the class of `f a ⊗ₜ g c`. -/
@[simp]
public theorem reducedTensorMap_tmul
    {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] B) (g : C →ₐ[R] D) (a : A) (c : C) :
    reducedTensorMap f g (Ideal.Quotient.mk _ (a ⊗ₜ[R] c)) =
      Ideal.Quotient.mk _ (f a ⊗ₜ[R] g c) := by
  rfl

/-- The map `reducedTensorMap f g` sends the class of `a ⊗ₜ 1` to the class of `f a ⊗ₜ 1`. -/
@[simp]
public theorem reducedTensorMap_includeLeft
    {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] B) (g : C →ₐ[R] D) (a : A) :
    reducedTensorMap f g (Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C) a)) =
      Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] D) (f a)) := by
  simp [Algebra.TensorProduct.includeLeft_apply]

/-- The map `reducedTensorMap f g` sends the class of `1 ⊗ₜ c` to the class of `1 ⊗ₜ g c`. -/
@[simp]
public theorem reducedTensorMap_includeRight
    {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] B) (g : C →ₐ[R] D) (c : C) :
    reducedTensorMap f g (Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C) c)) =
      Ideal.Quotient.mk _ ((Algebra.TensorProduct.includeRight : D →ₐ[R] B ⊗[R] D) (g c)) := by
  simp [Algebra.TensorProduct.includeRight_apply]

end ReducedTensorTower

namespace IsDiscreteValuationRing

namespace ReducedTensorTower

-- Compatibility aliases for the valuation-theory namespace used by older consumers.
export _root_.ReducedTensorTower
  (Reduction reductionMap reductionMap_mk reductionMap_id reductionMap_comp reductionEquiv
    reductionEquiv_mk reducedTensorMap reducedTensorMap_tmul reducedTensorMap_includeLeft
    reducedTensorMap_includeRight)

end ReducedTensorTower

end IsDiscreteValuationRing
