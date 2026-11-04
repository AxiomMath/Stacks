module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AnalyticallyUnramified.Defs
public import StacksFrontier.RingTheory.Flat.ReducedFibres
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.Nagata.IntegralClosure

/-!
# Finiteness of integral closure over an analytically unramified base

Let `A` be an analytically unramified Noetherian local ring, let `B` be an `A`-algebra of finite
type and let `L` be a `B`-algebra which is flat, formally unramified and essentially of finite
type over `A`. Then the integral closure of `B` in `L` is a finite `B`-module.

## Main results

* `adicCompletion_isNagata`: the completion of a Noetherian local ring at its maximal ideal is a
  Nagata ring.
* `isReduced_of_formallyUnramified_of_flat`: a flat formally unramified algebra essentially of
  finite type over a reduced Noetherian ring is reduced.
* `finite_integralClosure_of_faithfullyFlat`: finiteness of integral closure descends along a
  faithfully flat Nagata algebra with reduced base change.
* `finite_integralClosure_of_reduced_baseChange`: the relative form of the previous statement over
  an algebra of finite type.
* `finite_integralClosure_of_essentiallyEtale`: over an analytically unramified Noetherian local
  ring `A`, the integral closure of a finite type `A`-algebra `B` in a flat, formally unramified
  `B`-algebra essentially of finite type over `A` is a finite `B`-module.
* `finite_integralClosure_of_finite_family`: integral closure is finite when the algebra embeds in
  a finite product of algebras with finite integral closure.

## References

* [Stacks Project, Tag 0BG8](https://stacks.math.columbia.edu/tag/0BG8)
-/

@[expose] public section

open scoped TensorProduct

universe u

/-- The completion of a Noetherian local ring at its maximal ideal is a Nagata ring. -/
theorem adicCompletion_isNagata (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsNagataRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  obtain ⟨_, h⟩ := completion_noetherian A (IsLocalRing.maximalIdeal A) inferInstance
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  have : IsPrecomplete (IsLocalRing.maximalIdeal Ahat) Ahat := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact h.toIsPrecomplete
  exact IsNagataRing.of_isPrecomplete_maximalIdeal

/-- Finiteness of integral closure descends from a faithfully flat Nagata algebra `S` whose
tensor product with the ambient algebra `L` is reduced. -/
theorem finite_integralClosure_of_faithfullyFlat
    {R S L : Type u} [CommRing R] [CommRing S] [CommRing L]
    [Algebra R S] [Algebra R L] [Module.FaithfullyFlat R S]
    [Algebra.EssFiniteType R L] [IsReduced (S ⊗[R] L)]
    (hS : IsNagataRing S) : Module.Finite R (integralClosure R L) := by
  have : IsNoetherianRing S := hS.1
  have : Module.Finite S (integralClosure S (S ⊗[R] L)) :=
    IsIntegralClosure.finite_of_essFiniteType_of_isReduced (S := S ⊗[R] L) hS.2
  have : Module.Finite S (S ⊗[R] integralClosure R L) :=
    Module.Finite.of_injective (TensorProduct.toIntegralClosure R S L).toLinearMap
      TensorProduct.toIntegralClosure_injective_of_flat
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

/-- A flat, formally unramified algebra essentially of finite type over a reduced Noetherian ring
is reduced. -/
theorem isReduced_of_formallyUnramified_of_flat
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsReduced R] [Algebra.EssFiniteType R S]
    [Module.Flat R S] [Algebra.FormallyUnramified R S] : IsReduced S := by
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  exact isReduced_of_flat_of_isReduced_fiber (R := R) fun p _ ↦
    Algebra.FormallyUnramified.isReduced_of_field p.ResidueField (p.Fiber S)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Over an algebra `B` of finite type over `A`, the integral closure of `B` in `L` is finite as
soon as some faithfully flat Nagata `A`-algebra `S` has `S ⊗[A] L` reduced. -/
theorem finite_integralClosure_of_reduced_baseChange
    {A B L S : Type u} [CommRing A] [CommRing B] [CommRing L] [CommRing S]
    [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    [Algebra A S] [Module.FaithfullyFlat A S]
    [Algebra.FiniteType A B] [Algebra.EssFiniteType A L]
    [IsReduced (S ⊗[A] L)] (hS : IsNagataRing S) :
    Module.Finite B (integralClosure B L) := by
  let C := B ⊗[A] S
  have : Algebra.EssFiniteType B L := Algebra.EssFiniteType.of_comp A B L
  have : Algebra.FiniteType S C :=
    Algebra.FiniteType.of_surjective (Algebra.TensorProduct.commRight A S B).toAlgHom
      (Algebra.TensorProduct.commRight A S B).surjective
  have hfinite : ∀ (D : Type u) [CommRing D] [Algebra S D] [Algebra.FiniteType S D],
      IsNagataRing D := ((isNagataRing_tfae (R := S)).out 1 2).mp hS
  let e : (C ⊗[B] L) ≃+* (S ⊗[A] L) :=
    (Algebra.TensorProduct.comm B C L).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange A B B L S).toRingEquiv.trans
        (Algebra.TensorProduct.comm A L S).toRingEquiv)
  have : IsReduced (C ⊗[B] L) := isReduced_of_injective e e.injective
  exact finite_integralClosure_of_faithfullyFlat (S := C) (hfinite C)

/-- Over an analytically unramified Noetherian local ring `A`, the integral closure of a finite
type `A`-algebra `B` in a flat, formally unramified `B`-algebra `L` essentially of finite type
over `A` is a finite `B`-module. -/
theorem finite_integralClosure_of_essentiallyEtale
    {A B L : Type u} [CommRing A] [CommRing B] [CommRing L]
    [IsLocalRing A] [IsNoetherianRing A]
    [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    [Algebra.FiniteType A B] [Algebra.EssFiniteType A L]
    [Module.Flat A L] [Algebra.FormallyUnramified A L]
    (hA : IsAnalyticallyUnramified A) : Module.Finite B (integralClosure B L) := by
  let S := AdicCompletion (IsLocalRing.maximalIdeal A) A
  have : Module.FaithfullyFlat A S :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson
      (IsLocalRing.maximalIdeal A) (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  have : IsReduced S := hA
  have hS : IsNagataRing S := adicCompletion_isNagata A
  have : IsNoetherianRing S := hS.1
  have : IsReduced (S ⊗[A] L) := isReduced_of_formallyUnramified_of_flat S (S ⊗[A] L)
  exact finite_integralClosure_of_reduced_baseChange (A := A) (S := S) hS

/-- If an `R`-algebra `L` embeds into a finite product of `R`-algebras each with finite integral
closure over `R`, then the integral closure of `R` in `L` is a finite `R`-module. -/
theorem finite_integralClosure_of_finite_family
    {R L : Type*} [CommRing R] [CommRing L] [Algebra R L] [IsNoetherianRing R]
    {ι : Type*} [Finite ι] (K : ι → Type*) [∀ i, CommRing (K i)]
    [∀ i, Algebra R (K i)] (φ : ∀ i, L →ₐ[R] K i)
    (hφ : Function.Injective (fun x i => φ i x))
    [∀ i, Module.Finite R (integralClosure R (K i))] :
    Module.Finite R (integralClosure R L) := by
  exact Module.Finite.of_injective (LinearMap.pi fun i ↦ (φ i).mapIntegralClosure.toLinearMap)
    fun _ _ h ↦ Subtype.ext <| hφ <| funext fun i ↦ congrArg Subtype.val (congrFun h i)

end
