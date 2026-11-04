module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.Units
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.FlatBaseChange
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective

/-!
# Dualizing complexes and adic completion

The base change of a dualizing complex to the adic completion of a Noetherian ring along any
ideal is again a dualizing complex.

## Main results

* `Dualizing.isDualizingComplex_adicCompletion` says that a dualizing complex remains dualizing
  after base change to an adic completion.

## Implementation notes

The completed ring is Mathlib's `AdicCompletion I A`. Since a Noetherian ring's adic completion
is flat, extension of scalars is exact and hence induces the displayed functor on derived
categories. Its value on `K` represents the source's derived tensor product `K ⊗ᴸ_A A^∧` (and,
by flatness, its ordinary extension-of-scalars model).

The two hypotheses of `Dualizing.isDualizingComplex_extendScalars_of_flat` are discharged for
this map by `AdicCompletion.ker_evalOneₐ_eq_map`, which gives `A ⧸ I ≅ A^∧ ⧸ I A^∧`, and by the
fact that `I A^∧` lies in the Jacobson radical of `A^∧`.

This is part (2) of [Stacks, Tag 0DWD]; parts (1) and (3) are in
`StacksFrontier/RingTheory/Dualizing/UbiquityDualizingComplexes/Henselization.lean`, and the
statement conjoining all three is `Dualizing.isDualizingComplex_completion_henselization` in
`StacksFrontier/RingTheory/Dualizing/UbiquityDualizingComplexes/CompletionHenselization.lean`.

## References

* [Stacks Project, Tag 0DWD](https://stacks.math.columbia.edu/tag/0DWD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

local instance extendScalars_additive_adicCompletion
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    (ModuleCat.extendScalars.{u, u, v} f).Additive where
  map_add := by
    intro X Y g h
    let _ := f.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (LinearMap.baseChange B (g.hom + h.hom)) (1 ⊗ₜ[A] x) =
      (LinearMap.baseChange B g.hom + LinearMap.baseChange B h.hom) (1 ⊗ₜ[A] x)
    rw [LinearMap.baseChange_add]

private theorem adicCompletion_exact {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    PreservesFiniteLimits
        (ModuleCat.extendScalars.{u, u, v} (algebraMap A (AdicCompletion I A))) ∧
      PreservesFiniteColimits
        (ModuleCat.extendScalars.{u, u, v} (algebraMap A (AdicCompletion I A))) := by
  let F := ModuleCat.extendScalars.{u, u, v} (algebraMap A (AdicCompletion I A))
  let : F.Additive := extendScalars_additive_adicCompletion _
  let : Module.Flat A (AdicCompletion I A) := AdicCompletion.flat_of_isNoetherian I
  apply ((Functor.exact_tfae F).out 2 4).mp
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact (R := A) (M := AdicCompletion I A) hS

local instance adicCompletion_preservesFiniteLimits {A : Type u}
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, v} (algebraMap A (AdicCompletion I A))) :=
  (adicCompletion_exact I).1

local instance adicCompletion_preservesFiniteColimits {A : Type u}
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, u, v} (algebraMap A (AdicCompletion I A))) :=
  (adicCompletion_exact I).2

/-- **Stacks Project, Tag 0DWD.** The derived base change of a dualizing complex
to the completion of a Noetherian ring along any ideal is a dualizing complex. -/
@[stacks 0DWD "ideal_adic_completion"]
public theorem isDualizingComplex_adicCompletion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))
    (hK : IsDualizingComplex K) :
    IsDualizingComplex
      (((ModuleCat.extendScalars.{u, u, v}
        (algebraMap A (AdicCompletion I A))).mapDerivedCategory).obj K) := by
  have : IsNoetherianRing (AdicCompletion I A) := AdicCompletion.isNoetherianRing I
  have : Module.Flat A (AdicCompletion I A) := AdicCompletion.flat_of_isNoetherian I
  exact isDualizingComplex_extendScalars_of_flat I
    (AdicCompletion.quotientMap_bijective I (Ideal.fg_of_isNoetherianRing I))
    (by simpa [Ideal.jacobson_bot] using
      (AdicCompletion.isUnit_of_isUnit_evalOneₐ_and_isUnit_one_add_and_le_jacobson_bot I).2.2.2.1)
    K hK

end Dualizing
