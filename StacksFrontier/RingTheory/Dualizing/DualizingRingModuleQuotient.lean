module

public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import StacksFrontier.Homology.ExtendScalars.Flat
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# Dualizing modules along localizations, and quotients of base changes

A dualizing module `ω` of a Noetherian ring `R` gives the dualizing module `S ⊗_R ω` of a
localization `S` of `R` ([Stacks, Tag 0A7G] read on modules placed in one degree). In particular
a dualizing module transports along an isomorphism of rings.

The proof of [Stacks, Tag 0BBV] follows a property of local rings along a sequence of local
homomorphisms `A ⟶ R ⟶ S`: some dualizing module of `S` is a quotient of `S ⊗_A ω_A`. Being a
quotient of a base change is transitive: a surjection `R ⊗_A M ↠ N` and a surjection
`S ⊗_R N ↠ P` give a surjection `S ⊗_A M ↠ P`.

## Main results

* `Stacks.Duality.IsDualizingRingModule.tensor_of_isLocalization`: `S ⊗_R ω` is a dualizing
  module of the localization `S`.
* `Stacks.Duality.IsDualizingRingModule.tensor_of_bijective`: the same along a bijective ring
  homomorphism.
* `Dualizing.exists_surjective_tensor_trans`: transitivity of quotients of base changes.

## References

* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- **A dualizing module localizes** ([Stacks, Tag 0A7G]): for a localization `S` of the
Noetherian ring `R` and a dualizing `R`-module `ω`, the `S`-module `S ⊗_R ω` is dualizing. -/
theorem IsDualizingRingModule.tensor_of_isLocalization {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] (M : Submonoid R)
    [IsLocalization M S] {ω : Type u} [AddCommGroup ω] [Module R ω]
    (hω : IsDualizingRingModule R ω) : IsDualizingRingModule S (S ⊗[R] ω) := by
  obtain ⟨hfin, n, hn⟩ := hω
  refine ⟨inferInstance, n, ?_⟩
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S M))
  have h := Dualizing.isDualizingComplex_extendScalars_of_isLocalization (B := S) M _ hn
  exact Dualizing.isDualizingComplex_of_iso
    (((ModuleCat.extendScalars (algebraMap R S)).mapDerivedCategorySingleFunctor n).app
        (ModuleCat.of R ω) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) n).mapIso
        (PseudoCoherence.extendScalarsAlgebraMapObjIso (ModuleCat.of R ω))) h

/-- **A dualizing module transports along an isomorphism of rings**: for a bijective ring
homomorphism `R ⟶ S` and a dualizing `R`-module `ω`, the `S`-module `S ⊗_R ω` is dualizing. -/
theorem IsDualizingRingModule.tensor_of_bijective {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    (hbij : Function.Bijective (algebraMap R S)) {ω : Type u} [AddCommGroup ω] [Module R ω]
    (hω : IsDualizingRingModule R ω) : IsDualizingRingModule S (S ⊗[R] ω) :=
  have : IsLocalization (Submonoid.powers (1 : R)) S :=
    IsLocalization.away_of_isUnit_of_bijective S isUnit_one hbij
  hω.tensor_of_isLocalization (Submonoid.powers 1)

end Stacks.Duality

namespace Dualizing

/-- **Quotients of base changes compose.** For ring homomorphisms `φ : A ⟶ R` and
`ψ : R ⟶ S`, a surjection `R ⊗_A M ↠ N` and a surjection `S ⊗_R N ↠ P` give a surjection
`S ⊗_A M ↠ P`, through `S ⊗_A M = S ⊗_R (R ⊗_A M)`. -/
theorem exists_surjective_tensor_trans {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    (φ : A →+* R) (ψ : R →+* S) (χ : A →+* S) (hχ : ψ.comp φ = χ) (M N P : Type u)
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module S P]
    (hπ : letI := φ.toAlgebra; ∃ π : R ⊗[A] M →ₗ[R] N, Function.Surjective π)
    (hσ : letI := ψ.toAlgebra; ∃ σ : S ⊗[R] N →ₗ[S] P, Function.Surjective σ) :
    letI := χ.toAlgebra; ∃ τ : S ⊗[A] M →ₗ[S] P, Function.Surjective τ := by
  subst hχ
  let := φ.toAlgebra
  let := ψ.toAlgebra
  let := (ψ.comp φ).toAlgebra
  have : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨π, hπ⟩ := hπ
  obtain ⟨σ, hσ⟩ := hσ
  refine ⟨σ ∘ₗ π.baseChange S ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A R S S M).symm.toLinearMap, ?_⟩
  exact hσ.comp ((LinearMap.lTensor_surjective S hπ).comp (LinearEquiv.surjective _))

/-- **Dualizing quotients of base changes compose.** For ring homomorphisms `φ : A ⟶ R` and
`ψ : R ⟶ S` of Noetherian rings, if some dualizing module of `R` is a quotient of `R ⊗_A M`,
and for every dualizing module `N` of `R` some dualizing module of `S` is a quotient of
`S ⊗_R N`, then some dualizing module of `S` is a quotient of `S ⊗_A M`. -/
theorem exists_isDualizingRingModule_quotient_trans {A R S : Type u} [CommRing A] [CommRing R]
    [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S] (φ : A →+* R) (ψ : R →+* S)
    (χ : A →+* S) (hχ : ψ.comp φ = χ) (M : Type u) [AddCommGroup M] [Module A M]
    (hR : letI := φ.toAlgebra
      ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N),
        Stacks.Duality.IsDualizingRingModule R N ∧
          ∃ π : R ⊗[A] M →ₗ[R] N, Function.Surjective π)
    (hS : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Stacks.Duality.IsDualizingRingModule R N →
        letI := ψ.toAlgebra
        ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module S P),
          Stacks.Duality.IsDualizingRingModule S P ∧
            ∃ σ : S ⊗[R] N →ₗ[S] P, Function.Surjective σ) :
    letI := χ.toAlgebra
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module S P),
      Stacks.Duality.IsDualizingRingModule S P ∧
        ∃ τ : S ⊗[A] M →ₗ[S] P, Function.Surjective τ := by
  obtain ⟨N, _, _, hN, hπ⟩ := hR
  obtain ⟨P, _, _, hP, hσ⟩ := hS N hN
  exact ⟨P, _, _, hP, exists_surjective_tensor_trans φ ψ χ hχ M N P hπ hσ⟩

/-- **Along a localization, `S ⊗_R N` is a dualizing quotient of itself** for every dualizing
module `N` of `R` ([Stacks, Tag 0A7G]). -/
theorem exists_isDualizingRingModule_quotient_of_isLocalization {R S : Type u} [CommRing R]
    [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S] (ψ : R →+* S) (L : Submonoid R)
    (hψ : letI := ψ.toAlgebra; IsLocalization L S) (N : Type u) [AddCommGroup N] [Module R N]
    (hN : Stacks.Duality.IsDualizingRingModule R N) :
    letI := ψ.toAlgebra
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module S P),
      Stacks.Duality.IsDualizingRingModule S P ∧
        ∃ σ : S ⊗[R] N →ₗ[S] P, Function.Surjective σ := by
  let := ψ.toAlgebra
  exact ⟨S ⊗[R] N, _, _, hN.tensor_of_isLocalization L, LinearMap.id, Function.surjective_id⟩

/-- **Along an isomorphism of rings, `S ⊗_R N` is a dualizing quotient of itself** for every
dualizing module `N` of `R`. -/
theorem exists_isDualizingRingModule_quotient_of_bijective {R S : Type u} [CommRing R]
    [CommRing S] [IsNoetherianRing R] [IsNoetherianRing S] (ψ : R →+* S)
    (hψ : Function.Bijective ψ) (N : Type u) [AddCommGroup N] [Module R N]
    (hN : Stacks.Duality.IsDualizingRingModule R N) :
    letI := ψ.toAlgebra
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module S P),
      Stacks.Duality.IsDualizingRingModule S P ∧
        ∃ σ : S ⊗[R] N →ₗ[S] P, Function.Surjective σ := by
  let := ψ.toAlgebra
  exact ⟨S ⊗[R] N, _, _, hN.tensor_of_bijective hψ, LinearMap.id, Function.surjective_id⟩

end Dualizing

end
