module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.FlatBaseChange

/-!
# The dimension function read at an arbitrary presentation of the local ring

`Dualizing.dualizingDimension K p` is defined through the particular ring
`Localization.AtPrime p.asIdeal`. For an arbitrary ring `R` presenting that localization,
`n = δ_K(p)` exactly when the extension of `K` to `R`, shifted by `-n`, is a normalized
dualizing complex over `R`.

## Main results

* `Dualizing.isNormalizedDualizingComplex_extendScalars_iff_eq_dualizingDimension`: the
  characterisation of `δ_K(p)` at an arbitrary presentation `R` of the localization at `p`.
* `Dualizing.isNormalizedDualizingComplex_derivedExtensionScalars_iff_eq_dualizingDimension`:
  the same characterisation, with the extension of scalars written as
  `StacksDraft.PseudoCoherence.derivedExtensionScalars`.
* `Dualizing.isNormalizedDualizingComplex_extendScalars_dualizingDimension`: the shift by
  `-δ_K(p)` of the extension to `R` is normalized.

## References

* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0AWD](https://stacks.math.columbia.edu/tag/0AWD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence (derivedExtensionScalars)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Extension of scalars along a flat algebra preserves finite limits. -/
private theorem preservesFiniteLimits_extendScalars_of_flat (S T : Type u) [CommRing S]
    [CommRing T] [Algebra S T] [Module.Flat S T] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap S T)) :=
  extendScalars_preservesFiniteLimits_of_flat' _ (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- Let `K` be a dualizing complex over a Noetherian ring `A`, let `p` be a prime and let `R` be
any ring presenting the localization of `A` at `p`. A shift of the extension of `K` to `R` is a
normalized dualizing complex exactly when the shift is `δ_K(p)`. -/
theorem isNormalizedDualizingComplex_extendScalars_iff_eq_dualizingDimension
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K)
    (p : PrimeSpectrum A) (R : Type u) [CommRing R] [Algebra A R]
    [IsLocalization.AtPrime R p.asIdeal]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A R))]
    (n : ℤ) :
    letI : IsNoetherianRing R :=
      IsLocalization.isNoetherianRing p.asIdeal.primeCompl R inferInstance
    letI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R p.asIdeal
    IsNormalizedDualizingComplex.{u, u}
        (((ModuleCat.extendScalars.{u, u, u} (algebraMap A R)).mapDerivedCategory.obj K)⟦-n⟧) ↔
      n = dualizingDimension.{u, u} K p := by
  let : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl R inferInstance
  let : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R p.asIdeal
  set Ap := Localization.AtPrime p.asIdeal with hAp
  have : Module.Flat A Ap := IsLocalization.flat Ap p.asIdeal.primeCompl
  have := preservesFiniteLimits_extendScalars_of_flat A Ap
  let e : Ap ≃ₐ[A] R := IsLocalization.algEquiv p.asIdeal.primeCompl Ap R
  let : Algebra Ap R := (e : Ap →+* R).toAlgebra
  have hmapeq : algebraMap Ap R = (e : Ap →+* R) := rfl
  let : IsLocalization (Submonoid.powers (1 : Ap)) R :=
    IsLocalization.away_of_isUnit_of_bijective R isUnit_one e.bijective
  let : Module.Flat Ap R := IsLocalization.flat R (Submonoid.powers (1 : Ap))
  have := preservesFiniteLimits_extendScalars_of_flat Ap R
  let : IsLocalHom (algebraMap Ap R) :=
    IsLocalHom.of_surjective _ (hmapeq ▸ e.surjective)
  have hmax : (IsLocalRing.maximalIdeal Ap).map (algebraMap Ap R) =
      IsLocalRing.maximalIdeal R := by
    rw [hmapeq]
    exact IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  have hcomp : (algebraMap Ap R).comp (algebraMap A Ap) = algebraMap A R :=
    RingHom.ext fun x => e.commutes x
  set m := dualizingDimension.{u, u} K p with hm
  have key : IsNormalizedDualizingComplex.{u, u}
      (((ModuleCat.extendScalars.{u, u, u} (algebraMap A R)).mapDerivedCategory.obj K)⟦-m⟧) := by
    have hAp' : IsNormalizedDualizingComplex.{u, u}
        (((ModuleCat.extendScalars.{u, u, u}
          (algebraMap A Ap)).mapDerivedCategory.obj K)⟦-m⟧) :=
      (isNormalizedDualizingComplex_congr.{u, u}
        ((shiftFunctor (DerivedCategory (ModuleCat.{u} Ap)) (-m)).mapIso
          ((derivedExtensionScalarsIsoExtendScalars (algebraMap A Ap)).app K))).mp
        (dualizingDimension_spec.{u, u} K hK p)
    have hflat := isNormalizedDualizingComplex_extendScalars_of_flat.{u, u, u} hmax _ hAp'
    refine (isNormalizedDualizingComplex_congr.{u, u} ?_).mp hflat
    exact ((ModuleCat.extendScalars.{u, u, u}
        (algebraMap Ap R)).mapDerivedCategory.commShiftIso (-m)).app _ ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (-m)).mapIso
        ((extendScalarsCompMapDerivedCategoryIso (algebraMap A Ap) (algebraMap Ap R)
          (algebraMap A R) hcomp).app K)
  exact isNormalizedDualizingComplex_shift_iff_eq.{u, u} _ m key n

/-- Let `K` be a dualizing complex over a Noetherian ring `A`, let `p` be a prime and let `R` be
any ring presenting the localization of `A` at `p`. A shift of
`StacksDraft.PseudoCoherence.derivedExtensionScalars` of `K` to `R` is a normalized dualizing
complex exactly when the shift is `δ_K(p)`. -/
theorem isNormalizedDualizingComplex_derivedExtensionScalars_iff_eq_dualizingDimension
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K)
    (p : PrimeSpectrum A) (R : Type u) [CommRing R] [Algebra A R]
    [IsLocalization.AtPrime R p.asIdeal] (n : ℤ) :
    letI : IsNoetherianRing R :=
      IsLocalization.isNoetherianRing p.asIdeal.primeCompl R inferInstance
    letI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R p.asIdeal
    IsNormalizedDualizingComplex.{u, u}
        (((derivedExtensionScalars.{u, u, u} (algebraMap A R)).obj K)⟦-n⟧) ↔
      n = dualizingDimension.{u, u} K p := by
  let : IsNoetherianRing R :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl R inferInstance
  let : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R p.asIdeal
  have : Module.Flat A R := IsLocalization.flat R p.asIdeal.primeCompl
  have := preservesFiniteLimits_extendScalars_of_flat A R
  rw [isNormalizedDualizingComplex_congr.{u, u}
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (-n)).mapIso
      ((derivedExtensionScalarsIsoExtendScalars (algebraMap A R)).app K))]
  exact isNormalizedDualizingComplex_extendScalars_iff_eq_dualizingDimension K hK p R n

/-- The extension of a dualizing complex to any presentation of the localization at `p`, shifted
by `-δ_K(p)`, is a normalized dualizing complex. -/
theorem isNormalizedDualizingComplex_extendScalars_dualizingDimension
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K)
    (p : PrimeSpectrum A) (R : Type u) [CommRing R] [Algebra A R]
    [IsLocalization.AtPrime R p.asIdeal]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A R))] :
    letI : IsNoetherianRing R :=
      IsLocalization.isNoetherianRing p.asIdeal.primeCompl R inferInstance
    letI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R p.asIdeal
    IsNormalizedDualizingComplex.{u, u}
      (((ModuleCat.extendScalars.{u, u, u} (algebraMap A R)).mapDerivedCategory.obj K)⟦
        -dualizingDimension.{u, u} K p⟧) :=
  (isNormalizedDualizingComplex_extendScalars_iff_eq_dualizingDimension K hK p R _).mpr rfl

end Dualizing

end
