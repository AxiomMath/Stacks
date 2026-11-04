module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimitLocal
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapPerPrime
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit
public import StacksFrontier.RingTheory.Dualizing.DerivedLocalization
public import StacksFrontier.RingTheory.LocalCohomology.TorsionFlatDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local cohomology at a prime, computed on the completed local ring

Let `A` be a Noetherian ring and `𝔮` a prime of `A`. Put `B = A_𝔮` and let `S` be the completion
of the local ring `B` at its maximal ideal. Then, naturally in the `A`-module `N`,

`H^e_{𝔮B}(N_𝔮) ≅ H^e_{𝔪_S}(S ⊗_A N)` as `B`-modules,

where both sides are local cohomology at the maximal ideal in the coreflection model
`Stacks.LocalCohomology.localCohomologyModuleFunctor`. This is the "H-side" of local duality at a
prime, in the proof of Stacks 0EFX: the left side is the spelling consumed by
`Stacks.LocalCohomology.exists_map_idealPowerTower_eq_zero_of_local` (Stacks 0EF9), and the right
side is where local duality over the complete local ring `S` applies.

The isomorphism is the composite of
* localization as extension of scalars (`Dualizing.extendScalarsIsoLocalizedModuleFunctor`),
* the comparison of the two models of local cohomology, over `B` and over `S` (Stacks 0955,
  `Stacks.LocalCohomology.localCohomologyWithSupportInMaximalIdealIso`),
* flat descent of local cohomology with support in the closed point along `B → S`
  (`Stacks.LocalCohomology.localCohomologyModuleTorsionDescentIso`): `B → S` is flat and an
  isomorphism modulo the maximal ideal, and the preimage of the closed point of `B` is the
  closed point of `S`,
* and composition of extensions of scalars.

## Main definitions

* `Stacks.LocalCohomology.localizationCompletionDescentIso`: the natural isomorphism above.

## Main results

* `Stacks.LocalCohomology.preimage_zeroLocus_maximalIdeal_adicCompletion`: the preimage of the
  closed point of a Noetherian local ring in the spectrum of its completion is the closed point.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0EFR](https://stacks.math.columbia.edu/tag/0EFR)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace Stacks.LocalCohomology

section Completion

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The completion of a Noetherian local ring at its maximal ideal is local. -/
instance isLocalRing_adicCompletion_maximalIdeal :
    IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
  Stacks.AdicCompletionDimension.isLocalRing_adicCompletion_of_le_maximalIdeal (maximalIdeal R)
    le_rfl

/-- The maximal ideal of the completion of a Noetherian local ring is the extension of the
maximal ideal. -/
@[sga "7 VIII 7.3.5.3" "Completion clause"]
theorem maximalIdeal_adicCompletion :
    maximalIdeal (AdicCompletion (maximalIdeal R) R) =
      (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le (maximalIdeal R)
    (maximalIdeal R) le_rfl (Ideal.fg_of_isNoetherianRing _))).symm

/-- **The preimage of the closed point in the spectrum of the completion is the closed point.** -/
theorem preimage_zeroLocus_maximalIdeal_adicCompletion :
    PrimeSpectrum.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) ⁻¹'
        PrimeSpectrum.zeroLocus (maximalIdeal R : Set R) =
      PrimeSpectrum.zeroLocus
        (maximalIdeal (AdicCompletion (maximalIdeal R) R) :
          Set (AdicCompletion (maximalIdeal R) R)) := by
  rw [PrimeSpectrum.preimage_comap_zeroLocus, maximalIdeal_adicCompletion, Ideal.map,
    PrimeSpectrum.zeroLocus_span]

/-- **Local cohomology at the maximal ideal descends from the completion.** For a Noetherian
local ring `R` with completion `S`, `H^e_𝔪(N) ≅ H^e_{𝔪_S}(S ⊗_R N)` as `R`-modules, naturally in
`N`. -/
def localCohomologyModuleCompletionIso (e : ℤ) :
    localCohomologyModuleFunctor.{u, u} R e ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap R (AdicCompletion (maximalIdeal R) R)) ⋙
        localCohomologyModuleFunctor.{u, u} (AdicCompletion (maximalIdeal R) R) e ⋙
          ModuleCat.restrictScalars.{u} (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
  (localCohomologyWithSupportInMaximalIdealIso R e).symm ≪≫
    localCohomologyModuleTorsionDescentIso (AdicCompletion.flat_of_isNoetherian (maximalIdeal R))
      (PrimeSpectrum.zeroLocus (maximalIdeal R : Set R))
      (PrimeSpectrum.isClosed_zeroLocus _).stableUnderSpecialization (maximalIdeal R) le_rfl
      (Stacks.Algebraization.bijective_quotientMap_adicCompletion (maximalIdeal R)) e ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (eqToIso (by rw [preimage_zeroLocus_maximalIdeal_adicCompletion]) ≪≫
        localCohomologyWithSupportInMaximalIdealIso (AdicCompletion (maximalIdeal R) R) e) _)

end Completion

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (q : PrimeSpectrum A)

/-- **Local cohomology at a prime, computed on the completed local ring** (the module-side
descent in the proof of Stacks 0EFX). Let `B = A_𝔮` and `S` the completion of `B` at its maximal
ideal. Then `H^e_{𝔮B}(N_𝔮) ≅ H^e_{𝔪_S}(S ⊗_A N)` as `B`-modules, naturally in the `A`-module
`N`. -/
def localizationCompletionDescentIso (e : ℤ) :
    ModuleCat.localizedModuleFunctor.{u} q.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization.AtPrime q.asIdeal) e ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap A
          (AdicCompletion (maximalIdeal (Localization.AtPrime q.asIdeal))
            (Localization.AtPrime q.asIdeal))) ⋙
        localCohomologyModuleFunctor (AdicCompletion (maximalIdeal (Localization.AtPrime q.asIdeal))
          (Localization.AtPrime q.asIdeal)) e ⋙
          ModuleCat.restrictScalars.{u} (algebraMap (Localization.AtPrime q.asIdeal)
            (AdicCompletion (maximalIdeal (Localization.AtPrime q.asIdeal))
              (Localization.AtPrime q.asIdeal))) :=
  let B := Localization.AtPrime q.asIdeal
  let S := AdicCompletion (maximalIdeal B) B
  have hcomp : algebraMap A S = (algebraMap B S).comp (algebraMap A B) :=
    IsScalarTower.algebraMap_eq A B S
  Functor.isoWhiskerRight
      (Dualizing.extendScalarsIsoLocalizedModuleFunctor.{u, u} q.asIdeal.primeCompl).symm _ ≪≫
    Functor.isoWhiskerLeft _ (localCohomologyModuleCompletionIso B e) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((ModuleCat.extendScalarsComp (algebraMap A B) (algebraMap B S)).symm ≪≫
        eqToIso (by rw [hcomp])) _
end Stacks.LocalCohomology

end
