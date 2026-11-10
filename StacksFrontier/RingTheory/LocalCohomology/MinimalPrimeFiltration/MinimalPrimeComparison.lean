module

public import StacksFrontier.RingTheory.LocalCohomology.BoundedComparison
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ProZero

/-!
# Local cohomology at a prime minimal in its support

Let `A` be a Noetherian ring, let `T ⊆ Spec(A)` be stable under specialization and let `𝔭 ∈ T`
be minimal in `T`. The preimage of `T` in `Spec(A_𝔭)` is the closed point, so flat base change
along `A → A_𝔭` identifies the localization at `𝔭` of `Hⁱ_T(M)` with `Hⁱ_{𝔭A_𝔭}(M_𝔭)`.

## Main results

* `Stacks.LocalCohomology.nonempty_minimalPrime_localCohomology_iso` — that identification, for
  a module placed in degree zero.

## Implementation notes

`StacksFrontier/RingTheory/LocalCohomology/MinimalPrimeFiltration/ProZero.lean` proves the same
identification as a natural isomorphism of functors, but through the unbounded case of Tag 0EF5,
which carries a finiteness hypothesis on the Krull dimensions. Tag 0EF8 has no such hypothesis,
so the bounded-below case of Tag 0EF5 is used here instead: a module placed in degree zero is
bounded below, and the bounded-below and unbounded derived functors of sections with support
agree (Tag 0EF4). The price is that the bounded-below comparison of the two derived functors is
only known to exist, so this is an existence statement rather than a construction; that is all
the exact sequence of Tag 0EF8 needs of it.

## References

* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
* [Stacks Project, Tag 0EF5](https://stacks.math.columbia.edu/tag/0EF5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

private theorem zeroLocus_maximalIdeal_eq_singleton_closedPoint (B : Type*) [CommRing B]
    [IsLocalRing B] :
    PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal B : Set B) =
      {IsLocalRing.closedPoint B} := by
  ext q
  change IsLocalRing.maximalIdeal B ≤ q.asIdeal ↔ q = IsLocalRing.closedPoint B
  exact ⟨fun hq ↦ PrimeSpectrum.ext
      (le_antisymm (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') hq),
    fun hq ↦ hq ▸ le_rfl⟩

/-- **Local cohomology localizes at a prime minimal in its support.** Over a Noetherian ring,
for `𝔭 ∈ T` minimal in `T` the localization at `𝔭` of `Hⁱ_T(M)` is `Hⁱ_{𝔭A_𝔭}(M_𝔭)`. No
hypothesis on the Krull dimension of `A` is needed. -/
theorem nonempty_minimalPrime_localCohomology_iso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) (p : PrimeSpectrum A)
    (hp : p ∈ T \ PrimeSpectrum.nonminimalPrimes T) (M : ModuleCat.{max u v} A) (i : ℤ) :
    Nonempty ((localCohomologyWithSupportIn.{u, v} A T
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i).localizedModule
          p.asIdeal.primeCompl ≅
      (localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i).obj
        (M.localizedModule p.asIdeal.primeCompl)) := by
  classical
  let S := p.asIdeal.primeCompl
  let B := Localization S
  let f : A →+* B := algebraMap A B
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B S)
  let ext := ModuleCat.extendScalars.{u, u, max u v} f
  let eloc := extendScalars_iso_localizedModuleFunctor.{u, v} S
  have : PreservesFiniteLimits ext := preservesFiniteLimits_of_natIso eloc.symm
  have : PreservesFiniteColimits ext := preservesFiniteColimits_of_natIso eloc.symm
  let D := (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
    f).functor
  let eD : D ≅ ext.mapDerivedCategory :=
    derivedExtensionScalarsIsoMapDerivedCategory.{u, v, u} f
  let K := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M
  let Kp := (DerivedCategory.Plus.singleFunctor (ModuleCat.{max u v} A) 0).obj M
  let eK : DerivedCategory.Plus.ι.obj Kp ≅ K :=
    (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{max u v} A) 0).app M
  let F := derivedSectionsWithSupportIn.{u, v} A T
  let G := derivedSectionsWithSupportIn.{u, v} B ((PrimeSpectrum.comap f) ⁻¹' T)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i
  obtain ⟨eP⟩ := nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso.{u, v} A T
  -- Flat base change for a bounded-below object, transported to the unbounded model.
  let eBC : D.obj (F.obj K) ≅ G.obj (D.obj K) :=
    (D.mapIso (eP.app Kp ≪≫ F.mapIso eK)).symm ≪≫
      (derivedSectionsWithSupportInPlusBaseChangeIso.{u, v, u} f hf T hT).val.app Kp ≪≫
      G.mapIso (D.mapIso eK)
  -- Over the localization the support becomes the closed point.
  let m := IsLocalRing.maximalIdeal B
  have hm : m.FG := IsNoetherian.noetherian _
  have hU : (PrimeSpectrum.comap f) ⁻¹' T = PrimeSpectrum.zeroLocus (m : Set B) :=
    (localized_support_of_minimal_prime_eq_closedPoint T p hp).trans
      (zeroLocus_maximalIdeal_eq_singleton_closedPoint B).symm
  have : IsIso (compareSectionsWithSupportLocalCohomology.{u, v} B m hm) :=
    isIso_compareSectionsWithSupportLocalCohomology.{u, v} B m hm
  let eSupport : G ≅ Dualizing.localCohomologyFunctor.{u, max u v} B m hm ⋙
      (Dualizing.derivedPowerTorsionProperty B m hm).ι :=
    derivedSupportIsoOfEq.{u, v} B _ _ hU.subset hU.ge ≪≫
      asIso (compareSectionsWithSupportLocalCohomology.{u, v} B m hm)
  -- Base change of a module placed in degree zero is its localization, placed in degree zero.
  let eSingle : D.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj
        ((ModuleCat.localizedModuleFunctor.{max u v} S).obj M) :=
    eD.app K ≪≫ (ext.mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).mapIso (eloc.app M)
  exact ⟨(eloc.app ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
      (F.obj K))).symm ≪≫
    ((Dualizing.mapDerivedCategoryHomologyIso ext i).app (F.obj K)).symm ≪≫
    H.mapIso (eD.app (F.obj K)).symm ≪≫ H.mapIso eBC ≪≫
    H.mapIso (eSupport.app (D.obj K)) ≪≫
    H.mapIso ((Dualizing.localCohomologyFunctor.{u, max u v} B m hm ⋙
      (Dualizing.derivedPowerTorsionProperty B m hm).ι).mapIso eSingle)⟩

end Stacks.LocalCohomology

end
