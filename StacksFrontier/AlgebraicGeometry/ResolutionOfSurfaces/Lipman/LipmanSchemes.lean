module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDInseparableFinal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDSeparableGoUp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.LipmanSchemesAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.GorensteinResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LipmanGorensteinChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingDefinesRational

/-!
# Lipman's theorem for schemes

Two-dimensional Noetherian local normal domains with normal completion, and two-dimensional
integral Noetherian schemes whose normalization is finite and has finitely many singular points,
each with normal completed local ring, have resolutions of singularities by normalized blowups.

## Main results

* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_spec_of_isAdicComplete`: a
  two-dimensional Noetherian complete local normal domain has a resolution of singularities by
  normalized blowups ([Stacks, Tags 0BGN and 0BGM]).
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_spec_of_isNormalRing_adicCompletion`: the
  same for a two-dimensional Noetherian local normal domain whose completion is normal.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_finite_normalization`: the implication
  `(4) ⇒ (3)` of [Stacks, Tag 0BGP].

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0BGP](https://stacks.math.columbia.edu/tag/0BGP)
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- A two-dimensional Noetherian complete local normal domain has a resolution of singularities by
normalized blowups ([Stacks, Tags 0BGN and 0BGM]). -/
theorem hasResolutionByNormalizedBlowUps_spec_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    [IsAdicComplete (maximalIdeal A) A] (hdim : ringKrullDim A = 2) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) :=
  hasResolutionByNormalizedBlowUps_spec_of_isAdicComplete_of_inputs
    definesRationalSingularity_of_isRegularLocalRing_of_ringKrullDim_eq_two
    exists_normalizedPointBlowupChain_isGorensteinLocalRing_stalk
    exists_normalizedPointBlowupChain_isRegular_of_isGorensteinLocalRing
    isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable
    isReductionToRationalSingularitiesPossible_of_inseparable A hdim

/-- A two-dimensional Noetherian local normal domain whose completion is normal has a resolution of
singularities by normalized blowups. -/
theorem hasResolutionByNormalizedBlowUps_spec_of_isNormalRing_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hdim : ringKrullDim A = 2) (hnormal : IsNormalRing (AdicCompletion (maximalIdeal A) A)) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) :=
  hasResolutionByNormalizedBlowUps_spec_of_isNormalRing_adicCompletion_of_inputs
    definesRationalSingularity_of_isRegularLocalRing_of_ringKrullDim_eq_two
    exists_normalizedPointBlowupChain_isGorensteinLocalRing_stalk
    exists_normalizedPointBlowupChain_isRegular_of_isGorensteinLocalRing
    isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable
    isReductionToRationalSingularitiesPossible_of_inseparable A hdim hnormal

/-- A two-dimensional integral Noetherian scheme whose normalization is finite and has finitely
many singular points, at each of which the completion of the local ring is normal, has a
resolution of singularities by normalized blowups ([Stacks, Tag 0BGP], `(4) ⇒ (3)`). -/
theorem hasResolutionByNormalizedBlowUps_of_finite_normalization
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim Y = 2)
    (hfin : IsFinite (Scheme.normalization Y hY))
    (hsing : (singularLocus (Y.normalizationScheme hY)).Finite)
    (hnormal : ∀ y ∈ singularLocus (Y.normalizationScheme hY),
      IsNormalRing (AdicCompletion (maximalIdeal ((Y.normalizationScheme hY).presheaf.stalk y))
        ((Y.normalizationScheme hY).presheaf.stalk y))) :
    HasResolutionByNormalizedBlowUps Y :=
  hasResolutionByNormalizedBlowUps_of_finite_normalization_of_inputs
    definesRationalSingularity_of_isRegularLocalRing_of_ringKrullDim_eq_two
    exists_normalizedPointBlowupChain_isGorensteinLocalRing_stalk
    exists_normalizedPointBlowupChain_isRegular_of_isGorensteinLocalRing
    isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable
    isReductionToRationalSingularitiesPossible_of_inseparable Y hY hdim hfin hsing hnormal

end AlgebraicGeometry

end
