module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteCaseStepCompletedStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUps
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Resolution of an excellent normal local ring of dimension two

Let `(A, 𝔪)` be an excellent normal local domain of dimension two. Then `Spec(A)` has a
resolution of singularities by normalized blowups, and in particular a resolution of
singularities.

This is the case of a local ring of [Stacks, Tag 0BGP], `(4) ⇒ (3) ⇒ (2)`, run directly: the
completion `A^` is a normal domain because `A` is excellent ([Stacks, Tag 0C23]); so `Spec(A^)`
has a resolution ([Stacks, Tag 0BGN]), hence one by normalized blowups ([Stacks, Tag 0BGM]),
and such a sequence of normalized blowups descends to `Spec(A)` ([Stacks, Tag 0BGA]).

## Main results

* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isExcellent_of_ringKrullDim_eq_two`
* `AlgebraicGeometry.exists_isResolution_of_isExcellent_of_ringKrullDim_eq_two`

## References

* [Stacks Project, Tag 0BGP](https://stacks.math.columbia.edu/tag/0BGP)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- An excellent normal local domain `A` of dimension two has a resolution of singularities by
normalized blowups: the completion `A^` is a complete normal local domain of dimension two, so
[Stacks, Tags 0BGN and 0BGM] give one for `Spec(A^)`, which descends to `Spec(A)` by
[Stacks, Tag 0BGA]. -/
@[sga "6 X 7.17.5" "special case"]
theorem hasResolutionByNormalizedBlowUps_of_isExcellent_of_ringKrullDim_eq_two
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] (hexc : IsExcellent A)
    (hdim : ringKrullDim A = 2) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) := by
  have : IsNoetherianRing A := hexc.1.1
  have hcompl : IsNormalDomain (AdicCompletion (maximalIdeal A) A) :=
    isNormalDomain_adicCompletion_of_isExcellent A hexc (IsNormalRing.of_isIntegrallyClosed A)
  have hdim' : ringKrullDim (AdicCompletion (maximalIdeal A) A) = 2 := by
    rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal, hdim]
  exact hasResolutionByNormalizedBlowUps_of_adicCompletion A
    (IsNormalRing.of_isIntegrallyClosed _) IsNagataRing.of_isPrecomplete_maximalIdeal
    (hasResolutionByNormalizedBlowUps_of_exists_isResolution _ hdim'
      (exists_isResolution_of_isAdicComplete _ hdim'))

/-- An excellent normal local domain `A` of dimension two has a resolution of singularities
`X ⟶ Spec(A)`. (`IsNoetherianRing A` is an instance argument only because `IsResolution` needs
`Spec(A)` Noetherian to be stated; it follows from excellence.) -/
@[sga "6 X 7.17.5" "special case"]
theorem exists_isResolution_of_isExcellent_of_ringKrullDim_eq_two
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hexc : IsExcellent A) (hdim : ringKrullDim A = 2) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f := by
  refine exists_resolution_of_hasResolutionByNormalizedBlowUps (Spec (.of A)) ?_
    (hasResolutionByNormalizedBlowUps_of_isExcellent_of_ringKrullDim_eq_two A hexc hdim)
  rw [← hdim]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A

end AlgebraicGeometry

end
