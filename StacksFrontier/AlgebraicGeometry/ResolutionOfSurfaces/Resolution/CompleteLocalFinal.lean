module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalSteps
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUpsAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableReduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpTransfer
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.RationalDoublePointResolutionTag
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.RationalSingularPointsResolution

/-!
# [Stacks, Tag 0BGN] from Tag 0B4Q and the rational pass

The assembly `AlgebraicGeometry.exists_isResolution_of_isAdicComplete_of_inputs` of
[Stacks, Tag 0BGN] takes five inputs. This file supplies three of them from the theorems of this
library — the complete case of [Stacks, Tag 0BGM]
(`hasResolutionByNormalizedBlowUps_of_isResolution_of_rational`), [Stacks, Tag 0AXL]
(`SeparableGoUp.isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable`) and
[Stacks, Tag 0B4U]
(`SeparableGoUp.isReductionToRationalSingularitiesPossible_of_isPurelyInseparable_of_frobenius`) —
leaving the statement of [Stacks, Tag 0B4Q] and the pass through [Stacks, Tags 0BBV, 0BFY and 0BGE]
as the remaining premises.

With [Stacks, Tag 0B4Q] proved (`definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing`)
and the rational pass reduced to [Stacks, Tags 0BBV and 0BGE]
(`hasResolutionByNormalizedBlowUps_stalk_of_definesRationalSingularity`), both [Stacks, Tag 0BGM]
and [Stacks, Tag 0BGN] are stated here over exactly those two inputs.

## Main results

* `AlgebraicGeometry.exists_isResolution_of_isAdicComplete_of_rational`.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_exists_isResolution_of_rationalPass`:
  [Stacks, Tag 0BGM] over Tags 0BBV and 0BGE.
* `AlgebraicGeometry.exists_isResolution_of_isAdicComplete_of_rationalPass`:
  [Stacks, Tag 0BGN] over Tags 0BBV and 0BGE.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_exists_isResolution_of_gorensteinChain`
  and `AlgebraicGeometry.exists_isResolution_of_isAdicComplete_of_gorensteinChain`:
  [Stacks, Tags 0BGM and 0BGN] with [Stacks, Tag 0BGE]
  (`AlgebraicGeometry.exists_singularPointBlowupChain_isNormal_isRegular`) plugged in, over the
  Gorenstein sequence of blowups of [Stacks, Tag 0BBV] alone.

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 0BGN] over Tag 0B4Q and the rational pass.** The spectrum of a Noetherian
complete local normal domain of dimension two has a resolution of singularities, granted `h0B4Q`
([Stacks, Tag 0B4Q]) and `hrational` (the resolution of rational singular points by normalized
blowups, [Stacks, Tags 0BBV, 0BFY and 0BGE]). -/
theorem exists_isResolution_of_isAdicComplete_of_rational
    (h0B4Q : ∀ (B : Type u) [CommRing B] [IsDomain B] [IsRegularLocalRing B] [IsNagataRing B],
      ringKrullDim B = 2 → DefinesRationalSingularity B)
    (hrational : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
      [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B], ringKrullDim B = 2 →
      ∀ (Z : Scheme.{u}) [IsNormal Z] (g : Z ⟶ Spec (.of B)), IsModification g →
        ∀ z ∈ singularLocus Z, DefinesRationalSingularity (Z.presheaf.stalk z) →
          HasResolutionByNormalizedBlowUps (Spec (Z.presheaf.stalk z)))
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f := by
  refine exists_isResolution_of_isAdicComplete_of_inputs
    (fun C _ _ _ _ _ hdimC hres =>
      hasResolutionByNormalizedBlowUps_of_isResolution_of_rational C hdimC hres h0B4Q hrational)
    (fun R _ _ _ hR _ =>
      have : IsNagataRing R := IsNagataRing.of_isPrecomplete_maximalIdeal
      h0B4Q R hR)
    (fun A B _ _ _ _ _ _ _ _ _ _ _ _ hA hB hs hr =>
      SeparableGoUp.isReductionToRationalSingularitiesPossible_of_finite_of_isSeparable A B hA hB hs
        hr)
    (fun R B _ _ _ _ p hp hc hR _ _ _ _ _ _ _ _ h => ?_) hrational A hdim
  have : IsNagataRing R := IsNagataRing.of_isPrecomplete_maximalIdeal
  have hdimB : ringKrullDim B = 2 := by
    rw [← hR]
    exact (Algebra.IsIntegral.ringKrullDim_eq R B).symm
  exact SeparableGoUp.isReductionToRationalSingularitiesPossible_of_isPurelyInseparable_of_frobenius
    R B p hp hc hR h (h0B4Q R hR) (SeparableGoUp.isDominatedByFiniteOverBase R B hdimB.le)

/-- **[Stacks, Tag 0BGM] over Tags 0BBV and 0BGE.** A two-dimensional Noetherian local normal
domain whose spectrum has a resolution of singularities has a resolution by normalized blowups,
granted [Stacks, Tag 0BBV] (as `h0BBV`) and [Stacks, Tag 0BGE] (as `h0BGE`), in the forms of
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_stalk_of_definesRationalSingularity`. -/
theorem hasResolutionByNormalizedBlowUps_of_exists_isResolution_of_rationalPass
    (h0BBV : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsGorenstein Y)
    (h0BGE : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalDomain (AdicCompletion (maximalIdeal A) A) → Dualizing.IsGorensteinLocalRing A →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsRegular Y)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hdim : ringKrullDim A = 2)
    (hres : ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) :=
  hasResolutionByNormalizedBlowUps_of_isResolution_of_rational A hdim hres
    (fun B _ _ _ _ hB ↦ definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing B hB)
    (fun B _ _ _ _ _ hdimB Z _ g hg z hz hrat ↦
      hasResolutionByNormalizedBlowUps_stalk_of_definesRationalSingularity h0BBV h0BGE B hdimB Z
        g hg z hz hrat)

/-- **[Stacks, Tag 0BGN] over Tags 0BBV and 0BGE.** The spectrum of a Noetherian complete local
normal domain of dimension two has a resolution of singularities, granted [Stacks, Tag 0BBV]
(as `h0BBV`) and [Stacks, Tag 0BGE] (as `h0BGE`). -/
theorem exists_isResolution_of_isAdicComplete_of_rationalPass
    (h0BBV : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsGorenstein Y)
    (h0BGE : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalDomain (AdicCompletion (maximalIdeal A) A) → Dualizing.IsGorensteinLocalRing A →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsRegular Y)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f :=
  exists_isResolution_of_isAdicComplete_of_rational
    (fun B _ _ _ _ hB ↦ definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing B hB)
    (fun B _ _ _ _ _ hdimB Z _ g hg z hz hrat ↦
      hasResolutionByNormalizedBlowUps_stalk_of_definesRationalSingularity h0BBV h0BGE B hdimB Z
        g hg z hz hrat) A hdim

/-- **[Stacks, Tag 0BGM] over Tag 0BBV.** A two-dimensional Noetherian local normal domain whose
spectrum has a resolution of singularities has a resolution by normalized blowups, granted
[Stacks, Tag 0BBV] in the form `h0BBV`: a sequence of blowups in singular closed points, with
normal stages, ending in a Gorenstein scheme. [Stacks, Tag 0BGE] is supplied by
`AlgebraicGeometry.exists_singularPointBlowupChain_isNormal_isRegular`. -/
theorem hasResolutionByNormalizedBlowUps_of_exists_isResolution_of_gorensteinChain
    (h0BBV : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsGorenstein Y)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hdim : ringKrullDim A = 2)
    (hres : ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) :=
  hasResolutionByNormalizedBlowUps_of_exists_isResolution_of_rationalPass h0BBV
    exists_singularPointBlowupChain_isNormal_isRegular A hdim hres

/-- **[Stacks, Tag 0BGN] over Tag 0BBV.** The spectrum of a Noetherian complete local normal
domain of dimension two has a resolution of singularities, granted [Stacks, Tag 0BBV] in the form
`h0BBV` of `hasResolutionByNormalizedBlowUps_of_exists_isResolution_of_gorensteinChain`.
[Stacks, Tag 0BGE] is supplied by
`AlgebraicGeometry.exists_singularPointBlowupChain_isNormal_isRegular`. -/
theorem exists_isResolution_of_isAdicComplete_of_gorensteinChain
    (h0BBV : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → DefinesRationalSingularity A →
      (∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsGorenstein Y)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f :=
  exists_isResolution_of_isAdicComplete_of_rationalPass h0BBV
    exists_singularPointBlowupChain_isNormal_isRegular A hdim

end AlgebraicGeometry
