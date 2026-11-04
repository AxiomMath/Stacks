module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.CompleteLocalBaseCase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.CompleteLocalInductiveStep
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LocalBirationalExtensionsRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedPointBlowupRationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Lipman

/-!
# Lipman's theorem for schemes, assembled from its inputs

This file assembles [Stacks, Tags 0BGN and 0BGM] and the implication `(4) ⇒ (3)` of
[Stacks, Tag 0BGP] from the results they rest on, which are taken as arguments in the forms in
which they are stated elsewhere:

* `hregular`: [Stacks, Tag 0B4Q] ([Stacks, Tag 0BG0] is
  `AlgebraicGeometry.definesRationalSingularity_of_essFiniteType`);
* `hgorenstein`, `hdoublePoint`: [Stacks, Tags 0BBV and 0BGE];
* `hseparable`, `hinseparable`: [Stacks, Tags 0AXL and 0B4U].

[Stacks, Tag 0B4P] is
`AlgebraicGeometry.exists_normalizedPointBlowupChain_definesRationalSingularity_stalk`.

The inductive step of the proof of [Stacks, Tag 0BGN] is
`AlgebraicGeometry.exists_isResolution_of_intermediate_step`.

## Main results

* `hasResolutionByNormalizedBlowUps_spec_of_isAdicComplete_of_inputs`: a two-dimensional
  Noetherian complete local normal domain has a resolution by normalized blowups ([Stacks, Tags
  0BGN and 0BGM]).
* `hasResolutionByNormalizedBlowUps_spec_of_isNormalRing_adicCompletion_of_inputs`: the same for a
  two-dimensional Noetherian local normal domain with normal completion.
* `hasResolutionByNormalizedBlowUps_of_finite_normalization_of_inputs`: the implication
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

/-- The completion of a Noetherian local ring with normal completion is a normal domain and
adically complete. -/
private theorem isNormalDomain_and_isAdicComplete_adicCompletion (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (h : IsNormalRing (AdicCompletion (maximalIdeal A) A)) :
    IsNormalDomain (AdicCompletion (maximalIdeal A) A) ∧
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal A) A))
        (AdicCompletion (maximalIdeal A) A) := by
  obtain ⟨hdom, hic⟩ := h.of_isLocalRing
  exact ⟨⟨hdom, hic⟩,
    AdicCompletion.isAdicComplete_of_fg (IsNoetherian.noetherian (maximalIdeal A))⟩

/-- **[Stacks, Tags 0BGN and 0BGM].** A two-dimensional Noetherian complete local normal domain
has a resolution of singularities by normalized blowups. The induction on the degree over a
regular subring given by Cohen's structure theorem produces a resolution
(`Stacks.ResolutionOfSurfaces.exists_isResolution_of_steps`), and Tag 0BGM turns it into a
resolution by normalized blowups. -/
theorem hasResolutionByNormalizedBlowUps_spec_of_isAdicComplete_of_inputs
    (hregular : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsNagataRing A],
      ringKrullDim A = 2 → (letI := IsRegularLocalRing.isDomain A; DefinesRationalSingularity A))
    (hgorenstein : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      (letI := hN.1; ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧
        ∀ y : Y, ∃ _ : IsNoetherianRing (Y.presheaf.stalk y),
          Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk y))
    (hdoublePoint : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalRing (AdicCompletion (maximalIdeal A) A) →
      (letI := hN.1; Dualizing.IsGorensteinLocalRing A) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧ IsRegular Y)
    (hseparable : ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      [CommRing B] [IsLocalRing B] [IsNormalDomain B] [Algebra A B] [Module.Finite A B]
      [FaithfulSMul A B] [IsLocalHom (algebraMap A B)], IsNagataRing A → IsNagataRing B →
      ringKrullDim A = 2 → ringKrullDim B = 2 →
      (letI := FractionRing.liftAlgebra A (FractionRing B);
        Algebra.IsSeparable (FractionRing A) (FractionRing B)) →
      IsReductionToRationalSingularitiesPossible A → IsReductionToRationalSingularitiesPossible B)
    (hinseparable : ∀ (p : ℕ) [Fact p.Prime] (R A : Type u) [CommRing R] [IsRegularLocalRing R]
      [IsAdicComplete (maximalIdeal R) R] [CharP R p] [CommRing A] [IsNoetherianRing A]
      [IsLocalRing A] [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] [Algebra R A]
      [Module.Finite R A] [FaithfulSMul R A], ringKrullDim R = 2 →
      (letI := IsRegularLocalRing.isDomain R; letI := FractionRing.liftAlgebra R (FractionRing A);
       Module.finrank (FractionRing R) (FractionRing A) = p ∧
        ¬ Algebra.IsSeparable (FractionRing R) (FractionRing A)) →
      IsReductionToRationalSingularitiesPossible A)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    [IsAdicComplete (maximalIdeal A) A] (hdim : ringKrullDim A = 2) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) := by
  have hBGM : ∀ (C : Type u) [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
      [IsNormalDomain C], ringKrullDim C = 2 →
      (∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of C)), IsResolution f) →
      HasResolutionByNormalizedBlowUps (Spec (.of C)) := fun C _ _ _ _ hC hres =>
    hasResolutionByNormalizedBlowUps_of_isResolution_of_lipmanInputs hregular hgorenstein
      hdoublePoint definesRationalSingularity_of_essFiniteType C hC hres
  refine hBGM A hdim (Stacks.ResolutionOfSurfaces.exists_isResolution_of_steps ?_ ?_ A hdim)
  · intro B A' _ _ _ _ _ _ _ _ _ _ _ _ _ hA' hB hsmaller
    refine exists_isResolution_of_intermediate_step B A' hA' hB
      fun R C _ _ _ _ _ _ _ _ _ _ _ hR hle => ?_
    have : IsDomain R := IsRegularLocalRing.isDomain R
    exact hBGM C ((Algebra.IsIntegral.ringKrullDim_eq R C).symm.trans hR) (hsmaller R C hR hle)
  · intro R A' _ _ _ _ _ _ _ _ _ _ _ _ hR hmin
    exact exists_isResolution_of_forall_eq_bot_or_eq_top hregular hgorenstein hdoublePoint
      definesRationalSingularity_of_essFiniteType hseparable hinseparable
      exists_normalizedPointBlowupChain_definesRationalSingularity_stalk R A' hR hmin

/-- **A two-dimensional Noetherian local normal domain with normal completion has a resolution
of singularities by normalized blowups.** The completion is a two-dimensional Noetherian complete
local normal domain, and a resolution by normalized blowups of its spectrum descends
([Stacks, Tags 0BGA and 0BG6]). -/
theorem hasResolutionByNormalizedBlowUps_spec_of_isNormalRing_adicCompletion_of_inputs
    (hregular : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsNagataRing A],
      ringKrullDim A = 2 → (letI := IsRegularLocalRing.isDomain A; DefinesRationalSingularity A))
    (hgorenstein : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      (letI := hN.1; ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧
        ∀ y : Y, ∃ _ : IsNoetherianRing (Y.presheaf.stalk y),
          Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk y))
    (hdoublePoint : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalRing (AdicCompletion (maximalIdeal A) A) →
      (letI := hN.1; Dualizing.IsGorensteinLocalRing A) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧ IsRegular Y)
    (hseparable : ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      [CommRing B] [IsLocalRing B] [IsNormalDomain B] [Algebra A B] [Module.Finite A B]
      [FaithfulSMul A B] [IsLocalHom (algebraMap A B)], IsNagataRing A → IsNagataRing B →
      ringKrullDim A = 2 → ringKrullDim B = 2 →
      (letI := FractionRing.liftAlgebra A (FractionRing B);
        Algebra.IsSeparable (FractionRing A) (FractionRing B)) →
      IsReductionToRationalSingularitiesPossible A → IsReductionToRationalSingularitiesPossible B)
    (hinseparable : ∀ (p : ℕ) [Fact p.Prime] (R A : Type u) [CommRing R] [IsRegularLocalRing R]
      [IsAdicComplete (maximalIdeal R) R] [CharP R p] [CommRing A] [IsNoetherianRing A]
      [IsLocalRing A] [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] [Algebra R A]
      [Module.Finite R A] [FaithfulSMul R A], ringKrullDim R = 2 →
      (letI := IsRegularLocalRing.isDomain R; letI := FractionRing.liftAlgebra R (FractionRing A);
       Module.finrank (FractionRing R) (FractionRing A) = p ∧
        ¬ Algebra.IsSeparable (FractionRing R) (FractionRing A)) →
      IsReductionToRationalSingularitiesPossible A)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hdim : ringKrullDim A = 2) (hnormal : IsNormalRing (AdicCompletion (maximalIdeal A) A)) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) := by
  obtain ⟨_, _⟩ := isNormalDomain_and_isAdicComplete_adicCompletion A hnormal
  have hdimB : ringKrullDim (AdicCompletion (maximalIdeal A) A) = 2 := by
    rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal, hdim]
  exact hasResolutionByNormalizedBlowUps_of_adicCompletion A hnormal
    IsNagataRing.of_isPrecomplete_maximalIdeal
    (hasResolutionByNormalizedBlowUps_spec_of_isAdicComplete_of_inputs hregular hgorenstein
      hdoublePoint hseparable hinseparable _ hdimB)

/-- **[Stacks, Tag 0BGP], `(4) ⇒ (3)`.** A two-dimensional integral Noetherian scheme whose
normalization is finite, with finitely many singular points at each of which the completion of
the local ring is normal, has a resolution of singularities by normalized blowups. -/
theorem hasResolutionByNormalizedBlowUps_of_finite_normalization_of_inputs
    (hregular : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsNagataRing A],
      ringKrullDim A = 2 → (letI := IsRegularLocalRing.isDomain A; DefinesRationalSingularity A))
    (hgorenstein : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      (letI := hN.1; ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧
        ∀ y : Y, ∃ _ : IsNoetherianRing (Y.presheaf.stalk y),
          Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk y))
    (hdoublePoint : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalRing (AdicCompletion (maximalIdeal A) A) →
      (letI := hN.1; Dualizing.IsGorensteinLocalRing A) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧ IsRegular Y)
    (hseparable : ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      [CommRing B] [IsLocalRing B] [IsNormalDomain B] [Algebra A B] [Module.Finite A B]
      [FaithfulSMul A B] [IsLocalHom (algebraMap A B)], IsNagataRing A → IsNagataRing B →
      ringKrullDim A = 2 → ringKrullDim B = 2 →
      (letI := FractionRing.liftAlgebra A (FractionRing B);
        Algebra.IsSeparable (FractionRing A) (FractionRing B)) →
      IsReductionToRationalSingularitiesPossible A → IsReductionToRationalSingularitiesPossible B)
    (hinseparable : ∀ (p : ℕ) [Fact p.Prime] (R A : Type u) [CommRing R] [IsRegularLocalRing R]
      [IsAdicComplete (maximalIdeal R) R] [CharP R p] [CommRing A] [IsNoetherianRing A]
      [IsLocalRing A] [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] [Algebra R A]
      [Module.Finite R A] [FaithfulSMul R A], ringKrullDim R = 2 →
      (letI := IsRegularLocalRing.isDomain R; letI := FractionRing.liftAlgebra R (FractionRing A);
       Module.finrank (FractionRing R) (FractionRing A) = p ∧
        ¬ Algebra.IsSeparable (FractionRing R) (FractionRing A)) →
      IsReductionToRationalSingularitiesPossible A)
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (hdim : topologicalKrullDim Y = 2)
    (hfin : IsFinite (Scheme.normalization Y hY))
    (hsing : (singularLocus (Y.normalizationScheme hY)).Finite)
    (hnormal : ∀ y ∈ singularLocus (Y.normalizationScheme hY),
      IsNormalRing (AdicCompletion (maximalIdeal ((Y.normalizationScheme hY).presheaf.stalk y))
        ((Y.normalizationScheme hY).presheaf.stalk y))) :
    HasResolutionByNormalizedBlowUps Y := by
  let N := Y.normalizationScheme hY
  have : IsFinite (Scheme.normalization Y hY) := hfin
  have : IsNormal N := Scheme.isNormal_normalizationScheme Y hY
  have : IsLocallyNoetherian N :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.normalization Y hY)
  have hdimN : topologicalKrullDim N ≤ 2 :=
    (topologicalKrullDim_le_of_isIntegralHom (Scheme.normalization Y hY)).trans_eq hdim
  refine hasResolutionByNormalizedBlowUps_of_adicCompletion_stalks Y hY hdim hfin hsing
    hnormal fun y hy => ?_
  let O := N.presheaf.stalk y
  have : IsNormalDomain O := ⟨IsNormal.stalk_isDomain y, IsNormal.stalk_normal y⟩
  obtain ⟨_, _⟩ := isNormalDomain_and_isAdicComplete_adicCompletion O (hnormal y hy)
  exact hasResolutionByNormalizedBlowUps_spec_of_isAdicComplete_of_inputs hregular hgorenstein
    hdoublePoint hseparable hinseparable _
    (ringKrullDim_adicCompletion_stalk_eq_two_of_mem_singularLocus N hdimN y hy)

end AlgebraicGeometry

end
