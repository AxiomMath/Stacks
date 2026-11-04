module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteCaseStep
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalInduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUps
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularLocusFinite
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRing
public import StacksFrontier.FieldTheory.Separable.NoIntermediateField
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularityNoProjective

/-!
# The two steps of the induction for complete local domains

This file proves the inductive step of the source's proof of [Stacks, Tag 0BGN] from the
geometric construction of its second paragraph and from the complete case of
[Stacks, Tag 0BGM].

## Main results

* `AlgebraicGeometry.exists_isResolution_of_completeCaseStep`: the inductive step.
* `AlgebraicGeometry.exists_isResolution_of_isReductionToRationalSingularitiesPossible`: the end
  of the base case, after reduction to rational singularities has been shown possible.
* `AlgebraicGeometry.isReductionToRationalSingularitiesPossible_of_forall_eq_bot_or_eq_top`: the
  beginning of the base case: over a regular complete local ring with no intermediate field,
  reduction to rational singularities is possible, by the separable going-up or the degree-`p`
  inseparable case.

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The inductive step of the source's proof of [Stacks, Tag 0BGN].** Suppose `geo` provides,
for a resolution `Y ⟶ Spec B` and `B ⊆ A` finite, a normal modification `X ⟶ Spec A` with
finitely many singular points, at each of which the completed local ring is a complete local
normal domain of dimension two finite over a regular complete local ring of dimension two, of
degree at most `[A : B]`; and suppose `complete` is the complete case of [Stacks, Tag 0BGM].
Then, given resolutions of the spectra of all such rings of degree at most `[A : B]`, `Spec A` has
a resolution: each completed local ring has one, hence a resolution by normalized blowups by
`complete`, which descends to the local ring along the completion
(`hasResolutionByNormalizedBlowUps_of_adicCompletion`), and the local resolutions assemble
(`exists_isResolution_of_isModification_of_singularLocus`). -/
theorem exists_isResolution_of_completeCaseStep
    (geo : ∀ (B A : Type u) [CommRing B] [CommRing A] [IsNoetherianRing B] [IsLocalRing B]
      [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B] [IsNoetherianRing A] [IsLocalRing A]
      [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A], ringKrullDim A = 2 →
      ∀ [Algebra B A] [Module.Finite B A] [FaithfulSMul B A] {Y : Scheme.{u}}
        (g : Y ⟶ Spec (.of B)), IsResolution g →
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsNormal X ∧ IsModification f ∧
        (singularLocus X).Finite ∧
        ∀ x ∈ singularLocus X,
          IsNormalDomain (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)) ∧
          ringKrullDim (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)) = 2 ∧
          ∃ (R : Type u) (_ : CommRing R) (_ : IsRegularLocalRing R)
            (_ : IsAdicComplete (maximalIdeal R) R)
            (_ : Algebra R (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x))),
            Module.Finite R (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x)) ∧
            FaithfulSMul R (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x)) ∧
            ringKrullDim R = 2 ∧
            Module.finrank R (AdicCompletion (maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x)) ≤ Module.finrank B A)
    (complete : ∀ (C : Type u) [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
      [IsNormalDomain C] [IsAdicComplete (maximalIdeal C) C], ringKrullDim C = 2 →
      (∃ (Z : Scheme.{u}) (h : Z ⟶ Spec (.of C)), IsResolution h) →
      HasResolutionByNormalizedBlowUps (Spec (.of C)))
    (B A : Type u) [CommRing B] [CommRing A] [IsNoetherianRing B] [IsLocalRing B]
    [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B] [IsNoetherianRing A] [IsLocalRing A]
    [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] [Algebra B A] [Module.Finite B A]
    [FaithfulSMul B A] (hdimA : ringKrullDim A = 2)
    (hB : ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of B)), IsResolution g)
    (ih : ∀ (R C : Type u) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
        [CommRing C] [IsNoetherianRing C] [IsLocalRing C] [IsNormalDomain C]
        [IsAdicComplete (maximalIdeal C) C] [Algebra R C] [Module.Finite R C] [FaithfulSMul R C],
        ringKrullDim R = 2 → Module.finrank R C ≤ Module.finrank B A →
        ∃ (Z : Scheme.{u}) (h : Z ⟶ Spec (.of C)), IsResolution h) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f := by
  obtain ⟨Y, g, hg⟩ := hB
  obtain ⟨X, f, hXn, hf, hsing, hpt⟩ := geo B A hdimA g hg
  have := hXn
  refine exists_isResolution_of_isModification_of_singularLocus A f hf hdimA hsing fun x hx => ?_
  obtain ⟨hnC, hdimC, R, _, _, _, _, hfin, hfaith, hdimR, hle⟩ := hpt x hx
  have : IsProper f := hf.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNormalDomain (X.presheaf.stalk x) := by
    have := hf.source_isIntegral
    exact ⟨hXn.stalk_isDomain x, IsNormal.stalk_normal x⟩
  have hresC := ih R _ hdimR hle
  exact hasResolutionByNormalizedBlowUps_of_adicCompletion (X.presheaf.stalk x)
    (IsNormalRing.of_isIntegrallyClosed _) IsNagataRing.of_isPrecomplete_maximalIdeal
    (complete _ hdimC hresC)

/-- **The end of the base case of the source's proof of [Stacks, Tag 0BGN].** Let `A` be a
Noetherian complete local normal domain of dimension two for which reduction to rational
singularities is possible. Suppose `seq` is the conclusion of [Stacks, Tag 0B4P] — a normal
modification of `Spec A` whose local rings at closed points define rational singularities — and
`rat` resolves, by normalized blowups, the spectrum of the local ring at a singular point of a
normal modification of the spectrum of a two-dimensional Noetherian complete local normal domain,
when that local ring defines a rational singularity (the passes through [Stacks, Tags 0BBV and
0BGE]; this is the premise `hrational` of the 0BGM assembly
`hasResolutionByNormalizedBlowUps_of_isResolution_of_rational`, verbatim). Then `Spec A` has a
resolution of singularities: the modification has finitely many singular points, all closed,
because it is of finite type over the complete ring `A` (Tag 07R5), and the local resolutions
assemble. -/
theorem exists_isResolution_of_isReductionToRationalSingularitiesPossible
    (seq : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A], IsNagataRing A →
      ringKrullDim A = 2 → IsReductionToRationalSingularitiesPossible A →
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (hX : IsNormal X), IsModification f ∧
        ∀ x : X, IsClosed ({x} : Set X) →
          letI := hX; DefinesRationalSingularity (X.presheaf.stalk x))
    (rat : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
      [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B], ringKrullDim B = 2 →
      ∀ (Z : Scheme.{u}) [IsNormal Z] (g : Z ⟶ Spec (.of B)), IsModification g →
        ∀ z ∈ singularLocus Z, DefinesRationalSingularity (Z.presheaf.stalk z) →
          HasResolutionByNormalizedBlowUps (Spec (Z.presheaf.stalk z)))
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    [IsAdicComplete (maximalIdeal A) A] (hdimA : ringKrullDim A = 2)
    (hred : IsReductionToRationalSingularitiesPossible A) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f := by
  obtain ⟨X, f, hX, hf, hrat⟩ := seq A IsNagataRing.of_isPrecomplete_maximalIdeal hdimA hred
  have : IsProper f := hf.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have hdim : topologicalKrullDim X = 2 := by
    rw [topologicalKrullDim_eq_of_isModification f hf, ← hdimA]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A
  have hsing : (singularLocus X).Finite :=
    finite_singularLocus_of_locallyOfFiniteType_over_completeLocalRing A f hdim.le
  refine exists_isResolution_of_isModification_of_singularLocus A f hf hdimA hsing fun x hx => ?_
  exact rat A hdimA X f hf x hx (hrat x (isClosed_singleton_of_mem_singularLocus X hdim.le x hx))

/-- A ring finite and faithful over a ring of Krull dimension two has Krull dimension two. -/
private theorem ringKrullDim_eq_two_of_finite (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [FaithfulSMul R A] (hR : ringKrullDim R = 2) :
    ringKrullDim A = 2 := by
  rw [← hR]; exact (Algebra.IsIntegral.ringKrullDim_eq R A).symm

attribute [local instance] FractionRing.liftAlgebra in
/-- **The beginning of the base case of the source's proof of [Stacks, Tag 0BGN].** Let `A` be a
Noetherian complete local normal domain finite over a regular complete local ring `R` of
dimension two, such that `Frac A / Frac R` has no intermediate field other than its two ends.
Then reduction to rational singularities is possible for `A`: by the dichotomy for minimal
extensions the extension is separable, and then `sep` ([Stacks, Tag 0AXL]) transports reduction
from `R`, where it holds because `R` defines a rational singularity (`reg`,
[Stacks, Tag 0B4Q]); or it is purely inseparable of degree `p`, and then `insep`
([Stacks, Tag 0B4U]) applies. -/
theorem isReductionToRationalSingularitiesPossible_of_forall_eq_bot_or_eq_top
    (reg : ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R],
      ringKrullDim R = 2 → (hR : IsDomain R) → DefinesRationalSingularity R)
    (sep : ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A]
      [CommRing B] [IsLocalRing B] [IsNormalDomain B] [IsNagataRing B] [Algebra A B]
      [Module.Finite A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)],
      ringKrullDim A = 2 → ringKrullDim B = 2 →
      Algebra.IsSeparable (FractionRing A) (FractionRing B) →
      IsReductionToRationalSingularitiesPossible A → IsReductionToRationalSingularitiesPossible B)
    (insep : ∀ (R B : Type u) [CommRing R] [IsRegularLocalRing R]
      [IsAdicComplete (maximalIdeal R) R] [IsDomain R] (p : ℕ), p.Prime → CharP R p →
      ringKrullDim R = 2 → ∀ [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsNormalDomain B]
      [IsAdicComplete (maximalIdeal B) B] [Algebra R B] [Module.Finite R B] [FaithfulSMul R B],
      IsPurelyInseparable (FractionRing R) (FractionRing B) →
      Module.finrank (FractionRing R) (FractionRing B) = p →
      IsReductionToRationalSingularitiesPossible B)
    (R A : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] [Algebra R A] [Module.Finite R A]
    [FaithfulSMul R A] (hR : ringKrullDim R = 2)
    (hmin : ∀ M : IntermediateField (FractionRing R) (FractionRing A), M = ⊥ ∨ M = ⊤) :
    IsReductionToRationalSingularitiesPossible A := by
  have : FiniteDimensional (FractionRing R) (FractionRing A) :=
    Stacks.ResolutionOfSurfaces.finiteDimensional_fractionRing R A
  have hdimA := ringKrullDim_eq_two_of_finite R A hR
  rcases IntermediateField.isSeparable_or_finrank_eq_ringChar_of_forall_eq_bot_or_eq_top hmin with
    hsep | ⟨hp, hpi, hdeg⟩
  · have : IsNormalDomain R := isNormalDomain_of_isRegularLocalRing R
    have : IsNagataRing R := IsNagataRing.of_isPrecomplete_maximalIdeal
    have : IsNagataRing A := IsNagataRing.of_isPrecomplete_maximalIdeal
    have : IsLocalHom (algebraMap R A) :=
      (algebraMap_isIntegral_iff.mpr inferInstance).isLocalHom
        (FaithfulSMul.algebraMap_injective R A)
    exact sep R A hR hdimA hsep
      (isReductionToRationalSingularitiesPossible_of_definesRationalSingularity
        R (reg R hR inferInstance))
  · have : CharP R (ringChar (FractionRing R)) := by
      have := ringChar.charP (FractionRing R)
      refine ⟨fun x => ?_⟩
      rw [← map_eq_zero_iff (algebraMap R (FractionRing R)) (IsFractionRing.injective R _),
        map_natCast, CharP.cast_eq_zero_iff (FractionRing R) (ringChar (FractionRing R))]
    exact insep R A _ hp this hR hpi hdeg

/-- **[Stacks, Tag 0BGN] from the inputs of its proof.** The spectrum of a Noetherian complete
local normal domain of dimension two has a resolution of singularities, granted the five inputs
of the source's proof that are proved elsewhere in this library: the complete case of
[Stacks, Tag 0BGM] (`complete`), [Stacks, Tag 0B4Q] (`reg`), [Stacks, Tag 0AXL] (`sep`),
[Stacks, Tag 0B4U] (`insep`), and the resolution of the rational singularities produced by
[Stacks, Tag 0B4P] (`exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_of_reduction`)
through [Stacks, Tags 0BBV and 0BGE] (`rat`). This is the assembly of
`Stacks.ResolutionOfSurfaces.exists_isResolution_of_steps` with
`exists_isResolution_of_completeCaseStep` (its geometric construction being
`exists_normal_modification_completedStalk_finite_of_isResolution`),
`isReductionToRationalSingularitiesPossible_of_forall_eq_bot_or_eq_top` and
`exists_isResolution_of_isReductionToRationalSingularitiesPossible`; no `@[stacks]` attribute is
attached while the inputs are hypotheses. -/
theorem exists_isResolution_of_isAdicComplete_of_inputs
    (complete : ∀ (C : Type u) [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
      [IsNormalDomain C] [IsAdicComplete (maximalIdeal C) C], ringKrullDim C = 2 →
      (∃ (Z : Scheme.{u}) (h : Z ⟶ Spec (.of C)), IsResolution h) →
      HasResolutionByNormalizedBlowUps (Spec (.of C)))
    (reg : ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R],
      ringKrullDim R = 2 → (hR : IsDomain R) → DefinesRationalSingularity R)
    (sep : ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A]
      [CommRing B] [IsLocalRing B] [IsNormalDomain B] [IsNagataRing B] [Algebra A B]
      [Module.Finite A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)],
      ringKrullDim A = 2 → ringKrullDim B = 2 →
      (letI := FractionRing.liftAlgebra A (FractionRing B);
        Algebra.IsSeparable (FractionRing A) (FractionRing B)) →
      IsReductionToRationalSingularitiesPossible A → IsReductionToRationalSingularitiesPossible B)
    (insep : ∀ (R B : Type u) [CommRing R] [IsRegularLocalRing R]
      [IsAdicComplete (maximalIdeal R) R] [IsDomain R] (p : ℕ), p.Prime → CharP R p →
      ringKrullDim R = 2 → ∀ [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsNormalDomain B]
      [IsAdicComplete (maximalIdeal B) B] [Algebra R B] [Module.Finite R B] [FaithfulSMul R B],
      (letI := FractionRing.liftAlgebra R (FractionRing B);
        IsPurelyInseparable (FractionRing R) (FractionRing B) ∧
        Module.finrank (FractionRing R) (FractionRing B) = p) →
      IsReductionToRationalSingularitiesPossible B)
    (rat : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
      [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B], ringKrullDim B = 2 →
      ∀ (Z : Scheme.{u}) [IsNormal Z] (g : Z ⟶ Spec (.of B)), IsModification g →
        ∀ z ∈ singularLocus Z, DefinesRationalSingularity (Z.presheaf.stalk z) →
          HasResolutionByNormalizedBlowUps (Spec (Z.presheaf.stalk z)))
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f := by
  refine Stacks.ResolutionOfSurfaces.exists_isResolution_of_steps
    (fun B A _ _ _ _ _ _ _ _ _ _ _ _ _ hdimA hB ih =>
      exists_isResolution_of_completeCaseStep
        (fun B A _ _ _ _ _ _ _ _ _ _ hd _ _ _ _ g hg =>
          exists_normal_modification_completedStalk_finite_of_isResolution B A hd g hg)
        complete B A hdimA hB ih)
    (fun R A _ _ _ _ _ _ _ _ _ _ _ _ hR hmin => ?_) A hdim
  let := FractionRing.liftAlgebra R (FractionRing A)
  have hdimA := ringKrullDim_eq_two_of_finite R A hR
  have seq : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A], IsNagataRing A →
      ringKrullDim A = 2 → IsReductionToRationalSingularitiesPossible A →
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (hX : IsNormal X), IsModification f ∧
        ∀ x : X, IsClosed ({x} : Set X) →
          let := hX; DefinesRationalSingularity (X.presheaf.stalk x) := by
    intro A _ _ _ hN hd hr
    obtain ⟨X, f, hX, -, hf, hrat⟩ :=
      exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_of_reduction A hN hd hr
    exact ⟨X, f, hX, hf, hrat⟩
  exact exists_isResolution_of_isReductionToRationalSingularitiesPossible seq rat A hdimA
    (isReductionToRationalSingularitiesPossible_of_forall_eq_bot_or_eq_top reg
      (fun A B _ _ _ _ _ _ _ _ _ _ _ _ hA hB hs hr => sep A B hA hB hs hr)
      (fun R B _ _ _ _ p hp hc hR _ _ _ _ _ _ _ _ hpi hd => insep R B p hp hc hR ⟨hpi, hd⟩)
      R A hR hmin)

end AlgebraicGeometry
