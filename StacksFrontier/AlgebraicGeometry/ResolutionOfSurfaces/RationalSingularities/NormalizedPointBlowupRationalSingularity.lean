module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.PuncturedSpectrumModification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SpreadOutModification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.FlatBaseChangeFirstCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpQuasiProjectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayFirstCohomologyExactness
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayFirstCohomologyDimTwo
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort

/-!
# Rational singularities after finitely many normalized blowups

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two for which reduction to rational
singularities is possible. [Stacks, Tag 0B4P] produces a finite sequence of normalized blowups
`X = Xₙ ⟶ ⋯ ⟶ X₀ = Spec A` in closed points such that the local ring of `X` at every closed point
defines a rational singularity; moreover `X ⟶ Spec A` is a modification and `X` is a normal
scheme projective over `A`. This file proves it with no carried hypothesis.

## Main results

* `AlgebraicGeometry.normalizedPointBlowupChain_closedPoint_of_normalizedBlowUpSeq`: a sequence
  of normalized blowups of `Spec A` in closed points has its centres over the closed point.
* `AlgebraicGeometry.exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_unconditional`:
  the statement for `AlgebraicGeometry.NormalizedBlowUpSeq`.
* `exists_normalizedPointBlowupChain_definesRationalSingularity_stalk_of_reduction`:
  [Stacks, Tag 0B4P], with every clause of the source.
* `AlgebraicGeometry.exists_normalizedPointBlowupChain_definesRationalSingularity_stalk`: the
  sequence and the rational singularities alone, the form in which the proof of
  [Stacks, Tag 0BGN] uses the tag.

## Implementation notes

The proof is that of
`AlgebraicGeometry.exists_normalizedBlowUpSeq_definesRationalSingularity_stalk`, with each of its
five carried hypotheses discharged: the Leray sequence of [Stacks, Tag 0AXF] (1) is
`AlgebraicGeometry.lerayFirstCohomologyExact_of_ringKrullDim_eq_two`; flat base change in degree
one, [Stacks, Tag 02KH], is `AlgebraicGeometry.flatBaseChangeFirstCohomologyVanishing`;
quasi-projectivity of blowups, [Stacks, Tag 02NS], is `AlgebraicGeometry.blowUpIsQuasiProjective`;
the isomorphism of a normal modification of a local ring over its punctured spectrum,
[Stacks, Tag 0AB7], is `AlgebraicGeometry.normalModificationIsIsoAwayFromClosedPoint`; and Step 4
of the source's proof of [Stacks, Tag 0BG0] is
`AlgebraicGeometry.isNormal_and_isModification_of_isPullback_fromSpecStalk`, which asks, as the
source does, that the local modification be a modification and not only normal (the carried form
`SpreadOutIsNormalModificationOverSpec` is false as stated).

[Stacks, Tag 0B4P] is registered here, on
`AlgebraicGeometry.exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_unconditional`,
which proves every clause of the tag with no carried hypothesis.

## References

* [Stacks Project, Tag 0B4P](https://stacks.math.columbia.edu/tag/0B4P)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
* [Stacks Project, Tag 0B3X](https://stacks.math.columbia.edu/tag/0B3X)
* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Over the spectrum of a normal local Nagata ring, a finite sequence of normalized blowups at
closed points is a chain of normalized blowups at points lying over the closed point. -/
theorem normalizedPointBlowupChain_closedPoint_of_normalizedBlowUpSeq (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] (hNagata : IsNagataRing A) {X : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} (hseq : NormalizedBlowUpSeq (Spec (.of A)) X f) :
    Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
      {IsLocalRing.closedPoint A} X f := by
  have : IsNoetherianRing A := hNagata.1
  have : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have hNagataSpec : IsNagataScheme (Spec (.of A)) := isNagataScheme_spec_of_isNagataRing A hNagata
  induction hseq with
  | refl => exact Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain.refl
  | @blowUp W h prev hW w hw ih =>
    obtain ⟨-, -, -, hproper⟩ := prev.properties hNagataSpec
    have hclosed : IsClosed ({h.base w} : Set (Spec (.of A))) := by
      have := h.isClosedMap _ hw
      rwa [Set.image_singleton] at this
    exact ih.step hW w hw (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hclosed)))

/-- **[Stacks, Tag 0B4P].** For a local normal Nagata domain `A` of dimension two for which
reduction to rational singularities is possible, there is a finite sequence of normalized blowups
at closed points `X = Xₙ ⟶ ⋯ ⟶ X₁ ⟶ X₀ = Spec A` with `X` normal, the structure morphism a
projective modification, and the local ring of `X` at every closed point defining a rational
singularity. -/
@[stacks 0B4P]
theorem exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_unconditional
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hNagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hReduction : IsReductionToRationalSingularitiesPossible A) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (hX : IsNormal X),
      letI := hX
      NormalizedBlowUpSeq (Spec (.of A)) X f ∧ IsModification f ∧ IsProjectiveMorphism f ∧
        ∀ x : X, IsClosed ({x} : Set X) →
          DefinesRationalSingularity (X.presheaf.stalk x) := by
  classical
  have hNoethA : IsNoetherianRing A := hNagata.1
  have h0AXF : LerayFirstCohomologyExact A :=
    lerayFirstCohomologyExact_of_ringKrullDim_eq_two A hdim
  have h02NS : BlowUpIsQuasiProjective.{u} := blowUpIsQuasiProjective
  have hSpecNormal : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have hNagataSpec : IsNagataScheme (Spec (.of A)) := isNagataScheme_spec_of_isNagataRing A hNagata
  obtain ⟨X₀, hX₀, f₀, hf₀, hmax⟩ := exists_maximal_length_normal_modification A hReduction
  obtain ⟨W, g, dom, hseq, hWnormal, hgmod, hcomm⟩ :=
    exists_normalizedBlowUpSeq_isModification_dominating A hNagata hdim f₀ hf₀
  have hWmod : IsModification (dom ≫ f₀) := hcomm ▸ hgmod
  obtain ⟨φ₀, hφ₀, -⟩ := h0AXF f₀ dom hX₀ hWnormal hf₀ hWmod
  have htransfer : Module.length A (firstCohomologyAsBaseModule X₀ f₀) ≤
      Module.length A (firstCohomologyAsBaseModule W g) :=
    (Module.length_le_of_injective φ₀ hφ₀).trans_eq
      (congrArg (fun k => Module.length A (firstCohomologyAsBaseModule W k)) hcomm)
  have hWmax : ∀ (Y : Scheme.{u}) (_ : IsNormal Y) (p : Y ⟶ Spec (.of A)), IsModification p →
      Module.length A (firstCohomologyAsBaseModule Y p) ≤
        Module.length A (firstCohomologyAsBaseModule W g) :=
    fun Y hY p hp => (hmax Y hY p hp).trans htransfer
  obtain ⟨bound, hBound⟩ := hReduction
  have hWfinite : Module.length A (firstCohomologyAsBaseModule W g) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (hBound W g hgmod) (ENat.natCast_lt_top bound))
  obtain ⟨-, hNoethLocW, -, hProperW⟩ := hseq.properties hNagataSpec
  have := hNoethLocW
  have := hProperW
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace g
  have hNoethW : IsNoetherian W := AlgebraicGeometry.IsNoetherian.mk
  refine ⟨W, g, hWnormal, hseq, hgmod, ?_, ?_⟩
  · obtain ⟨M, hMinv, hMample⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of A))
    have := hMinv
    exact hseq.isProjectiveMorphism h02NS hNagataSpec M hMample
  intro x hx Y hY p hp
  have := hY
  have hemb := (GlueingNearPoint.puncturedOpen hx).isOpen.isOpenEmbedding_subtypeVal
  have : NoetherianSpace (GlueingNearPoint.puncturedOpen hx).toScheme :=
    hemb.isEmbedding.noetherianSpace
  have hqc : QuasiCompact (GlueingNearPoint.puncturedOpen hx).ι :=
    quasiCompact_of_noetherianSpace_source _
  have hfp : FinitePresentation p := by
    have := hp.isProper
    have : IsDomain ↥(W.presheaf.stalk x) := hWnormal.stalk_isDomain x
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨X', g', q, hg'away, hg'proper, hsq⟩ :=
    exists_isPullback_fromSpecStalk_of_isProper W x hx hqc p
      ⟨hfp, normalModificationIsIsoAwayFromClosedPoint A hdim.le g hWnormal hgmod x hx
        inferInstance p hY hp⟩ hp.isProper
  have hxη : letI := hgmod.source_isIntegral; x ≠ genericPoint W := by
    let := hgmod.source_isIntegral
    intro hxg
    have hdimW : topologicalKrullDim W = 2 := by
      rw [topologicalKrullDim_eq_of_isModification g hgmod, ← hdim]
      exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A
    obtain ⟨z, hz⟩ := exists_ne_of_topologicalKrullDim_eq_two hdimW x
    have hzc : z ∈ closure ({x} : Set W) := by
      rw [hxg, (genericPoint_spec W).def]
      exact Set.mem_univ z
    rw [hx.closure_eq] at hzc
    exact hz hzc
  obtain ⟨hX'normal, hX'mod⟩ :=
    isNormal_and_isModification_of_isPullback_fromSpecStalk g hgmod x hx hxη g' p q hsq
      hg'proper hg'away.2 hY hp
  obtain ⟨φ, hφinj, hφzero⟩ := h0AXF g g' hWnormal hX'normal hgmod hX'mod
  have hsurj := surjective_of_injective_of_length_le φ hφinj hWfinite
    (hWmax X' hX'normal _ hX'mod)
  let T : SemistableReduction.TwoModifications.{u} :=
    { situation := vanishingSituationOfModification A hdim g hgmod
      X' := X'
      g := g'
      modification' := hX'mod
      normal := hWnormal }
  obtain ⟨G⟩ := T.nonempty_generatingSections_rightDerived_one_pushforward
  have hzero : IsZero (((Scheme.Modules.pushforward g').rightDerived 1).obj
      (SheafOfModules.unit X'.ringCatSheaf)) :=
    @isZero_of_generatingSections_of_subsingleton_sections _ _ G (hφzero hsurj)
  exact flatBaseChangeFirstCohomologyVanishing x g' p q hsq hg'proper hzero

/-- **[Stacks, Tag 0B4P].** Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension
two for which reduction to rational singularities is possible. Then there is a finite sequence of
normalized blowups `X = Xₙ ⟶ ⋯ ⟶ X₁ ⟶ X₀ = Spec A` in closed points such that for every closed
point `x ∈ X` the local ring `𝒪_{X, x}` defines a rational singularity. Moreover `X ⟶ Spec A` is
a modification and `X` is a normal scheme projective over `A`.

The centres of a sequence of normalized blowups in closed points of schemes proper over
`Spec A` lie over the closed point of `Spec A`, which is how the sequence is recorded here. -/
theorem exists_normalizedPointBlowupChain_definesRationalSingularity_stalk_of_reduction
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hN : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hred : IsReductionToRationalSingularitiesPossible A) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
      Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
        {IsLocalRing.closedPoint A} X f ∧
      IsNormal X ∧ IsModification f ∧ IsProjectiveMorphism f ∧
      ∀ x : X, IsClosed ({x} : Set X) → ∃ _ : IsDomain (X.presheaf.stalk x),
        DefinesRationalSingularity (X.presheaf.stalk x) := by
  obtain ⟨X, f, hX, hseq, hmod, hproj, hrat⟩ :=
    exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_unconditional A hN hdim hred
  exact ⟨X, f, normalizedPointBlowupChain_closedPoint_of_normalizedBlowUpSeq A hN hseq, hX, hmod,
    hproj, fun x hx => ⟨hX.stalk_isDomain x, hrat x hx⟩⟩

/-- [Stacks, Tag 0B4P] in the form consumed by the proof of [Stacks, Tag 0BGN]: the sequence of
normalized blowups over the closed point, and the rational singularity of the local rings at its
closed points. -/
theorem exists_normalizedPointBlowupChain_definesRationalSingularity_stalk
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hN : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hred : IsReductionToRationalSingularitiesPossible A) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
      Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
        {IsLocalRing.closedPoint A} X f ∧
      ∀ x : X, IsClosed ({x} : Set X) → ∃ _ : IsDomain (X.presheaf.stalk x),
        DefinesRationalSingularity (X.presheaf.stalk x) := by
  obtain ⟨X, f, hchain, -, -, -, hrat⟩ :=
    exists_normalizedPointBlowupChain_definesRationalSingularity_stalk_of_reduction A hN hdim hred
  exact ⟨X, f, hchain, hrat⟩

end AlgebraicGeometry

end
