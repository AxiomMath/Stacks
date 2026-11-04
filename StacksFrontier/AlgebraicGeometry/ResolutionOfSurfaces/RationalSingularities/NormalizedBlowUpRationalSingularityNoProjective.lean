module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.PuncturedSpectrumModification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SpreadOutModification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.FlatBaseChangeFirstCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayFirstCohomologyDimTwo
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# Rational singularities after finitely many normalized blowups, without projectivity

[Stacks, Tag 0B4P] produces, for a local normal Nagata domain `A` of dimension two for which
reduction to rational singularities is possible, a finite sequence of normalized blowups of
`Spec A` whose local rings at closed points define rational singularities, and adds that the
result is projective over `A`. The source's proof of [Stacks, Tag 0BGN] uses only the first part,
so it is stated here on its own: the projectivity clause is the only place the proof in
`RationalSingularities/NormalizedBlowUpRationalSingularity.lean` uses its hypothesis standing for
[Stacks, Tag 02NS], and without that clause the hypothesis is not needed.

## Main results

* `AlgebraicGeometry.exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_of_leray`: the
  sequence, its normality, its being a modification, and the rational singularity of the local
  rings at its closed points.

## Implementation notes

The proof is that of
`AlgebraicGeometry.exists_normalizedBlowUpSeq_definesRationalSingularity_stalk` with its
projectivity bullet removed, and with two of its remaining four hypotheses discharged: a
modification of the local ring at a closed point is an isomorphism over the punctured spectrum
(`AlgebraicGeometry.normalModificationIsIsoAwayFromClosedPoint`), and Step 4 of the source's proof
of [Stacks, Tag 0BG0] in its corrected form, with the local modification a modification
(`AlgebraicGeometry.isNormal_and_isModification_of_isPullback_fromSpecStalk`; the closed point is
not the generic point because the scheme has dimension two). The two hypotheses still taken are the
Leray sequence of [Stacks, Tag 0AXF] (1) and flat base change [Stacks, Tag 02KH] for the first
higher direct image. No `@[stacks]` attribute is attached: the statement is part of a tag and is
proved over those two inputs.

## References

* [Stacks Project, Tag 0B4P](https://stacks.math.columbia.edu/tag/0B4P)
* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

/-- **The sequence of [Stacks, Tag 0B4P], without its projectivity clause.** Let `A` be a local
normal Nagata domain of dimension two for which reduction to rational singularities is possible.
Granted the Leray sequence `LerayFirstCohomologyExact A` and flat base change
`FlatBaseChangeFirstCohomologyVanishing`, there is a finite sequence of normalized blowups at
closed points `X → Spec A` with `X` normal, `X → Spec A` a modification, and the local ring of `X`
at every closed point defining a rational singularity. -/
public theorem exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_of_leray
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hNagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hReduction : IsReductionToRationalSingularitiesPossible A)
    (h0AXF : LerayFirstCohomologyExact A)
    (h02KH : FlatBaseChangeFirstCohomologyVanishing.{u})
 :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (hX : IsNormal X),
      letI := hX
      NormalizedBlowUpSeq (Spec (.of A)) X f ∧ IsModification f ∧
        ∀ x : X, IsClosed ({x} : Set X) →
          DefinesRationalSingularity (X.presheaf.stalk x) := by
  classical
  have hNoethA : IsNoetherianRing A := hNagata.1
  have hSpecNormal : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have hNagataSpec : IsNagataScheme (Spec (.of A)) := isNagataScheme_spec_of_isNagataRing A hNagata
  -- Step 1: a normal modification of maximal first-cohomology length.
  obtain ⟨X₀, hX₀, f₀, hf₀, hmax⟩ := exists_maximal_length_normal_modification A hReduction
  -- Step 2: dominate it by a sequence of normalized blowups at closed points.
  obtain ⟨W, g, dom, hseq, hWnormal, hgmod, hcomm⟩ :=
    exists_normalizedBlowUpSeq_isModification_dominating A hNagata hdim f₀ hf₀
  have hWmod : IsModification (dom ≫ f₀) := by rw [hcomm]; exact hgmod
  -- the sequence is itself of maximal length: `H¹` injects along the domination.
  obtain ⟨φ₀, hφ₀, -⟩ := h0AXF f₀ dom hX₀ hWnormal hf₀ hWmod
  have htransfer : Module.length A (firstCohomologyAsBaseModule X₀ f₀) ≤
      Module.length A (firstCohomologyAsBaseModule W g) := by
    refine (Module.length_le_of_injective φ₀ hφ₀).trans_eq ?_
    exact congrArg (fun k => Module.length A (firstCohomologyAsBaseModule W k)) hcomm
  have hWmax : ∀ (Y : Scheme.{u}) (_ : IsNormal Y) (p : Y ⟶ Spec (.of A)), IsModification p →
      Module.length A (firstCohomologyAsBaseModule Y p) ≤
        Module.length A (firstCohomologyAsBaseModule W g) :=
    fun Y hY p hp => (hmax Y hY p hp).trans htransfer
  obtain ⟨bound, hBound⟩ := hReduction
  have hWfinite : Module.length A (firstCohomologyAsBaseModule W g) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (hBound W g hgmod) (ENat.natCast_lt_top bound))
  -- Properties of the total space of the sequence.
  obtain ⟨-, hNoethLocW, -, hProperW⟩ := hseq.properties hNagataSpec
  have := hNoethLocW
  have := hProperW
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace g
  have hNoethW : IsNoetherian W := AlgebraicGeometry.IsNoetherian.mk
  refine ⟨W, g, hWnormal, hseq, hgmod, ?_⟩
  -- Rational singularities at the closed points.
  intro x hx Y hY p hp
  have := hY
  -- spread the normal modification `p` of `Spec 𝒪_{W, x}` out to a proper `g' : X' ⟶ W`
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
  -- maximality forces the Leray edge map to be onto, so `R¹g'_*𝒪_{X'}` has no sections
  obtain ⟨φ, hφinj, hφzero⟩ := h0AXF g g' hWnormal hX'normal hgmod hX'mod
  have hsurj := surjective_of_injective_of_length_le φ hφinj hWfinite
    (hWmax X' hX'normal _ hX'mod)
  -- and it is generated by global sections, by the third conclusion of Tag 0AXF
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
  -- flat base change transports the vanishing to `Y`
  exact h02KH x g' p q hsq hg'proper hzero


/-- **The sequence of [Stacks, Tag 0B4P], without its projectivity clause.** Let `A` be a local
normal Nagata domain of dimension two for which reduction to rational singularities is possible.
There is a finite sequence of normalized blowups at closed points `X → Spec A` with `X` normal,
`X → Spec A` a modification, and the local ring of `X` at every closed point defining a rational
singularity. The Leray input is `lerayFirstCohomologyExact_of_ringKrullDim_eq_two` and flat base
change is `flatBaseChangeFirstCohomologyVanishing`. -/
public theorem exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_of_reduction
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hNagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hReduction : IsReductionToRationalSingularitiesPossible A) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (hX : IsNormal X),
      letI := hX
      NormalizedBlowUpSeq (Spec (.of A)) X f ∧ IsModification f ∧
        ∀ x : X, IsClosed ({x} : Set X) →
          DefinesRationalSingularity (X.presheaf.stalk x) :=
  have : IsNoetherianRing A := hNagata.1
  exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_of_leray A hNagata hdim hReduction
    (lerayFirstCohomologyExact_of_ringKrullDim_eq_two A hdim) flatBaseChangeFirstCohomologyVanishing

end

end AlgebraicGeometry
