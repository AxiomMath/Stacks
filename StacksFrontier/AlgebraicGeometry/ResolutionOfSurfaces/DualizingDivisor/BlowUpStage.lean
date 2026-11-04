module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.FlatBaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.BlowUpDualizingTrivial
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.BlowUpTrivialModule
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.BlowupChainIntegral
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.TrivialOfFlatCover
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality

/-!
# The blowup of a rational double point has trivial twisted inverse image

Let `W` be a Noetherian normal integral scheme and `w ∈ W` a closed singular point whose local
ring is a rational double point ([Stacks, Tag 0BGC]). The blowup `b : W' ⟶ W` in `w` satisfies
`b^×(𝒪_W[0]) ≅ 𝒪_{W'}[0]`: by flat base change of `b^×` ([Stacks, Tag 0E9U]) along the open
immersion of `W ∖ {w}` (over which `b` is an isomorphism) and along `Spec 𝒪_{W,w} ⟶ W` (over which
`b` is the blowup of a Gorenstein rational surface singularity, whose dualizing complex is
trivial), `b^×(𝒪_W[0])` is trivial after two flat pullbacks covering `W'`, hence a module `L` in
degree zero with `L ≅ 𝒪_{W'}`. This is the stage lemma of the proof of the second sentence of
[Stacks, Tag 0EA2].

## Main results

* `AlgebraicGeometry.DualizingDivisor.hasTrivialTwistedInverseImage_blowUpToBase`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open CategoryTheory Limits Stacks.Duality

universe u

namespace AlgebraicGeometry.DualizingDivisor

open BlowUpDualizing

/-- `𝒪_X[0]` is bounded below. -/
theorem isBoundedBelow_unitQC (X : Scheme.{u}) : DerivedCategoryB.IsBoundedBelow (unitQC X).obj :=
  ⟨0, fun n hn => DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor X.Modules 0).obj
    (Scheme.unitModule X)) 0 n hn⟩

/-- **The blowup of a rational double point has trivial twisted inverse image**:
`b^×(𝒪_W[0]) ≅ 𝒪_{W'}[0]` for the blowup `b` of `W` in a closed singular point `w` with
`𝒪_{W,w} ≅ A`, `A` a rational double point. -/
theorem hasTrivialTwistedInverseImage_blowUpToBase {W : Scheme.{u}} [IsNoetherian W]
    [IsIntegral W] [IsNormal W] {w : W} (hw : IsClosed ({w} : Set W))
    (hsing : w ∈ singularLocus W) (S : RationalDoublePointSituation.{u})
    (e : S.A ≃+* W.presheaf.stalk w) :
    HasTrivialTwistedInverseImage
      (blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : TopologicalSpace.Closeds W))) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : TopologicalSpace.Closeds W)
  set b := blowUpToBase I
  have hI : (I.support : Set W) = {w} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hO := isIso_c_blowUpToBase_of_mem_singularLocus hw hsing
  have : IsNoetherian (blowUp I) :=
    have := LocallyOfFiniteType.isLocallyNoetherian b
    have : CompactSpace (blowUp I) := QuasiCompact.compactSpace_of_compactSpace b
    ⟨⟩
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward b
  set U : W.Opens := I.support.compl
  have : CompactSpace U := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian U.toScheme := ⟨⟩
  have sqU : IsPullback (b ⁻¹ᵁ U).ι (b ∣_ U) b U.ι := (isPullback_morphismRestrict b U).flip
  obtain ⟨h, sq, hh, -⟩ := exists_isPullback_blowUpScheme S.A w hw e
  -- flat base change along `U ⟶ W`
  have fU := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat_right sqU
    (unitQC W) (isBoundedBelow_unitQC W)
  have fA := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat_right sq.flip
    (unitQC W) (isBoundedBelow_unitQC W)
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (b ∣_ U)
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (blowUpToBase (centre S.A))
  obtain ⟨tU⟩ := hasTrivialTwistedInverseImage_of_isIso (b ∣_ U)
  have : IsNormal (Spec (.of S.A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed S.A)
  let S' := rationalSingularitySituationOfModification S.A S.nagata S.dimension_two
    S.definesRationalSingularity (𝟙 _) (isModification_id _)
  obtain ⟨t0⟩ :=
    RationalSingularitySituation.nonempty_relativeDualizingComplex_blowUp_iso_unit_of_isGorenstein
      S' S.gorenstein S.not_isRegularLocalRing
  let tA : (twistedInverseImage (blowUpToBase (centre S.A))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj (unitQC (Spec (.of S.A))) ≅
      unitQC (blowUpScheme S.A) :=
    (ObjectProperty.fullyFaithfulι _).preimageIso t0
  let K := (twistedInverseImage b (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).obj
    (unitQC W)
  let e₁ : (quasiCoherentDerivedPullback' (b ⁻¹ᵁ U).ι).obj K ≅ unitQC _ :=
    @asIso _ _ _ _ _ fU ≪≫
      (twistedInverseImage _ _).mapIso (quasiCoherentDerivedPullbackUnitIso U.ι) ≪≫
      tU
  let e₂ : (quasiCoherentDerivedPullback' h).obj K ≅ unitQC _ :=
    @asIso _ _ _ _ _ fA ≪≫ (twistedInverseImage _ _).mapIso
      (quasiCoherentDerivedPullbackUnitIso (specToOfRingEquivStalk S.A w e)) ≪≫ tA
  obtain ⟨L, hL, ⟨φK⟩, ⟨eL₁⟩, ⟨eL₂⟩⟩ := exists_iso_singleQuasiCoherent_of_pullback_iso _ h
    (mem_range_or_mem_range_of_isPullback I hI S.A e h sq) K e₁ e₂
  obtain ⟨ψ⟩ := nonempty_iso_unit_of_pullback_iso_of_blowUp I hI hO S.A S.dimension_two e h sq L
    eL₁ eL₂
  exact ⟨φK ≪≫ (ObjectProperty.fullyFaithfulι _).preimageIso
    ((DerivedCategory.singleFunctor _ 0).mapIso ψ)⟩

end AlgebraicGeometry.DualizingDivisor

end
