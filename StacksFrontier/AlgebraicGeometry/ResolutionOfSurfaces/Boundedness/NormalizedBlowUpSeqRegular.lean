module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularPointBlowupCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingDefinesRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageBlowUp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CohomologyModelBridge
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpReduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpClosedPointDimension
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationIsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpClosedPointDimension
import all StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regular local rings and `H¹(𝒪) = 0` along normalized blowups of a regular surface germ

Let `A` be a Nagata regular local ring of dimension two. Along a sequence of normalized blowups of
`Spec A` at closed points every closed point has a regular two-dimensional local ring, so each
blowup is regular over its centre and normal, the normalization does nothing, and `H¹(𝒪) = 0`
survives the blowup (`AlgebraicGeometry.isZero_rightDerived_evaluation_one_blowUp_pointIdeal`,
which rests on [Stacks, Tags 0AGS and 0AXF]). This is the inductive step of a proof of
[Stacks, Tag 0B4Q].

## Main results

* `AlgebraicGeometry.isRegularLocalRing_stalk_blowUp_and_isNormal`: the blowup of a normal scheme
  at a closed point with regular two-dimensional local ring is normal, with regular local rings
  over the centre.
* `AlgebraicGeometry.isRegularLocalRing_and_isZero_of_normalizedBlowUpSeq`: along a sequence of
  normalized blowups of `Spec A`, closed points have regular local rings and `H¹(𝒪) = 0`.

## Implementation notes

[Stacks, Tag 0B4Q] itself is
`AlgebraicGeometry.definesRationalSingularity_of_isRegularLocalRing_of_isNagataRing` in
`Boundedness/RegularLocalRingRational.lean` and is not restated here.
`AlgebraicGeometry.isIso_stalkMap_blowUpToBase_of_ne` is used from
`RationalDoublePoints/StageBlowUp.lean`, and
`AlgebraicGeometry.ringKrullDim_stalk_eq_two_of_isModification` from
`Boundedness/RegularLocalRingDefinesRational.lean`.

## References

* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A local ring is its own localization at its maximal ideal. -/
theorem nonempty_ringEquiv_localization_maximalIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    Nonempty (A ≃+* Localization.AtPrime (IsLocalRing.maximalIdeal A)) := by
  have hM : (IsLocalRing.maximalIdeal A).primeCompl ≤ IsUnit.submonoid A := fun r hr =>
    IsLocalRing.notMem_maximalIdeal.mp hr
  exact ⟨(IsLocalization.atUnits A (IsLocalRing.maximalIdeal A).primeCompl hM
    (S := Localization.AtPrime (IsLocalRing.maximalIdeal A))).toRingEquiv⟩

/-- **The blowup of a normal scheme at a closed point with regular two-dimensional local ring:**
its local rings over the centre are regular, its other local rings are those of the base, and it
is normal. -/
@[ega "IV 19.4.4" "special case"]
theorem isRegularLocalRing_stalk_blowUp_and_isNormal {X : Scheme.{u}} [IsNormal X] (w : X)
    (hw : IsClosed ({w} : Set X)) [IsRegularLocalRing (X.presheaf.stalk w)]
    (hdim : ringKrullDim (X.presheaf.stalk w) = 2) :
    (∀ y : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)),
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)) y = w →
        IsRegularLocalRing ((blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨{w}, hw⟩ : Closeds X))).presheaf.stalk y)) ∧
      IsNormal (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X))) := by
  have hreg := fun y hy => isRegularLocalRing_stalk_blowUp_of_mapsTo
    (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)) w hw rfl inferInstance hdim y hy
  refine ⟨hreg, (isNormal_iff_stalk_normal _).2 fun y => ?_⟩
  by_cases hy : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)) y = w
  · have := hreg y hy
    exact ⟨IsRegularLocalRing.isDomain _, isIntegrallyClosed_of_isRegularLocalRing _⟩
  · have := isIso_stalkMap_blowUpToBase_of_ne w hw y hy
    have := IsNormal.stalk_normal (X := X)
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds X)) y)
    let e := (asIso ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : Closeds X))).stalkMap y)).commRingCatIsoToRingEquiv
    have : IsDomain ((blowUp (Scheme.IdealSheafData.vanishingIdeal
        (⟨{w}, hw⟩ : Closeds X))).presheaf.stalk y) :=
      Function.Injective.isDomain e.symm.toRingHom e.symm.injective
    exact ⟨this, IsIntegrallyClosed.of_equiv e⟩

/-- `H¹(𝒪) = 0` passes from a scheme to an isomorphic one. -/
theorem isZero_structureSheafH1_of_isIso {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsIso φ]
    (h : IsZero (structureSheafH1 X)) : IsZero (structureSheafH1 Y) := by
  have hc : IsIso φ.c := PresheafedSpace.c_isIso_of_iso φ.toPshHom
  have : Subsingleton (structureSheafH1 X) := ModuleCat.isZero_iff_subsingleton.mp h
  have : Subsingleton ((forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤)))
      AddCommGrpCat.{u}).obj (structureSheafH1 X)) := this
  have hsub := (leraySmulEdge_injective φ hc).subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub

/-- A scheme whose stalk map at `y` is an isomorphism onto a regular local ring has regular
local ring at `y`. -/
private theorem isRegularLocalRing_stalk_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (y : X)
    [IsIso (f.stalkMap y)] [IsRegularLocalRing (Y.presheaf.stalk (f y))] :
    IsRegularLocalRing (X.presheaf.stalk y) :=
  IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv

/-- **Along a sequence of normalized blowups of the spectrum of a Nagata regular local ring of
dimension two, closed points have regular local rings and `H¹(𝒪) = 0`.** At each step the centre
is a closed point with a regular local ring, two-dimensional because the stage is a modification
of `Spec A`; the blowup is regular over the centre and an isomorphism elsewhere, so it is normal,
its normalization is an isomorphism, and `H¹(𝒪) = 0` survives the blowup. -/
theorem isRegularLocalRing_and_isZero_of_normalizedBlowUpSeq (A : Type u) [CommRing A]
    [IsRegularLocalRing A] [IsNagataRing A] (hdim : ringKrullDim A = 2) {W : Scheme.{u}}
    {g : W ⟶ Spec (.of A)} (hseq : NormalizedBlowUpSeq (Spec (.of A)) W g) :
    (∀ w : W, IsClosed ({w} : Set W) → IsRegularLocalRing (W.presheaf.stalk w)) ∧
      IsZero (structureSheafH1 W) := by
  have : IsNormalDomain A := isNormalDomain_of_isRegularLocalRing A
  have : IsNoetherianRing A := (inferInstance : IsNagataRing A).1
  have : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have hS : IsNagataScheme (Spec (.of A)) := isNagataScheme_spec_of_isNagataRing A inferInstance
  have hdimS : topologicalKrullDim (Spec (.of A)) = 2 :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans hdim
  induction hseq with
  | refl =>
    refine ⟨fun w hw => ?_, ?_⟩
    · have hwc : w = IsLocalRing.closedPoint A := by
        have hmax : w.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal w).mp hw
        exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
      subst hwc
      obtain ⟨e⟩ := nonempty_ringEquiv_localization_maximalIdeal A
      exact IsRegularLocalRing.of_ringEquiv ((e.trans (Spec.stalkIso (CommRingCat.of A)
        (IsLocalRing.closedPoint A)).commRingCatIsoToRingEquiv.symm))
    · exact (isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived _).1
        (firstStructureSheafCohomologyVanishes_of_isAffine _)
  | @blowUp X f prev hX x hx ih =>
    obtain ⟨hreg, hH⟩ := ih
    obtain ⟨-, hLN, hN, -⟩ := prev.properties hS
    obtain ⟨hmod, -⟩ := prev.isModification hS hdimS
    have : IsIntegral X := hmod.source_isIntegral
    have hd2 := ringKrullDim_stalk_eq_two_of_isModification A hdim f hmod x hx
    have := hreg x hx
    set M := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) with hM
    have hblowH : IsZero (structureSheafH1 (blowUp M)) :=
      isZero_rightDerived_evaluation_one_blowUp_pointIdeal x hx hd2 hH
    obtain ⟨hregB, hBN⟩ := isRegularLocalRing_stalk_blowUp_and_isNormal x hx hd2
    have hν : IsIso (Scheme.normalization (blowUp M)
        (Stacks.Blowup.finite_irreducibleComponents_blowUp M hX)) :=
      Scheme.isIso_normalization_of_isNormal _ _
    refine ⟨fun w hw => ?_, ?_⟩
    · let ν := Scheme.normalization (blowUp M)
        (Stacks.Blowup.finite_irreducibleComponents_blowUp M hX)
      have hνw : IsClosed ({ν w} : Set (blowUp M)) := by
        simpa using ν.isClosedMap _ hw
      have hregν : IsRegularLocalRing ((blowUp M).presheaf.stalk (ν w)) := by
        by_cases hy : blowUpToBase M (ν w) = x
        · exact hregB _ hy
        · have := isIso_stalkMap_blowUpToBase_of_ne x hx (ν w) hy
          have := hreg _ (by simpa using (blowUpToBase M).isClosedMap _ hνw)
          exact isRegularLocalRing_stalk_of_isIso_stalkMap (blowUpToBase M) (ν w)
      exact isRegularLocalRing_stalk_of_isIso_stalkMap ν w
    · exact isZero_structureSheafH1_of_isIso (inv (Scheme.normalization (blowUp M)
        (Stacks.Blowup.finite_irreducibleComponents_blowUp M hX))) hblowH

end AlgebraicGeometry

end
