module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# A modification of a two-dimensional normal local ring is an isomorphism off the closed point

Let `B` be a Noetherian local normal domain of dimension at most two, and `p : Y ⟶ Spec(B)` a
modification. Every point of the punctured spectrum `Spec(B) ∖ {𝔪}` has a local ring of dimension
at most one, so over it `p` is finite by [Stacks, Tag 0AB7], and a finite birational morphism onto
a normal integral scheme is an isomorphism by [Stacks, Tag 0AB1]. Hence `p` is an isomorphism over
the punctured spectrum.

This proves the isomorphism half of
`AlgebraicGeometry.ModificationIsFinitePresentationAway`, used by
`AlgebraicGeometry.definesRationalSingularity_stalk_of_isModification`, and the hypothesis
`AlgebraicGeometry.NormalModificationIsIsoAwayFromClosedPoint` of
`AlgebraicGeometry.exists_normalizedBlowUpSeq_definesRationalSingularity_stalk`.

## Main results

* `AlgebraicGeometry.isIso_morphismRestrict_of_isModification`: a modification of the spectrum of
  a Noetherian local normal domain of dimension at most two is an isomorphism over every open
  avoiding the closed point.
* `AlgebraicGeometry.isIso_pullback_puncturedOpen_of_isModification`: the same over the inverse
  image of the punctured open of a scheme along `Spec 𝒪_{X, x} ⟶ X`, in the spelling of
  `AlgebraicGeometry.ModificationIsFinitePresentationAway`.
* `AlgebraicGeometry.modificationIsFinitePresentationAway_of_isLocallyNoetherian`: the hypothesis
  `ModificationIsFinitePresentationAway` holds at every closed point of a locally Noetherian normal
  scheme whose local ring there has dimension at most two.
* `AlgebraicGeometry.normalModificationIsIsoAwayFromClosedPoint`: the hypothesis
  `NormalModificationIsIsoAwayFromClosedPoint A` holds for every Noetherian domain `A` of
  dimension at most two.

## References

* [Stacks Project, Tag 0AB7](https://stacks.math.columbia.edu/tag/0AB7)
* [Stacks Project, Tag 0AB1](https://stacks.math.columbia.edu/tag/0AB1)
* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point of the spectrum of a Noetherian local ring of dimension at most two, other than the
closed point, has a local ring of dimension at most one. -/
theorem ringKrullDim_stalk_le_one_of_ne_closedPoint (B : CommRingCat.{u}) [IsLocalRing B]
    [IsNoetherianRing B] (hdim : ringKrullDim B ≤ 2) (s : Spec B)
    (hs : s ≠ IsLocalRing.closedPoint B) :
    ringKrullDim ((Spec B).presheaf.stalk s) ≤ 1 := by
  have : s.asIdeal.IsPrime := s.2
  have hlt : s.asIdeal < IsLocalRing.maximalIdeal B :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal s.2.ne_top) fun h =>
      hs (PrimeSpectrum.ext h)
  have hht := Ideal.height_strict_mono_of_isPrime hlt
  have hmax : ((IsLocalRing.maximalIdeal B).height : WithBot ℕ∞) ≤ 2 := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; exact hdim
  have hmax' : (IsLocalRing.maximalIdeal B).height ≤ 2 := WithBot.coe_le_coe.mp hmax
  have hle : s.asIdeal.height ≤ 1 :=
    (ENat.lt_add_one_iff (by simp)).mp (lt_of_lt_of_le hht hmax' : s.asIdeal.height < 1 + 1)
  calc ringKrullDim ((Spec B).presheaf.stalk s)
      = ringKrullDim (Localization.AtPrime s.asIdeal) :=
        ringKrullDim_eq_of_ringEquiv (Spec.stalkIso B s).commRingCatIsoToRingEquiv
    _ = (s.asIdeal.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height s.asIdeal _
    _ ≤ 1 := by exact_mod_cast hle

/-- **A modification of the spectrum of a Noetherian local normal domain of dimension at most two
is an isomorphism over every open avoiding the closed point.** Over such an open every local ring
of the base has dimension at most one, so the restricted morphism, proper and birational, is
finite near each point by [Stacks, Tag 0AB7]; being finite and birational onto a normal integral
scheme it is an isomorphism by [Stacks, Tag 0AB1]. -/
theorem isIso_morphismRestrict_of_isModification (B : CommRingCat.{u}) [IsLocalRing B]
    [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] (hdim : ringKrullDim B ≤ 2)
    {Y : Scheme.{u}} (p : Y ⟶ Spec B) (hp : IsModification p) (V : (Spec B).Opens)
    (hV : IsLocalRing.closedPoint B ∉ V) : IsIso (p ∣_ V) := by
  rcases isEmpty_or_nonempty V with hE | hN
  · exact isIso_of_isEmpty _
  have : IsProper p := hp.2.1
  have : IsIntegral Y := hp.2.2
  have hbir : IsBirational (p ∣_ V) := hp.1.restrict V
  have : IsLocallyNoetherian (Spec B) := isLocallyNoetherian_Spec.mpr inferInstance
  have hfin : IsFinite (p ∣_ V) := by
    have : IsLocallyNoetherian V.toScheme := inferInstance
    have hW : ∀ s : V, ∃ W : V.toScheme.Opens, s ∈ W ∧ IsFinite ((p ∣_ V) ∣_ W) := by
      intro s
      have : IsNoetherianRing (V.toScheme.presheaf.stalk s) :=
        isNoetherianRing_of_ringEquiv _ (V.stalkIso s).commRingCatIsoToRingEquiv.symm
      have hs : (s : Spec B) ≠ IsLocalRing.closedPoint B := fun h => hV (h ▸ s.2)
      have hdims : ringKrullDim (V.toScheme.presheaf.stalk s) ≤ 1 :=
        (ringKrullDim_eq_of_ringEquiv (V.stalkIso s).commRingCatIsoToRingEquiv).trans_le
          (ringKrullDim_stalk_le_one_of_ne_closedPoint B hdim s hs)
      exact exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one (p ∣_ V) s hdims
        (Or.inl fun η hη => isAlgebraic_residueField_of_isIso_stalkMap _ η
          (hbir.isIso_stalkMap η hη))
    choose W hmem hWfin using hW
    let : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
      Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite.{u}) W ?_ hWfin
    exact eq_top_iff.mpr fun s _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨s, hmem s⟩
  have : IsNormal (Spec B) := isNormal_spec_of_isIntegrallyClosed B
  have : IsNormal V.toScheme := isNormal_of_isOpenImmersion V.ι
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have hgen : genericPoint (Spec B) ∈ V :=
    ((genericPoint_spec (Spec B)).mem_open_set_iff V.isOpen).mpr
      (let ⟨s⟩ := hN; ⟨s.1, trivial, s.2⟩)
  have : Nonempty (p ⁻¹ᵁ V).toScheme :=
    ⟨⟨genericPoint Y, show p (genericPoint Y) ∈ V by rw [hp.1.genericPoint_eq]; exact hgen⟩⟩
  have : IsIntegral (p ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (p ⁻¹ᵁ V).ι
  exact isIso_of_isIntegralHom_of_isBirational_of_isNormal (p ∣_ V) hbir

/-- **A modification of `Spec 𝒪_{X, x}` is an isomorphism over the punctured spectrum**, for a
closed point `x` whose local ring is a Noetherian normal domain of dimension at most two, in the
spelling of `AlgebraicGeometry.ModificationIsFinitePresentationAway`: the base change of the
modification along the inclusion of the inverse image of `X ∖ {x}` is an isomorphism. -/
theorem isIso_pullback_puncturedOpen_of_isModification {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) [IsDomain (X.presheaf.stalk x)]
    [IsNoetherianRing (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 2)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (X.presheaf.stalk x)) (hp : IsModification p) :
    IsIso ((Over.pullback ((X.fromSpecStalk x) ⁻¹ᵁ GlueingNearPoint.puncturedOpen hx).ι).obj
      (Over.mk p)).hom := by
  set V := (X.fromSpecStalk x) ⁻¹ᵁ GlueingNearPoint.puncturedOpen hx
  have hV : IsLocalRing.closedPoint (X.presheaf.stalk x) ∉ V := by
    change X.fromSpecStalk x (IsLocalRing.closedPoint _) ∉ GlueingNearPoint.puncturedOpen hx
    rw [Scheme.fromSpecStalk_closedPoint]
    exact GlueingNearPoint.notMem_puncturedOpen hx
  have := isIso_morphismRestrict_of_isModification _ hdim p hp V hV
  change IsIso (pullback.snd p V.ι)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  infer_instance

/-- **The hypothesis `ModificationIsFinitePresentationAway` holds** at a closed point of a locally
Noetherian normal scheme whose local ring has dimension at most two. -/
theorem modificationIsFinitePresentationAway_of_isLocallyNoetherian {X : Scheme.{u}}
    [IsNormal X] [IsLocallyNoetherian X] (x : X) (hx : IsClosed ({x} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk x) ≤ 2) :
    ModificationIsFinitePresentationAway x hx := by
  intro Y p _ hp
  have : IsProper p := hp.2.1
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  have hfp : FinitePresentation p := ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨hfp, isIso_pullback_puncturedOpen_of_isModification x hx hdim p hp⟩

/-- **The hypothesis `NormalModificationIsIsoAwayFromClosedPoint A` holds** for every Noetherian
domain `A` of dimension at most two. -/
theorem normalModificationIsIsoAwayFromClosedPoint (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A ≤ 2) :
    NormalModificationIsIsoAwayFromClosedPoint A := by
  intro X f hX hf x hx _ Y p _ hp
  have : IsProper f := hf.2.1
  have : IsIntegral X := hf.2.2
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  have hdimX : topologicalKrullDim X = ringKrullDim A := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hf.1.topologicalKrullDim_eq_of_isClosedMap f.isClosedMap
  have hdimx : ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
    refine le_trans ?_ (hdimX.trans_le hdim)
    rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
    exact le_iSup_of_le x le_rfl
  exact isIso_pullback_puncturedOpen_of_isModification x hx hdimx p hp

end AlgebraicGeometry

end
