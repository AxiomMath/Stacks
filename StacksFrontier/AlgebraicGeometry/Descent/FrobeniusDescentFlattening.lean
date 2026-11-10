module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformIsoOverOpen
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Reduced
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentFlatBase
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFinitePresentationFromFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.LowerSemicontinuity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyConnectedFibres

/-!
# Flattening by blowing up, in the proof of Stacks Tag 0EXH

Let `f : X ⟶ Y` be proper with geometrically connected fibres, flat over a dense open `U ⊆ Y`,
and let `b : Y' ⟶ Y` be the blowup of `Y` in a quasi-coherent ideal `ℐ` whose support is disjoint
from `U`, with strict transform `f' : X' ⟶ Y'` of `f` flat and of finite presentation (Stacks Tag
081R). The proof of Stacks Tag 0EXH uses that:

* the inverse image `b⁻¹U` is dense in `Y'` (its complement lies in the exceptional divisor, an
  effective Cartier divisor, Stacks Tag 02OS);
* over `b⁻¹U` the strict transform is the base change of `f` over `U`;
* hence `f'` is surjective, `f'_*𝒪 = 𝒪` over `b⁻¹U` when `f_*𝒪 = 𝒪` over `U`, and all fibres of
  `f'` are geometrically connected: the number of geometric connected components of the fibres of
  the flat proper morphism of finite presentation `f'` is lower semicontinuous (Stacks Tag 0BUI)
  and equal to one on the dense open `b⁻¹U`.

## Main results

* `AlgebraicGeometry.dense_preimage_blowUpToBase`.
* `AlgebraicGeometry.isPullback_strictTransformToBlowUp_morphismRestrict`.
* `AlgebraicGeometry.surjective_strictTransformToBlowUp`.
* `AlgebraicGeometry.isIso_c_strictTransformToBlowUp_morphismRestrict`.
* `AlgebraicGeometry.geometricallyConnected_strictTransformToBlowUp`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 0BUI](https://stacks.math.columbia.edu/tag/0BUI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The blowup is an isomorphism over every open disjoint from its centre. -/
theorem isIso_blowUpToBase_morphismRestrict (ℐ : Y.IdealSheafData) {U : Y.Opens}
    (h : Disjoint (U : Set Y) (ℐ.support : Set Y)) : IsIso (blowUpToBase ℐ ∣_ U) :=
  isIso_morphismRestrict_of_le _ (fun _ hy ↦ Set.disjoint_left.mp h hy)
    (isIso_blowUp_restrict_compl_support ℐ)

/-- **The inverse image of a dense open disjoint from the centre is dense in the blowup.** -/
theorem dense_preimage_blowUpToBase (ℐ : Y.IdealSheafData) {U : Y.Opens} (hU : Dense (U : Set Y)) :
    Dense ((blowUpToBase ℐ ⁻¹ᵁ U : (blowUp ℐ).Opens) : Set (blowUp ℐ)) := by
  let b := blowUpToBase ℐ
  let D := exceptionalIdeal ℐ
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal ℐ
  have hO : Dense (D.support.compl : Set (blowUp ℐ)) := by
    have : IsAffineHom (Scheme.Opens.ι D.support.compl) :=
      Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor D hD
    have : IsSchemeTheoreticallyDominant (Scheme.Opens.ι D.support.compl) :=
      (Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant
        D.support.compl).mp
        (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor D hD)
    have hdense := (Scheme.Opens.ι D.support.compl).denseRange
    rwa [DenseRange, Scheme.Opens.range_ι] at hdense
  let V : Y.Opens := ⟨ℐ.supportᶜ, ℐ.support.isClosed.isOpen_compl⟩
  have : IsIso (b ∣_ V) := isIso_blowUp_restrict_compl_support ℐ
  have hOV : (D.support.compl : Set (blowUp ℐ)) = b ⁻¹' (V : Set Y) := by
    ext y
    change y ∉ ((ℐ.comap b).support : Set _) ↔ _
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  rw [dense_iff_inter_open]
  intro G hG ⟨x₀, hx₀⟩
  obtain ⟨x, hxG, hxO⟩ := hO.inter_open_nonempty G hG ⟨x₀, hx₀⟩
  have hxV : b x ∈ (V : Set Y) := by rwa [← Set.mem_preimage, ← hOV]
  let e := (b ∣_ V).homeomorph
  let G' : Set (b ⁻¹ᵁ V : (blowUp ℐ).Opens) := Subtype.val ⁻¹' G
  have hG' : IsOpen (V.ι.base '' (e '' G')) :=
    V.ι.isOpenEmbedding.isOpenMap _ (e.isOpenMap _ (hG.preimage continuous_subtype_val))
  obtain ⟨y, hyG, hyU⟩ := hU.inter_open_nonempty _ hG'
    ⟨b x, ⟨b x, hxV⟩, ⟨⟨x, hxV⟩, hxG, Subtype.ext (morphismRestrict_base_coe b V ⟨x, hxV⟩)⟩, rfl⟩
  obtain ⟨_, ⟨w, hwG, rfl⟩, rfl⟩ := hyG
  refine ⟨w.1, hwG, ?_⟩
  change b w.1 ∈ (U : Set Y)
  have : V.ι.base (e w) = b w.1 := morphismRestrict_base_coe b V w
  rwa [← this]

/-- **Over the inverse image of an open disjoint from the centre, the strict transform is the
base change.** The square formed by the restrictions of the strict transform and of `f` is
cartesian. -/
theorem isPullback_strictTransformToBlowUp_morphismRestrict (f : X ⟶ Y) (ℐ : Y.IdealSheafData)
    {U : Y.Opens} (h : Disjoint (U : Set Y) (ℐ.support : Set Y)) :
    ∃ t : ((strictTransformToBlowUp f ℐ) ⁻¹ᵁ (blowUpToBase ℐ ⁻¹ᵁ U)).toScheme ⟶
        (f ⁻¹ᵁ U).toScheme,
      IsPullback t (strictTransformToBlowUp f ℐ ∣_ (blowUpToBase ℐ ⁻¹ᵁ U)) (f ∣_ U)
        ((blowUpToBase ℐ).resLE U (blowUpToBase ℐ ⁻¹ᵁ U) le_rfl) := by
  let b := blowUpToBase ℐ
  let fW := pullback.snd f b
  let i₁ := (Stacks.StrictTransform.ideal f b (exceptionalIdeal ℐ)).subschemeι
  have sq := Stacks.Chow.isPullback_morphismRestrict_of_isPullback
    (IsPullback.of_hasPullback f b) U
  have hi : IsIso (i₁ ∣_ (fW ⁻¹ᵁ (b ⁻¹ᵁ U))) :=
    Stacks.StrictTransform.isIso_subschemeι_restrict f b (exceptionalIdeal ℐ)
      (preimage_le_exceptionalComplement f ℐ h)
  have hcomp : strictTransformToBlowUp f ℐ ∣_ (b ⁻¹ᵁ U) =
      (i₁ ∣_ (fW ⁻¹ᵁ (b ⁻¹ᵁ U))) ≫ (fW ∣_ (b ⁻¹ᵁ U)) :=
    morphismRestrict_comp i₁ fW (b ⁻¹ᵁ U)
  have s : IsPullback (i₁ ∣_ (fW ⁻¹ᵁ (b ⁻¹ᵁ U))) (strictTransformToBlowUp f ℐ ∣_ (b ⁻¹ᵁ U))
      (fW ∣_ (b ⁻¹ᵁ U)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [hcomp, Category.comp_id]⟩
  have key := s.paste_horiz sq
  rw [Category.id_comp] at key
  exact ⟨_, key⟩

/-- **`f_*𝒪 = 𝒪` over an open disjoint from the centre passes to the strict transform over its
inverse image.** -/
theorem isIso_c_strictTransformToBlowUp_morphismRestrict (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (ℐ : Y.IdealSheafData) {U : Y.Opens}
    (h : Disjoint (U : Set Y) (ℐ.support : Set Y)) (hU : IsIso (f ∣_ U).c) :
    IsIso (strictTransformToBlowUp f ℐ ∣_ (blowUpToBase ℐ ⁻¹ᵁ U)).c := by
  obtain ⟨t, sq⟩ := isPullback_strictTransformToBlowUp_morphismRestrict f ℐ h
  have := isIso_blowUpToBase_morphismRestrict ℐ h
  have : IsIso ((blowUpToBase ℐ).resLE U (blowUpToBase ℐ ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  exact Stacks.AlgebraicGeometry.isIso_c_of_isPullback_of_flat sq hU

/-- The strict transform of a proper morphism along a blowup is proper. -/
private theorem isProper_strictTransformToBlowUp (f : X ⟶ Y) [IsProper f]
    (ℐ : Y.IdealSheafData) : IsProper (strictTransformToBlowUp f ℐ) := by
  change IsProper ((Stacks.StrictTransform.ideal f (blowUpToBase ℐ)
    (exceptionalIdeal ℐ)).subschemeι ≫ pullback.snd f (blowUpToBase ℐ))
  infer_instance

/-- **The strict transform of a surjective proper morphism along a blowup in a centre disjoint
from a dense open is surjective.** -/
theorem surjective_strictTransformToBlowUp (f : X ⟶ Y) [IsProper f] [Surjective f]
    (ℐ : Y.IdealSheafData) {U : Y.Opens} (hU : Dense (U : Set Y))
    (h : Disjoint (U : Set Y) (ℐ.support : Set Y)) :
    Surjective (strictTransformToBlowUp f ℐ) := by
  obtain ⟨t, sq⟩ := isPullback_strictTransformToBlowUp_morphismRestrict f ℐ h
  have : Surjective (f ∣_ U) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict f U).flip ‹_›
  have hsurj : Surjective (strictTransformToBlowUp f ℐ ∣_ (blowUpToBase ℐ ⁻¹ᵁ U)) :=
    MorphismProperty.of_isPullback (P := @Surjective) sq ‹_›
  have := isProper_strictTransformToBlowUp f ℐ
  have hclosed : IsClosed (Set.range (strictTransformToBlowUp f ℐ)) :=
    (strictTransformToBlowUp f ℐ).isClosedMap.isClosed_range
  have hsub : ((blowUpToBase ℐ ⁻¹ᵁ U : (blowUp ℐ).Opens) : Set (blowUp ℐ)) ⊆
      Set.range (strictTransformToBlowUp f ℐ) := by
    intro y hy
    obtain ⟨x, hx⟩ := hsurj.surj ⟨y, hy⟩
    exact ⟨x.1, (morphismRestrict_base_coe _ _ x).symm.trans (congrArg Subtype.val hx)⟩
  exact ⟨fun y ↦ closure_minimal hsub hclosed (dense_preimage_blowUpToBase ℐ hU y)⟩

/-- **The strict transform of a proper morphism with geometrically connected fibres, if flat and
of finite presentation, has geometrically connected fibres** (Stacks Tag 0BUI): the number of
geometric connected components of its fibres is lower semicontinuous and is one over the dense
open over which the strict transform is the base change. -/
theorem geometricallyConnected_strictTransformToBlowUp (f : X ⟶ Y) [IsProper f]
    [GeometricallyConnected f] (ℐ : Y.IdealSheafData) {U : Y.Opens} (hU : Dense (U : Set Y))
    (h : Disjoint (U : Set Y) (ℐ.support : Set Y)) [Flat (strictTransformToBlowUp f ℐ)]
    [LocallyOfFinitePresentation (strictTransformToBlowUp f ℐ)] :
    GeometricallyConnected (strictTransformToBlowUp f ℐ) := by
  let f' := strictTransformToBlowUp f ℐ
  let b := blowUpToBase ℐ
  have : IsProper f' := isProper_strictTransformToBlowUp f ℐ
  have hsurj : Surjective f' := surjective_strictTransformToBlowUp f ℐ hU h
  obtain ⟨t, sq⟩ := isPullback_strictTransformToBlowUp_morphismRestrict f ℐ h
  have hf1 : ∀ y : Y, numGeometricConnectedComponents f y = 1 := fun y ↦
    (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one f y).mp
      ((GeometricallyConnected.iff_geometricallyConnected_fiber f).mp ‹_› y)
  have hU1 : ∀ y ∈ ((b ⁻¹ᵁ U : (blowUp ℐ).Opens) : Set (blowUp ℐ)),
      numGeometricConnectedComponents f' y = 1 := by
    intro y hy
    have e1 := numGeometricConnectedComponents_eq_of_isPullback (f ∣_ U) (f' ∣_ (b ⁻¹ᵁ U)) t
      (b.resLE U (b ⁻¹ᵁ U) le_rfl) sq
    have e2 := numGeometricConnectedComponents_eq_of_isPullback f' (f' ∣_ (b ⁻¹ᵁ U))
      (f' ⁻¹ᵁ (b ⁻¹ᵁ U)).ι (b ⁻¹ᵁ U).ι (isPullback_morphismRestrict f' (b ⁻¹ᵁ U)).flip
    have e3 := numGeometricConnectedComponents_eq_of_isPullback f (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι
      (isPullback_morphismRestrict f U).flip
    let y' : (b ⁻¹ᵁ U : (blowUp ℐ).Opens).toScheme := ⟨y, hy⟩
    calc numGeometricConnectedComponents f' y
        = numGeometricConnectedComponents f' ((b ⁻¹ᵁ U).ι y') := rfl
      _ = numGeometricConnectedComponents (f' ∣_ (b ⁻¹ᵁ U)) y' := (congrFun e2 y').symm
      _ = numGeometricConnectedComponents (f ∣_ U) (b.resLE U (b ⁻¹ᵁ U) le_rfl y') :=
          congrFun e1 y'
      _ = numGeometricConnectedComponents f (U.ι (b.resLE U (b ⁻¹ᵁ U) le_rfl y')) :=
          congrFun e3 _
      _ = 1 := hf1 _
  have hopen := lowerSemicontinuous_iff_isOpen_preimage.mp
    (lowerSemicontinuous_numGeometricConnectedComponents f') 1
  refine (GeometricallyConnected.iff_geometricallyConnected_fiber f').mpr fun y ↦
    (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one f' y).mpr ?_
  have hle : numGeometricConnectedComponents f' y ≤ 1 := by
    by_contra hlt
    obtain ⟨z, hz, hzU⟩ := (dense_preimage_blowUpToBase ℐ hU).inter_open_nonempty _ hopen
      ⟨y, lt_of_not_ge hlt⟩
    exact (hz : 1 < numGeometricConnectedComponents f' z).ne' (hU1 z hzU)
  -- at least one: the geometric fibre is nonempty
  have hne : numGeometricConnectedComponents f' y ≠ 0 := by
    obtain ⟨x, rfl⟩ := hsurj.surj y
    let k := (blowUp ℐ).residueField (f' x)
    let K := SeparableClosure k
    have hpt : f'.fiberToSpecResidueField (f' x) (f'.asFiber x) =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) (IsLocalRing.closedPoint K) :=
      Subsingleton.elim _ _
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hpt
    have : Nonempty (_root_.ConnectedComponents (geometricFiber f' (f' x) K)) :=
      ⟨ConnectedComponents.mk z⟩
    intro h0
    exact (ENat.card_eq_zero_iff_empty _).mp h0 |>.false (Classical.arbitrary _)
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

end AlgebraicGeometry

end
