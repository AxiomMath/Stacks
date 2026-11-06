module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Flatness.Applications.FiniteLocallyFreeStrictTransform
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.PuncturedSpectrumModification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CompletionVanishingDescends
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalSurfaceSingularPointsFinite
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CompletionDefinesRationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedModification
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpReduction
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOffExceptional
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.GenericFibrePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.IrreducibleComponentSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic

/-!
# A normal modification of `Spec B` is dominated by one finite over a modification of `Spec A`

Let `A ⟶ B` be a finite injective local homomorphism of local normal Nagata domains of
dimension two. Every normal modification `Y` of `Spec B` is dominated by a normal modification
`Y'` of `Spec B` which is finite and surjective over a normal modification `X'` of `Spec A`,
compatibly with `Spec B ⟶ Spec A`. This is the reduction step of the proof of
[Stacks, Tag 0AXL]; no separability of the fraction field extension is needed for it.

## The argument

Let `U ⊆ Spec A` be the punctured spectrum.

* Over `U` the composite `Y ⟶ Spec B ⟶ Spec A` is finite locally free: the modification
  `Y ⟶ Spec B` is an isomorphism over the punctured spectrum of `B`, which is the inverse image
  of `U`, and `Spec B ⟶ Spec A` is finite and flat over `U`, the local rings of `A` there being
  normal of dimension at most one, hence Dedekind, and `B` being torsion free over them.
* By [Stacks, Tag 0B49] there is a `U`-admissible blowup `X₀ ⟶ Spec A` along which the strict
  transform `T` of `Y` is finite locally free. The flattening input of 0B49, [Stacks, Tag 081R],
  is supplied unconditionally by the Raynaud–Gruson flattening of [Stacks, Tag 0815]
  (`AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre`).
* `T` is integral, being the scheme-theoretic image of an open of the base change which is
  isomorphic to an open of `Y`, and `T ⟶ Y` is proper and birational.
* Normalizing `X₀` and `T` — finite morphisms, by the Nagata property — gives `X'` and `Y'`, with
  `Y' ⟶ X'` finite and surjective by the universal property of the normalization.

## Main results

* `AlgebraicGeometry.isDominatedByFiniteOverBase`

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
* [Stacks Project, Tag 0B49](https://stacks.math.columbia.edu/tag/0B49)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section PuncturedSpectrum

variable (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]

/-- **The punctured spectrum of `B` is the inverse image of the punctured spectrum of `A`** for
an integral local homomorphism `A ⟶ B`: a prime of `B` over the maximal ideal of `A` is
maximal. -/
theorem preimage_puncturedSpectrum_eq [Algebra.IsIntegral A B] [IsLocalHom (algebraMap A B)] :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ Stacks.puncturedSpectrum A =
      Stacks.puncturedSpectrum B := by
  ext x
  change PrimeSpectrum.comap (algebraMap A B) x ≠ IsLocalRing.closedPoint A ↔
    x ≠ IsLocalRing.closedPoint B
  refine not_congr ⟨fun h => ?_, fun h => by rw [h, IsLocalRing.comap_closedPoint]⟩
  have hmax : (PrimeSpectrum.comap (algebraMap A B) x).asIdeal.IsMaximal := by
    rw [h]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have : x.asIdeal.IsPrime := x.isPrime
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) x.asIdeal hmax))

omit [IsLocalRing A] [IsLocalRing B] in
/-- The generic point of the spectrum of a domain maps to the generic point under an injective
ring homomorphism. -/
theorem specMap_mem_genericPoints [IsDomain A] [IsDomain B]
    (hinj : Function.Injective (algebraMap A B)) (η : Spec (.of B))
    (hη : η ∈ genericPoints (Spec (.of B))) :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) η ∈ genericPoints (Spec (.of A)) := by
  have : IsDomain (CommRingCat.of A) := ‹IsDomain A›
  have : IsDomain (CommRingCat.of B) := ‹IsDomain B›
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hη
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff, hη,
    genericPoint_eq_bot_of_affine (.of B), genericPoint_eq_bot_of_affine (.of A)]
  change PrimeSpectrum.comap (algebraMap A B) ⊥ = _
  ext1
  change Ideal.comap (algebraMap A B) ⊥ = ⊥
  exact (RingHom.injective_iff_ker_eq_bot _).mp hinj

omit [IsLocalRing B] in
/-- **`Spec B ⟶ Spec A` is flat over the punctured spectrum** for a finite injective local map
of local domains of dimension at most two with `A` normal and Noetherian: at a point over the
punctured spectrum the local ring of `A` is normal of dimension at most one. -/
theorem flat_specMap_morphismRestrict_puncturedSpectrum [IsDomain A] [IsDomain B]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [Algebra.IsIntegral A B]
    [IsLocalHom (algebraMap A B)] (hinj : Function.Injective (algebraMap A B))
    (hdimA : ringKrullDim A ≤ 2) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_ Stacks.puncturedSpectrum A) := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : IsNormal (Spec (.of A)) := isNormal_spec_of_isIntegrallyClosed A
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have hφ : ∀ x : Spec (.of B), φ x ∈ Stacks.puncturedSpectrum A → (φ.stalkMap x).hom.Flat :=
    fun x hx => flat_stalkMap_of_ringKrullDim_le_one_of_genericPoints φ x
      (ringKrullDim_stalk_le_one_of_ne_closedPoint (.of A) hdimA (φ x) hx)
      (specMap_mem_genericPoints A B hinj)
  rw [Flat.iff_flat_stalkMap]
  intro x
  have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Flat.respectsIso
  exact ((RingHom.toMorphismProperty RingHom.Flat).arrow_mk_iso_iff
    (morphismRestrictStalkMap φ _ x)).mpr (hφ x.1 x.2)

/-- A morphism-property holds for the base change along `U.ι` iff it holds for the restriction
over `U`, when the property respects isomorphisms. -/
private theorem pullback_snd_iff_morphismRestrict (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) :
    P (pullback.snd f U.ι) ↔ P (f ∣_ U) := by
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f U]
  exact P.cancel_left_of_respectsIso _ _

/-- **The composite `Y ⟶ Spec B ⟶ Spec A` is finite locally free over the punctured spectrum**
for a modification `Y` of `Spec B`, `A ⟶ B` a finite injective local map of two-dimensional
local Noetherian normal domains: the modification is an isomorphism over the punctured spectrum of
`B`, the inverse image of that of `A`, over which `Spec B ⟶ Spec A` is finite and flat. -/
theorem isFiniteLocallyFree_pullback_snd_puncturedSpectrum [IsNormalDomain A] [IsNormalDomain B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B] [FaithfulSMul A B]
    [IsLocalHom (algebraMap A B)] (hdimA : ringKrullDim A = 2) (hdimB : ringKrullDim B = 2)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of B)) (hg : IsModification g) :
    Stacks.Morphisms.IsFiniteLocallyFree
      (pullback.snd (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Stacks.puncturedSpectrum A).ι) := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let U := Stacks.puncturedSpectrum A
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have hiso : IsIso (g ∣_ (φ ⁻¹ᵁ U)) := by
    change IsIso (g ∣_ (φ ⁻¹ᵁ Stacks.puncturedSpectrum A))
    rw [preimage_puncturedSpectrum_eq]
    exact isIso_morphismRestrict_puncturedSpectrum_of_isModification B hdimB g hg
  have : IsFinite φ := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : MorphismProperty.RespectsIso @IsFinite :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have key : ∀ (P : MorphismProperty Scheme.{u}) [P.RespectsIso], P (φ ∣_ U) →
      P (pullback.snd (g ≫ φ) U.ι) := by
    intro P _ h
    have h1 : P (g ∣_ (φ ⁻¹ᵁ U) ≫ φ ∣_ U) := (P.cancel_left_of_respectsIso _ _).mpr h
    rw [← morphismRestrict_comp] at h1
    exact (pullback_snd_iff_morphismRestrict P _ U).mpr h1
  rw [Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian]
  exact ⟨key @IsFinite inferInstance, key @Flat <|
    flat_specMap_morphismRestrict_puncturedSpectrum A B (FaithfulSMul.algebraMap_injective A B)
      hdimA.le⟩

/-- **[Stacks, Tag 0B49] for `Y ⟶ Spec B ⟶ Spec A`, unconditionally.** There is an admissible
blowup of `Spec A` with centre off the punctured spectrum along which the strict transform of a
modification `Y` of `Spec B` is finite locally free. The flattening input [Stacks, Tag 081R] of
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform` is supplied by
`AlgebraicGeometry.finitePresentationHasAffineChartFlatteningCentre` through
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform`; local finite presentation of
the strict transform holds because the blowup of the Noetherian `Spec A` is locally Noetherian. -/
theorem exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_puncturedSpectrum
    [IsNormalDomain A] [IsNormalDomain B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Finite A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]
    (hdimA : ringKrullDim A = 2) (hdimB : ringKrullDim B = 2)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of B)) (hg : IsModification g) :
    ∃ J : (Spec (.of A)).IdealSheafData,
      Stacks.Blowup.IsAdmissibleBlowup (Stacks.puncturedSpectrum A) (blowUpToBase J) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          (strictTransformToBlowUp (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) J) := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let h := g ≫ φ
  let U := Stacks.puncturedSpectrum A
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsProper g := hg.isProper
  have : IsFinite φ := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsProper h := inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h
  have hUc : IsCompact (U : Set (Spec (.of A))) := NoetherianSpace.isCompact _
  have hflf := isFiniteLocallyFree_pullback_snd_puncturedSpectrum A B hdimA hdimB g hg
  have : LocallyOfFinitePresentation h :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hflatU : Flat (h.resLE U (h ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    have hfl : Flat (pullback.snd h U.ι) :=
      ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian _).mp
        hflf).2
    exact (pullback_snd_iff_morphismRestrict @Flat h U).mp hfl
  obtain ⟨I, hIfp, hdisj, -, hflat⟩ := exists_isAdmissibleBlowup_flat_strictTransform h U hUc
    (finitePresentationHasAffineChartFlatteningCentre h U hUc hflatU)
  have : IsLocallyNoetherian (blowUp I) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase I)
  have : LocallyOfFinitePresentation (strictTransformToBlowUp h I) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  exact exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform h U hUc
    ⟨I, hIfp, hdisj, hflat, inferInstance⟩

/-! ### Base change of an isomorphism over an open -/

/-- **A base change is an isomorphism over the inverse image of an open over which the original
morphism is one.** The first projection of `X ×_S T` restricted over `f⁻¹(W)` is the base change
of `g` restricted over `W`. -/
theorem isIso_morphismRestrict_pullback_fst {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (W : S.Opens) [IsIso (g ∣_ W)] : IsIso (pullback.fst f g ∣_ (f ⁻¹ᵁ W)) := by
  have hW : IsIso (pullback.snd g W.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict g W]
    infer_instance
  have hbig₁ : IsPullback
      (pullback.fst (pullback.snd g W.ι) (f ∣_ W) ≫ pullback.fst g W.ι)
      (pullback.snd (pullback.snd g W.ι) (f ∣_ W)) g ((f ⁻¹ᵁ W).ι ≫ f) := by
    simpa only [morphismRestrict_ι] using
      (IsPullback.of_hasPullback (pullback.snd g W.ι) (f ∣_ W)).paste_horiz
        (IsPullback.of_hasPullback g W.ι)
  have hbig₂ := (isPullback_morphismRestrict (pullback.fst f g) (f ⁻¹ᵁ W)).paste_vert
    (IsPullback.of_hasPullback f g)
  have h₁ : IsIso (pullback.snd g ((f ⁻¹ᵁ W).ι ≫ f)) := by
    have he : pullback.snd g ((f ⁻¹ᵁ W).ι ≫ f) =
        hbig₁.isoPullback.inv ≫ pullback.snd (pullback.snd g W.ι) (f ∣_ W) := by
      rw [← cancel_epi hbig₁.isoPullback.hom, hbig₁.isoPullback_hom_snd, Iso.hom_inv_id_assoc]
    rw [he]
    infer_instance
  have he₂ : pullback.fst f g ∣_ (f ⁻¹ᵁ W) =
      hbig₂.flip.isoPullback.hom ≫ pullback.snd g ((f ⁻¹ᵁ W).ι ≫ f) :=
    hbig₂.flip.isoPullback_hom_snd.symm
  rw [he₂]
  infer_instance

end PuncturedSpectrum

section StrictTransform

variable (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsNormalDomain A] [IsNormalDomain B] [IsNoetherianRing A] [IsNoetherianRing B]
  [Module.Finite A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]

variable {A B}

/-- Over the complement `W` of the centre of a blowup, the inverse image of `h⁻¹(W)` in the base
change is the complement of the exceptional divisor. -/
theorem preimage_pullback_fst_preimage_compl_support {X Y : Scheme.{u}} (h : Y ⟶ X)
    (J : X.IdealSheafData) :
    pullback.fst h (blowUpToBase J) ⁻¹ᵁ (h ⁻¹ᵁ ⟨J.supportᶜ, J.support.isClosed.isOpen_compl⟩) =
      Stacks.StrictTransform.exceptionalComplement h (blowUpToBase J) (exceptionalIdeal J) := by
  let b := blowUpToBase J
  let E := exceptionalIdeal J
  let W : X.Opens := ⟨J.supportᶜ, J.support.isClosed.isOpen_compl⟩
  ext x
  change h (pullback.fst h b x) ∈ W ↔ pullback.snd h b x ∈ (E.support.compl : Set _)
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  change b (pullback.snd h b x) ∉ J.support ↔ pullback.snd h b x ∉ E.support
  rw [show E = J.comap b from rfl, Scheme.IdealSheafData.support_comap]
  rfl

/-- `Spec B ⟶ Spec A` maps the generic point to the generic point. -/
private theorem specMap_genericPoint {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B] [FaithfulSMul A B] :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) (genericPoint (Spec (.of B))) =
      genericPoint (Spec (.of A)) := by
  have hφ := specMap_mem_genericPoints A B (FaithfulSMul.algebraMap_injective A B)
    (genericPoint (Spec (.of B))) (by rw [genericPoints_eq_singleton]; rfl)
  rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hφ

omit [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]
    [IsLocalRing A] [IsLocalRing B] in
/-- The generic point of a modification `Y` of `Spec B` lies over the complement of the centre of
a nonzero ideal sheaf on `Spec A`. -/
theorem genericPoint_mem_preimage_compl_support {Y : Scheme.{u}} [IsIntegral Y]
    (g : Y ⟶ Spec (.of B)) (hg : IsModification g) (J : (Spec (.of A)).IdealSheafData)
    (hJ : J ≠ ⊥) :
    genericPoint Y ∈ (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ
      ⟨J.supportᶜ, J.support.isClosed.isOpen_compl⟩ := by
  change (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (genericPoint Y) ∉ J.supportSet
  rw [Scheme.Hom.comp_apply, IsBirational.genericPoint_eq g hg.isBirational, specMap_genericPoint]
  exact genericPoint_notMem_supportSet J hJ

omit [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]
    [IsLocalRing A] [IsLocalRing B] in
/-- **The strict transform of a modification of `Spec B` along a blowup of `Spec A` is
integral**: it is the scheme-theoretic image of the complement of the exceptional divisor, which
is isomorphic to a nonempty open of the integral `Y`. -/
theorem isIntegral_strictTransform_specMap {Y : Scheme.{u}} [IsIntegral Y]
    (g : Y ⟶ Spec (.of B)) (hg : IsModification g) (J : (Spec (.of A)).IdealSheafData)
    (hJ : J ≠ ⊥) :
    IsIntegral (Stacks.StrictTransform.scheme (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (blowUpToBase J) (exceptionalIdeal J)) := by
  let h := g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))
  let b := blowUpToBase J
  let E := exceptionalIdeal J
  let W : (Spec (.of A)).Opens := ⟨J.supportᶜ, J.support.isClosed.isOpen_compl⟩
  let V := Stacks.StrictTransform.exceptionalComplement h b E
  have : IsIso (b ∣_ W) := isIso_blowUp_restrict_compl_support J
  have : IsIso (pullback.fst h b ∣_ (h ⁻¹ᵁ W)) := isIso_morphismRestrict_pullback_fst h b W
  have hVeq : pullback.fst h b ⁻¹ᵁ (h ⁻¹ᵁ W) = V := preimage_pullback_fst_preimage_compl_support h J
  have : Nonempty (h ⁻¹ᵁ W).toScheme := ⟨⟨_, genericPoint_mem_preimage_compl_support g hg J hJ⟩⟩
  have : IsIntegral (h ⁻¹ᵁ W).toScheme := isIntegral_of_isOpenImmersion (h ⁻¹ᵁ W).ι
  have : IsIntegral V.toScheme :=
    hVeq ▸ IsIntegral.of_isIso (asIso (pullback.fst h b ∣_ (h ⁻¹ᵁ W))).inv
  have hVirr : IsIrreducible (Set.range V.ι.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ V.toScheme).image V.ι.base
      V.ι.continuous.continuousOn
  have hker := Stacks.StrictTransform.ideal_eq_ker_ι h b E
  change IsIntegral (Stacks.StrictTransform.ideal h b E).subscheme
  have hred : IsReduced (Stacks.StrictTransform.ideal h b E).subscheme := by
    rw [hker]
    exact Scheme.Hom.isReduced_image V.ι
  have hirr : IrreducibleSpace (Stacks.StrictTransform.ideal h b E).subscheme := by
    refine Stacks.Chow.irreducibleSpace_subscheme_of_isIrreducible _ ?_
    rw [hker, Scheme.Hom.support_ker_eq_closure_range, Closeds.coe_closure]
    exact hVirr.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

omit [IsNoetherianRing B] [Module.Finite A B] [IsLocalHom (algebraMap A B)] [IsLocalRing A]
    [IsLocalRing B] in
/-- **The strict transform of a modification of `Spec B` along a blowup of `Spec A` is a
modification of `Y`**: it maps isomorphically onto the inverse image in `Y` of the complement of
the centre, which contains the generic point of `Y`. -/
theorem isModification_strictTransform_specMap {Y : Scheme.{u}} [IsIntegral Y]
    (g : Y ⟶ Spec (.of B)) (hg : IsModification g) (J : (Spec (.of A)).IdealSheafData)
    (hJ : J ≠ ⊥) :
    IsModification ((Stacks.StrictTransform.ideal (g ≫ Spec.map (CommRingCat.ofHom
        (algebraMap A B))) (blowUpToBase J) (exceptionalIdeal J)).subschemeι ≫
      pullback.fst (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (blowUpToBase J)) := by
  let h := g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))
  let b := blowUpToBase J
  let E := exceptionalIdeal J
  let W : (Spec (.of A)).Opens := ⟨J.supportᶜ, J.support.isClosed.isOpen_compl⟩
  let ι := (Stacks.StrictTransform.ideal h b E).subschemeι
  let V' := pullback.fst h b ⁻¹ᵁ (h ⁻¹ᵁ W)
  have : IsIso (b ∣_ W) := isIso_blowUp_restrict_compl_support J
  have hfstiso : IsIso (pullback.fst h b ∣_ (h ⁻¹ᵁ W)) := isIso_morphismRestrict_pullback_fst h b W
  have hgenY : genericPoint Y ∈ h ⁻¹ᵁ W := genericPoint_mem_preimage_compl_support g hg J hJ
  have : IsIntegral (Stacks.StrictTransform.scheme h b E) :=
    isIntegral_strictTransform_specMap g hg J hJ
  have hιiso : IsIso (ι ∣_ V') :=
    Stacks.StrictTransform.isIso_subschemeι_restrict h b E
      (preimage_pullback_fst_preimage_compl_support h J).le
  have hσiso : IsIso ((ι ≫ pullback.fst h b) ∣_ (h ⁻¹ᵁ W)) := by
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' hιiso hfstiso
  have hgenT : ∀ x ∈ genericPoints (Stacks.StrictTransform.scheme h b E),
      (ι ≫ pullback.fst h b) x ∈ h ⁻¹ᵁ W := by
    intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    obtain ⟨w, -⟩ := (ConcreteCategory.bijective_of_isIso (ι ∣_ V').base).2
      ((asIso (pullback.fst h b ∣_ (h ⁻¹ᵁ W))).inv ⟨genericPoint Y, hgenY⟩)
    exact show genericPoint (Stacks.StrictTransform.scheme h b E) ∈ ι ⁻¹ᵁ V' from
      ((genericPoint_spec _).mem_open_set_iff (ι ⁻¹ᵁ V').isOpen).mpr ⟨w.1, trivial, w.2⟩
  have hgenY' : ∀ y ∈ genericPoints Y, y ∈ h ⁻¹ᵁ W := fun y hy => by
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hy
    exact hy ▸ hgenY
  exact ⟨isBirational_of_isIso_morphismRestrict _ (h ⁻¹ᵁ W) hσiso hgenT hgenY',
    inferInstance, ‹_›⟩

omit [IsNoetherianRing B] [Module.Finite A B] [IsLocalHom (algebraMap A B)] [IsLocalRing A]
    [IsLocalRing B] in
/-- **The strict transform of a modification of `Spec B` along an admissible blowup of `Spec A`
is integral, and properly and birationally over the modification.** Write `W ⊆ Spec A` for the
complement of the centre. Over `W` the blowup is an isomorphism, so the open of the base change
off the exceptional divisor is isomorphic, through the first projection, to the inverse image
`Y_W` of `W` in `Y`: a nonempty open of the integral `Y`. The strict transform is the
scheme-theoretic image of that reduced irreducible open, hence integral, and it maps
isomorphically onto `Y_W`, which contains the generic point of `Y`. -/
theorem isIntegral_strictTransform_and_isModification
    {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ Spec (.of B)) (hg : IsModification g)
    (J : (Spec (.of A)).IdealSheafData) (hJ : J ≠ ⊥) :
    IsIntegral (Stacks.StrictTransform.scheme (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (blowUpToBase J) (exceptionalIdeal J)) ∧
      IsModification ((Stacks.StrictTransform.ideal (g ≫ Spec.map (CommRingCat.ofHom
          (algebraMap A B))) (blowUpToBase J) (exceptionalIdeal J)).subschemeι ≫
        pullback.fst (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (blowUpToBase J)) :=
  ⟨isIntegral_strictTransform_specMap g hg J hJ, isModification_strictTransform_specMap g hg J hJ⟩

omit [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B] [IsLocalHom (algebraMap A B)]
    [IsLocalRing A] [IsLocalRing B] in
/-- The generic point of a modification `Y` of `Spec B` maps to the generic point of `Spec A`
under `Y ⟶ Spec B ⟶ Spec A`. -/
theorem comp_specMap_genericPoint {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ Spec (.of B))
    (hg : IsModification g) :
    (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (genericPoint Y) =
      genericPoint (Spec (.of A)) := by
  rw [Scheme.Hom.comp_apply, IsBirational.genericPoint_eq g hg.isBirational, specMap_genericPoint]

/-- The centre of an admissible blowup of an integral scheme is nonzero as soon as the blowup is
nonempty: every point of the blowup lies on a chart at a nonzero section of the centre. -/
theorem ne_bot_of_nonempty_blowUp {X : Scheme.{u}} (J : X.IdealSheafData) [Nonempty (blowUp J)] :
    J ≠ ⊥ := by
  rintro rfl
  obtain ⟨x⟩ := ‹Nonempty (blowUp (⊥ : X.IdealSheafData))›
  obtain ⟨W, a, ha, -⟩ := exists_ne_zero_mem_range_blowUpAffineChart (⊥ : X.IdealSheafData) x
  exact ha a.2

end StrictTransform

/-! ### Normalizing a square with a finite side -/

/-- A morphism which is an isomorphism over an open `U` is injective on the points over `U`. -/
theorem eq_of_apply_eq_of_isIso_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    [IsIso (f ∣_ U)] {x y : X} (hx : f x ∈ U) (hxy : f x = f y) : x = y := by
  have key : (⟨x, hx⟩ : (f ⁻¹ᵁ U).toScheme) =
      ⟨y, show f y ∈ U from hxy ▸ hx⟩ := by
    apply (ConcreteCategory.bijective_of_isIso (f ∣_ U).base).1
    apply Subtype.ext
    calc _ = f x := morphismRestrict_base_coe f U ⟨x, hx⟩
      _ = f y := hxy
      _ = _ := (morphismRestrict_base_coe f U ⟨y, show f y ∈ U from hxy ▸ hx⟩).symm
  exact congrArg Subtype.val key

/-- **A finite morphism of integral schemes preserving generic points lifts to a finite dominant
morphism between the normalizations.** -/
theorem exists_isFinite_isDominant_lift_normalization {T X : Scheme.{u}} [IsIntegral T]
    [IsIntegral X] (hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    [IsFinite (T.normalization hT)] [IsFinite (X.normalization hX)]
    [IsIntegral (T.normalizationScheme hT)] [IsIntegral (X.normalizationScheme hX)]
    (t : T ⟶ X) [IsFinite t] (ht : t (genericPoint T) = genericPoint X) :
    ∃ π : T.normalizationScheme hT ⟶ X.normalizationScheme hX,
      π ≫ X.normalization hX = T.normalization hT ≫ t ∧ IsFinite π ∧ IsDominant π := by
  let νX := X.normalization hX
  let νT := T.normalization hT
  have : IsNormal (T.normalizationScheme hT) := Scheme.isNormal_normalizationScheme T hT
  have hgen : ∀ η : genericPoints (T.normalizationScheme hT), (νT ≫ t) η.1 ∈ genericPoints X := by
    rintro ⟨η, hη⟩
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hη
    subst hη
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff]
    change t (νT (genericPoint _)) = _
    rw [IsBirational.genericPoint_eq νT (Scheme.isBirational_normalization T hT), ht]
  obtain ⟨π, hπ, -⟩ := Scheme.existsUnique_lift_normalization hX (νT ≫ t) hgen
  have hπfin : IsFinite π := by
    have hc : IsFinite (π ≫ νX) := by
      rw [hπ]
      infer_instance
    exact MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) π νX inferInstance hc
  have hx : νX (π (genericPoint _)) = νX (genericPoint _) := by
    rw [← Scheme.Hom.comp_apply, hπ, Scheme.Hom.comp_apply,
      IsBirational.genericPoint_eq νT (Scheme.isBirational_normalization T hT), ht,
      IsBirational.genericPoint_eq νX (Scheme.isBirational_normalization X hX)]
  exact ⟨π, hπ, hπfin, ((tfae_isDominant_of_isIntegral π).out 2 1).mp
    (eq_of_specializes_of_base_eq_of_isIntegralHom νX
      (genericPoint_specializes (π (genericPoint _))) hx.symm).symm⟩

/-- **Normalizing a square with a finite side.** Let `X ⟶ Spec A` and `T ⟶ Spec B` be
modifications, `A` and `B` Nagata domains, and `T ⟶ X` finite and preserving generic points.
The normalizations of `X` and `T` are normal modifications of `Spec A` and `Spec B`, and the
normalization of `T` is finite and surjective over that of `X`, compatibly with `T ⟶ X`. -/
theorem exists_normalization_finite_surjective (A B : Type u) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (hA : IsNagataRing A) (hB : IsNagataRing B) {T X : Scheme.{u}}
    [IsIntegral T] [IsIntegral X] (b : X ⟶ Spec (.of A)) (hb : IsModification b)
    (c : T ⟶ Spec (.of B)) (hc : IsModification c) (t : T ⟶ X) [IsFinite t]
    (ht : t (genericPoint T) = genericPoint X) :
    ∃ (T' X' : Scheme.{u}) (νT : T' ⟶ T) (νX : X' ⟶ X) (π : T' ⟶ X'),
      IsNormal T' ∧ IsNormal X' ∧ IsModification (νT ≫ c) ∧ IsModification (νX ≫ b) ∧
        IsFinite π ∧ Surjective π ∧ π ≫ νX = νT ≫ t := by
  have : IsProper b := hb.isProper
  have : IsProper c := hc.isProper
  have hNX := isNagataScheme_of_locallyOfFiniteType b (isNagataScheme_spec_of_isNagataRing A hA)
  have hNT := isNagataScheme_of_locallyOfFiniteType c (isNagataScheme_spec_of_isNagataRing B hB)
  have hfinX :=
    Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme X hNX
  have hfinT :=
    Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme T hNT
  have : IsFinite (X.normalization hfinX) := Scheme.isFinite_normalization hNX hfinX
  have : IsFinite (T.normalization hfinT) := Scheme.isFinite_normalization hNT hfinT
  have hb' := isModification_normalization_comp A hA b hb hfinX
  have hc' := isModification_normalization_comp B hB c hc hfinT
  have : IsIntegral (X.normalizationScheme hfinX) := hb'.source_isIntegral
  have : IsIntegral (T.normalizationScheme hfinT) := hc'.source_isIntegral
  obtain ⟨π, hπ, hπfin, hπdom⟩ := exists_isFinite_isDominant_lift_normalization hfinT hfinX t ht
  exact ⟨_, _, _, _, π, Scheme.isNormal_normalizationScheme T hfinT,
    Scheme.isNormal_normalizationScheme X hfinX, hc', hb', hπfin,
    Surjective.of_universallyClosed_of_isDominant π, hπ⟩

/-! ### The reduction step -/

/-- **The reduction step of [Stacks, Tag 0AXL].** Let `A ⟶ B` be a finite injective local
homomorphism of local normal Nagata domains of dimension two. Then every normal modification `Y`
of `Spec B` is dominated by a normal modification `Y'` of `Spec B` which is finite and
surjective over a normal modification `X'` of `Spec A`, compatibly with `Spec B ⟶ Spec A`.
Separability of the fraction field extension is not needed. -/
theorem isDominatedByFiniteOverBase (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    [CommRing B] [IsLocalRing B] [IsNormalDomain B] [Algebra A B] [Module.Finite A B]
    [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] (hA : IsNagataRing A) (hB : IsNagataRing B)
    (hdimA : ringKrullDim A = 2) (hdimB : ringKrullDim B = 2) :
    SeparableGoUp.IsDominatedByFiniteOverBase A B := by
  intro Y _ g hg
  have : IsNoetherianRing A := hA.isNoetherianRing
  have : IsNoetherianRing B := hB.isNoetherianRing
  have : IsIntegral Y := hg.source_isIntegral
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  let h := g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))
  obtain ⟨J, hJadm, hJflf⟩ :=
    exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_puncturedSpectrum A B hdimA
      hdimB g hg
  let b := blowUpToBase J
  have hbmod : IsModification b :=
    isModification_of_isAdmissibleBlowup_puncturedSpectrum A (by norm_num [hdimA]) hJadm
  have : IsIntegral (blowUp J) := hbmod.source_isIntegral
  have hJne : J ≠ ⊥ := ne_bot_of_nonempty_blowUp J
  obtain ⟨hTint, hsmod⟩ := isIntegral_strictTransform_and_isModification g hg J hJne
  let E := exceptionalIdeal J
  let T := Stacks.StrictTransform.scheme h b E
  let ι := (Stacks.StrictTransform.ideal h b E).subschemeι
  let s : T ⟶ Y := ι ≫ pullback.fst h b
  let t : T ⟶ blowUp J := strictTransformToBlowUp h J
  have : IsIntegral T := hTint
  have : IsLocallyNoetherian (blowUp J) := LocallyOfFiniteType.isLocallyNoetherian b
  have : IsFinite t :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian t).mp
      hJflf).1
  have hts : t ≫ b = s ≫ h := by
    change (ι ≫ pullback.snd h b) ≫ b = (ι ≫ pullback.fst h b) ≫ h
    rw [Category.assoc, Category.assoc, pullback.condition]
  let W : (Spec (.of A)).Opens := ⟨J.supportᶜ, J.support.isClosed.isOpen_compl⟩
  have : IsIso (b ∣_ W) := isIso_blowUp_restrict_compl_support J
  have hξA : genericPoint (Spec (.of A)) ∈ W := genericPoint_notMem_supportSet J hJne
  have h1 : b (t (genericPoint T)) = genericPoint (Spec (.of A)) := by
    rw [← Scheme.Hom.comp_apply, hts, Scheme.Hom.comp_apply,
      IsBirational.genericPoint_eq s hsmod.isBirational]
    exact comp_specMap_genericPoint g hg
  have htgen : t (genericPoint T) = genericPoint (blowUp J) :=
    eq_of_apply_eq_of_isIso_morphismRestrict b W (x := t (genericPoint T)) (h1 ▸ hξA)
      (h1.trans (IsBirational.genericPoint_eq b hbmod.isBirational).symm)
  obtain ⟨T', X', νT, νX, π, hT', hX', hg', hf', hπfin, hπsurj, hπ⟩ :=
    exists_normalization_finite_surjective A B hA hB b hbmod (s ≫ g) (hsmod.comp hg) t htgen
  refine ⟨T', X', νT ≫ s ≫ g, νX ≫ b, π, νT ≫ s, hT', hX', hg', hf', hπfin, hπsurj, ?_,
    Category.assoc _ _ _⟩
  rw [← Category.assoc, hπ, Category.assoc, hts]
  rfl

end AlgebraicGeometry

end
