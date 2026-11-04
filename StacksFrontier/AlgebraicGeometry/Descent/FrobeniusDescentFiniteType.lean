module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.ReducedCover
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleSurjective
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitClosedCoverGlue
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectProperCoverDescent
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseFlatLocus
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentFlattening
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentStein

/-!
# The essential-image half of Stacks Tag 0EXH over a base of finite type over a field

This file assembles the finite-type case of the essential-image half of Stacks Tag 0EXH, following
the source:

* `X` may be replaced by its reduction (pullback to `X_red` is fully faithful on `colim_F Vect`);
* `Y` may be replaced by the base `S` of the Stein factorization `X ⟶ S ⟶ Y`
  (`AlgebraicGeometry.descendsAfterFrobenius_of_toNormalization`), after which `f_*𝒪_X = 𝒪_S`
  and `S` is reduced;
* a flat family with `f_*𝒪 = 𝒪` over a dense open is handled through the normalization of the
  base (`AlgebraicGeometry.descendsAfterFrobenius_of_flat`);
* in general the family is flattened by a blowup, the strict transform is flat, and the descent on
  the blowup is glued from the strict transform and the part over the non-flat locus, which is
  treated by Noetherian induction on its image in a fixed ambient scheme.

Every replacement of the base is a descent along a proper surjective morphism of finite
presentation, through the h-descent of Stacks Tag 0EXE
(`AlgebraicGeometry.mem_essImage_of_mem_essImage_baseChange`).

## Main results

* `AlgebraicGeometry.descendsAfterFrobenius_of_flat`.
* `AlgebraicGeometry.descendsAfterFrobenius_of_reduction`.
* `AlgebraicGeometry.descendsAfterFrobenius_of_toNormalization`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : ℕ} [Fact p.Prime]

/-- A quasi-compact scheme locally of finite type over a field is Noetherian. -/
private theorem isNoetherian_of_compactSpace_over_field {k : Type u} [Field k] {Z : Scheme.{u}}
    (s : Z ⟶ Spec (.of k)) [LocallyOfFiniteType s] [CompactSpace Z] : IsNoetherian Z :=
  have := LocallyOfFiniteType.isLocallyNoetherian s
  {}

/-- Over a locally Noetherian target, locally of finite type implies locally of finite
presentation. -/
private theorem locallyOfFinitePresentation_of_locallyOfFiniteType {Z W : Scheme.{u}} {g : Z ⟶ W}
    [IsLocallyNoetherian W] [LocallyOfFiniteType g] : LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance

/-- `f_*𝒪 = 𝒪` restricts to every open of the base. -/
private theorem isIso_c_morphismRestrict_of_isIso_c (f : X ⟶ Y) [IsIso f.c] (U : Y.Opens) :
    IsIso (f ∣_ U).c :=
  (isIso_c_morphismRestrict_iff f U).mpr fun W _ ↦ NatIso.isIso_app_of_isIso f.c (Opposite.op W)

/-- **The conclusion of Stacks Tag 0EXH descends along a proper surjective morphism of finite
presentation of the base**: this is the h-descent of Stacks Tag 0EXE
(`AlgebraicGeometry.mem_essImage_of_mem_essImage_baseChange`), read through
`AlgebraicGeometry.mem_essImage_frobeniusColimitVectModelPullback_iff`. -/
theorem descendsAfterFrobenius_of_baseChange {Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [GeometricallyConnected f]
    [IsProper g] [Surjective g] [LocallyOfFinitePresentation g]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (E : X.Vect)
    (h : Scheme.Vect.DescendsAfterFrobenius (pullback.snd f g) p
      (isInCharacteristic_of_hom (pullback.fst f g) p hX)
      ((Scheme.Vect.pullback (pullback.fst f g)).obj E)) :
    Scheme.Vect.DescendsAfterFrobenius f p hX E := by
  have hX' := isInCharacteristic_of_hom (pullback.fst f g) p hX
  have hY' := isInCharacteristic_of_hom g p hY
  have hmem := (mem_essImage_frobeniusColimitVectModelPullback_iff (pullback.snd f g) p hX' hY'
    ((frobeniusColimitVectModelPullback (pullback.fst f g) p hX' hX).obj ⟨E, 0⟩)).mpr h
  exact (mem_essImage_frobeniusColimitVectModelPullback_iff f p hX hY ⟨E, 0⟩).mp
    (mem_essImage_of_mem_essImage_baseChange (IsPullback.of_hasPullback f g) p hX hY hX' hY'
      ⟨E, 0⟩ hmem)

/-- **The essential-image half of Stacks Tag 0EXH for a flat family over a reduced base of finite
type over a field, with `f_*𝒪 = 𝒪` over a dense open.** The base is replaced by its
normalization. -/
theorem descendsAfterFrobenius_of_flat (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] [CompactSpace Y] [IsReduced Y] (f : X ⟶ Y) [Flat f] [IsProper f]
    [GeometricallyConnected f] (V : Y.Opens) (hV : Dense (V : Set Y)) (hfV : IsIso (f ∣_ V).c)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (E : X.Vect)
    (hE : Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius f p hX E) :
    Scheme.Vect.DescendsAfterFrobenius f p hX E := by
  have : IsNoetherian Y := isNoetherian_of_compactSpace_over_field s
  let ν := normalizationOverField k s
  have : IsFinite ν := isFinite_normalizationOverField k s
  have : LocallyOfFinitePresentation ν := locallyOfFinitePresentation_of_locallyOfFiniteType
  have : Surjective ν := Scheme.surjective_normalization Y _
  exact descendsAfterFrobenius_of_baseChange f ν hX hY E
    (descendsAfterFrobenius_normalization_pullback k s f V hV hfV hX E hE)

/-- **The conclusion of Stacks Tag 0EXH descends from the reduction of the source.** -/
theorem descendsAfterFrobenius_of_reduction (f : X ⟶ Y) [IsNoetherian X]
    (hX : IsInCharacteristic X p) (hXr : IsInCharacteristic X.reduction p)
    (hY : IsInCharacteristic Y p) (E : X.Vect)
    (h : Scheme.Vect.DescendsAfterFrobenius (X.reductionι ≫ f) p hXr
      ((Scheme.Vect.pullback X.reductionι).obj E)) :
    Scheme.Vect.DescendsAfterFrobenius f p hX E := by
  have := frobeniusColimitVectModelPullback_isEquivalence_reductionι p hX hXr
  exact Scheme.Vect.DescendsAfterFrobenius.of_comp f X.reductionι hX hXr hY
    ⟨inferInstance, inferInstance⟩ h

/-- **The conclusion of Stacks Tag 0EXH descends from the first factor of the Stein
factorization.** -/
theorem descendsAfterFrobenius_of_toNormalization (f : X ⟶ Y) [IsProper f]
    [GeometricallyConnected f] [IsLocallyNoetherian Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) (E : X.Vect)
    (h : Scheme.Vect.DescendsAfterFrobenius f.toNormalization p hX E) :
    Scheme.Vect.DescendsAfterFrobenius f p hX E := by
  have : IsFinite f.fromNormalization := Stacks.SteinFactorization.isFinite_fromNormalization f
  have : LocallyOfFinitePresentation f.fromNormalization :=
    locallyOfFinitePresentation_of_locallyOfFiniteType
  have : Surjective (f.toNormalization ≫ f.fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  have : Surjective f.fromNormalization := Surjective.of_comp f.toNormalization _
  exact descendsAfterFrobenius_of_baseChange f f.fromNormalization hX hY E
    (descendsAfterFrobenius_pullback_fromNormalization f hX hY E h)

/-- The reduced closed subscheme of `Y` supported on the complement of an open `U`. -/
abbrev complementIdeal (U : Y.Opens) : Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩

/-- **The flattening step of the essential-image half of Stacks Tag 0EXH.** Let `Y` be reduced,
quasi-compact and locally of finite type over a field, `f : X ⟶ Y` proper with geometrically
connected fibres and `f_*𝒪_X = 𝒪_Y`, flat and locally of finite presentation over a dense open
`U`. If the conclusion of Stacks Tag 0EXH holds for the base change of `f` to the reduced closed
subscheme `Z` on the complement of `U`, then it holds for `f`. The base is blown up so that the
strict transform becomes flat (Stacks Tag 081R); the flat case applies to the strict transform,
the hypothesis to the part of the total transform over the inverse image of `Z`, and the two
descents are glued over the total transform (`AlgebraicGeometry.mem_essImage_of_closedCover`)
and descended along the blowup. -/
theorem descendsAfterFrobenius_of_flattening (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] [CompactSpace Y] [IsReduced Y] (f : X ⟶ Y) [IsProper f]
    [GeometricallyConnected f] (hO : IsIso f.c) (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) (E : X.Vect)
    (hE : Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius f p hX E) (U : Y.Opens)
    (hU : Dense (U : Set Y)) (hflat : Flat (f ∣_ U)) (hfp : LocallyOfFinitePresentation (f ∣_ U))
    (hZ : Scheme.Vect.DescendsAfterFrobenius (pullback.snd f (complementIdeal U).subschemeι) p
      (isInCharacteristic_of_hom (pullback.fst f (complementIdeal U).subschemeι) p hX)
      ((Scheme.Vect.pullback (pullback.fst f (complementIdeal U).subschemeι)).obj E)) :
    Scheme.Vect.DescendsAfterFrobenius f p hX E := by
  have : IsNoetherian Y := isNoetherian_of_compactSpace_over_field s
  obtain ⟨ℐ, -, hdisj, hadm, hflat'', hfp''⟩ :=
    exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase f U
      (TopologicalSpace.NoetherianSpace.isCompact _) hflat hfp
  let b := blowUpToBase ℐ
  have : IsProper b := Stacks.Blowup.IsAdmissibleBlowup.isProper hadm
  have : Surjective b := Stacks.Blowup.IsAdmissibleBlowup.surjective hadm hU
  have : LocallyOfFinitePresentation b := locallyOfFinitePresentation_of_locallyOfFiniteType
  have : IsReduced (blowUp ℐ) := isReduced_blowUp ℐ
  have : CompactSpace (blowUp ℐ) := QuasiCompact.compactSpace_of_compactSpace b
  have : QuasiSeparatedSpace (blowUp ℐ) := quasiSeparatedSpace_of_quasiSeparated b
  have : IsLocallyNoetherian (blowUp ℐ) := LocallyOfFiniteType.isLocallyNoetherian (b ≫ s)
  have hY'' : IsInCharacteristic (blowUp ℐ) p := isInCharacteristic_of_hom b p hY
  let f'' := strictTransformToBlowUp f ℐ
  have : Flat f'' := hflat''
  have : LocallyOfFinitePresentation f'' := hfp''.1
  have : IsProper f'' := by
    change IsProper ((Stacks.StrictTransform.ideal f b (exceptionalIdeal ℐ)).subschemeι ≫
      pullback.snd f b)
    infer_instance
  have : GeometricallyConnected f'' := geometricallyConnected_strictTransformToBlowUp f ℐ hU hdisj
  -- the total transform and its two closed pieces
  let W := pullback f b
  let fW := pullback.snd f b
  let gW := pullback.fst f b
  have hW : IsInCharacteristic W p := isInCharacteristic_of_hom gW p hX
  let i₁ := (Stacks.StrictTransform.ideal f b (exceptionalIdeal ℐ)).subschemeι
  have hX'' : IsInCharacteristic (Stacks.StrictTransform.scheme f b (exceptionalIdeal ℐ)) p :=
    isInCharacteristic_of_hom (i₁ ≫ gW) p hX
  let Zι := (complementIdeal U).subschemeι
  let t := pullback.snd Zι b
  have hT₂ : IsInCharacteristic (pullback Zι b) p := isInCharacteristic_of_hom t p hY''
  have : IsClosedImmersion t :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback Zι b)
      inferInstance
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian fW
  have : LocallyOfFinitePresentation i₁ := locallyOfFinitePresentation_of_locallyOfFiniteType
  have : LocallyOfFinitePresentation t := locallyOfFinitePresentation_of_locallyOfFiniteType
  let i₂ := pullback.fst fW t
  let f₂ := pullback.snd fW t
  have sq : IsPullback i₂ f₂ fW t := IsPullback.of_hasPullback fW t
  have hW₂ : IsInCharacteristic (pullback fW t) p := isInCharacteristic_of_hom i₂ p hW
  -- the two pieces cover the total transform
  have hcov : Set.range i₁ ∪ Set.range i₂ = Set.univ := by
    refine Set.eq_univ_of_forall fun w ↦ ?_
    by_cases hw : w ∈ Set.range i₂
    · exact Or.inr hw
    · left
      have hbU : b (fW w) ∈ (U : Set Y) := by
        by_contra hbU
        apply hw
        rwa [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Pullback.range_snd,
          Set.mem_preimage, Scheme.IdealSheafData.range_subschemeι,
          Stacks.AffineClosedUnion.support_vanishingIdeal]
      have hnot : w ∉ Stacks.StrictTransform.exceptionalPreimage f b (exceptionalIdeal ℐ) :=
        fun h ↦ preimage_le_compl_support_exceptionalIdeal ℐ hdisj hbU h
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact Stacks.StrictTransform.mem_support_ideal_of_notMem_exceptionalPreimage f b _ hnot
  -- the descent over the strict transform, by the flat case
  have hQ := isIso_c_strictTransformToBlowUp_morphismRestrict f ℐ hdisj
    (isIso_c_morphismRestrict_of_isIso_c f U)
  have hD₁ := descendsAfterFrobenius_of_flat k (b ≫ s) f'' (b ⁻¹ᵁ U)
    (dense_preimage_blowUpToBase ℐ hU hdisj) hQ hX'' hY'' _
    (hE.pullback (g' := i₁ ≫ gW) (f' := f'') (g := b) (by
      simp only [Category.assoc, gW, pullback.condition]; rfl) hX hX'')
  -- the descent over the part above `Z`, from the hypothesis
  let a : pullback fW t ⟶ pullback f Zι :=
    pullback.lift (i₂ ≫ gW) (f₂ ≫ pullback.fst Zι b) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, Category.assoc, pullback.condition])
  have hD₂ := hZ.pullback (g' := a) (f' := f₂) (g := pullback.fst Zι b)
    (pullback.lift_snd _ _ _) _ hW₂
  have ha : a ≫ pullback.fst f Zι = i₂ ≫ gW := pullback.lift_fst _ _ _
  -- glue, and descend along the blowup
  have : IsProper (i₁ ≫ fW) := inferInstanceAs (IsProper f'')
  have : Surjective (i₁ ≫ fW) := inferInstanceAs (Surjective f'')
  have : GeometricallyConnected (i₁ ≫ fW) := inferInstanceAs (GeometricallyConnected f'')
  have hmem := mem_essImage_of_closedCover (i₁ := i₁) sq hcov p hW hY'' hX'' hW₂ hT₂
    ⟨(Scheme.Vect.pullback gW).obj E, 0⟩
    ((mem_essImage_frobeniusColimitVectModelPullback_iff (i₁ ≫ fW) p hX'' hY'' _).mpr
      (hD₁.of_iso hX'' (((Scheme.Vect.pullbackComp i₁ gW).app E).symm)))
    ((mem_essImage_frobeniusColimitVectModelPullback_iff f₂ p hW₂ hT₂ _).mpr
      (hD₂.of_iso hW₂ ((Scheme.Vect.pullbackComp a (pullback.fst f Zι)).app E ≪≫
        (Scheme.Vect.pullbackCongr ha).app E ≪≫
        ((Scheme.Vect.pullbackComp i₂ gW).app E).symm)))
  exact descendsAfterFrobenius_of_baseChange f b hX hY E
    ((mem_essImage_frobeniusColimitVectModelPullback_iff fW p hW hY'' _).mp hmem)

/-- Precomposing with a surjective closed immersion keeps the fibres geometrically connected:
the geometric fibres change by a base change of the closed immersion, a homeomorphism. -/
theorem geometricallyConnected_comp_of_isClosedImmersion {X' : Scheme.{u}} (i : X' ⟶ X)
    [IsClosedImmersion i] [Surjective i] (f : X ⟶ Y) [GeometricallyConnected f] :
    GeometricallyConnected (i ≫ f) := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have h' := IsPullback.of_hasPullback f y
  have : ConnectedSpace ↑(pullback f y : Scheme.{u}) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) y _ _ h'
  let g : Z ⟶ pullback f y := h'.lift (fst ≫ i) snd (by rw [Category.assoc, h.w])
  have hg₂ : g ≫ pullback.snd f y = snd := h'.lift_snd _ _ _
  have hsq : IsPullback fst g i (pullback.fst f y) :=
    IsPullback.of_bot (by rw [hg₂]; exact h) (h'.lift_fst _ _ _).symm h'
  have : IsClosedImmersion g :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback hsq inferInstance
  have : Surjective g := MorphismProperty.of_isPullback (P := @Surjective) hsq ‹_›
  let e : Z ≃ₜ (pullback f y : Scheme.{u}) :=
    (Equiv.ofBijective g ⟨g.isClosedEmbedding.injective, g.surjective⟩).toHomeomorphOfIsInducing
      g.isClosedEmbedding.isInducing
  exact e.symm.surjective.connectedSpace e.symm.continuous

/-- **The essential-image half of Stacks Tag 0EXH over a base of finite type over a field, by
Noetherian induction.** Fix a Noetherian scheme `Y₀`. For every closed `T ⊆ Y₀`, the conclusion of
Stacks Tag 0EXH holds for every proper `f : X ⟶ Y` with geometrically connected fibres and every
`ℰ` satisfying the fibre condition, whenever `Y` is quasi-compact and locally of finite type over a
field and comes with a closed embedding into `Y₀` with image in `T`. -/
theorem descendsAfterFrobenius_of_closedEmbedding (k : Type u) [Field k] (Y₀ : Scheme.{u})
    [IsNoetherian Y₀] (T : TopologicalSpace.Closeds Y₀) :
    ∀ {X Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] [CompactSpace Y]
      (φ : Y ⟶ Y₀), Topology.IsClosedEmbedding φ.base → Set.range φ.base ⊆ T →
      ∀ (f : X ⟶ Y) [IsProper f] [GeometricallyConnected f] (hX : IsInCharacteristic X p)
        (hY : IsInCharacteristic Y p) (E : X.Vect),
        Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius f p hX E →
          Scheme.Vect.DescendsAfterFrobenius f p hX E := by
  induction T using WellFoundedLT.induction with
  | _ T IH =>
  intro X Y s _ _ φ hφ hφT f _ _ hX hY E hE
  have : IsNoetherian Y := isNoetherian_of_compactSpace_over_field s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := isNoetherian_of_compactSpace_over_field (f ≫ s)
  let ι := X.reductionι
  have : Surjective ι := ⟨X.surjective_reductionι⟩
  have hX₁ : IsInCharacteristic X.reduction p := isInCharacteristic_of_hom ι p hX
  refine descendsAfterFrobenius_of_reduction f hX hX₁ hY E ?_
  let f₁ := ι ≫ f
  have : GeometricallyConnected f₁ := geometricallyConnected_comp_of_isClosedImmersion ι f
  have hE₁ := hE.pullback (g' := ι) (f' := f₁) (g := 𝟙 Y) (Category.comp_id _).symm hX hX₁
  have : CompactSpace X.reduction := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace X.reduction := quasiSeparatedSpace_of_quasiSeparated f₁
  refine descendsAfterFrobenius_of_toNormalization f₁ hX₁ hY _ ?_
  let π := f₁.fromNormalization
  let f' := f₁.toNormalization
  have : IsFinite π := Stacks.SteinFactorization.isFinite_fromNormalization f₁
  have : UniversallyInjective π := universallyInjective_fromNormalization f₁
  have : IsProper f' := Stacks.SteinFactorization.isProper_toNormalization f₁
  have : GeometricallyConnected f' :=
    Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper f₁
  have hO : IsIso f'.c := Stacks.SteinFactorization.isIso_c_toNormalization_of_isProper f₁
  have hS : IsInCharacteristic f₁.normalization p := isInCharacteristic_of_hom π p hY
  have : CompactSpace f₁.normalization := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace f₁.normalization := quasiSeparatedSpace_of_quasiSeparated π
  have hπ : Topology.IsClosedEmbedding π.base :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap π.continuous π.injective
      π.isClosedMap
  have hE' := hE₁.pullback (g' := 𝟙 _) (f' := f') (g := π)
    (by rw [Category.id_comp]; exact (Scheme.Hom.toNormalization_fromNormalization f₁).symm)
    hX₁ hX₁
  refine Scheme.Vect.DescendsAfterFrobenius.of_iso hX₁ ((Scheme.Vect.pullbackId _).app _) ?_
  -- generic flatness over the Stein base, which is reduced
  obtain ⟨U, hUd, hflatU, hfpU⟩ := exists_dense_open_flat_finitePresentation_structureSheaf f'
  have hflat : Flat (f' ∣_ U) := by rwa [← Scheme.Hom.resLE_eq_morphismRestrict]
  have hfp : LocallyOfFinitePresentation (f' ∣_ U) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    exact hfpU.1
  by_cases hUtop : U = ⊤
  · -- the flat case
    rw [hUtop] at hflat
    have h1 : (f' ⁻¹ᵁ ⊤).ι ≫ f' = (f' ∣_ ⊤) ≫ (⊤ : f₁.normalization.Opens).ι :=
      (morphismRestrict_ι f' ⊤).symm
    have : Flat ((f' ⁻¹ᵁ ⊤).ι ≫ f') := by rw [h1]; infer_instance
    have : IsIso (f' ⁻¹ᵁ ⊤).ι := by
      rw [Scheme.Hom.preimage_top, ← Scheme.topIso_hom]; infer_instance
    have : Flat (inv (f' ⁻¹ᵁ ⊤).ι ≫ ((f' ⁻¹ᵁ ⊤).ι ≫ f')) := inferInstance
    have : Flat f' := by rwa [IsIso.inv_hom_id_assoc] at this
    exact descendsAfterFrobenius_of_flat k (π ≫ s) f' ⊤ dense_univ
      (isIso_c_morphismRestrict_of_isIso_c f' ⊤) hX₁ hS _ hE'
  · -- Noetherian induction on the non-flat locus
    let Zι := (complementIdeal U).subschemeι
    let φZ := Zι ≫ π ≫ φ
    have hφZ : Topology.IsClosedEmbedding φZ.base :=
      (hφ.comp hπ).comp Zι.isClosedEmbedding
    let T' : TopologicalSpace.Closeds Y₀ := ⟨Set.range φZ.base, hφZ.isClosed_range⟩
    have hT' : T' < T := by
      have hle : T' ≤ T := by
        rintro _ ⟨z, rfl⟩
        exact hφT ⟨π (Zι z), rfl⟩
      refine lt_of_le_of_ne hle fun h ↦ hUtop ?_
      have hall : ∀ x : f₁.normalization, x ∉ (U : Set f₁.normalization) := by
        intro x hx
        have hmem : φ (π x) ∈ (T' : Set Y₀) := h ▸ hφT ⟨π x, rfl⟩
        obtain ⟨z, hz⟩ := hmem
        have hzx : Zι z = x := (hφ.comp hπ).injective hz
        have hzU : Zι z ∈ ((complementIdeal U).support : Set _) := by
          rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
        rw [Stacks.AffineClosedUnion.support_vanishingIdeal] at hzU
        exact hzU (hzx ▸ hx)
      ext x
      have := hUd.closure_eq
      rw [Set.eq_empty_of_forall_notMem hall, closure_empty] at this
      exact absurd (this ▸ Set.mem_univ x : x ∈ (∅ : Set _)) (Set.notMem_empty x)
    have hZch : IsInCharacteristic (complementIdeal U).subscheme p :=
      isInCharacteristic_of_hom Zι p hS
    have hXZ : IsInCharacteristic (pullback f' Zι) p :=
      isInCharacteristic_of_hom (pullback.fst f' Zι) p hX₁
    have : CompactSpace (complementIdeal U).subscheme :=
      QuasiCompact.compactSpace_of_compactSpace Zι
    have hZ := IH T' hT' (Zι ≫ π ≫ s) φZ hφZ subset_rfl (pullback.snd f' Zι) hXZ hZch _
      (hE'.pullback (g' := pullback.fst f' Zι) (f' := pullback.snd f' Zι) (g := Zι)
        pullback.condition hX₁ hXZ)
    exact descendsAfterFrobenius_of_flattening k (π ≫ s) f' hO hX₁ hS _ hE' U hUd hflat hfp hZ

/-- **The essential-image half of Stacks Tag 0EXH over a base of finite type over a field.** Let
`Y` be quasi-compact and locally of finite type over a field, `f : X ⟶ Y` proper and surjective
with geometrically connected fibres, all in characteristic `p`, and `ℰ` a finite locally free
`𝒪_X`-module such that for every `y ∈ Y` some Frobenius power pullback of `ℰ` is free on the
reduced fibre `X_{y,red}`. Then some Frobenius power pullback of `ℰ` is the pullback of a finite
locally free `𝒪_Y`-module. -/
theorem descendsAfterFrobenius_of_finiteType (k : Type u) [Field k] (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] [CompactSpace Y] (f : X ⟶ Y) [IsProper f] [Surjective f]
    [GeometricallyConnected f] (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (E : X.Vect) (hE : Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius f p hX E) :
    Scheme.Vect.DescendsAfterFrobenius f p hX E := by
  have : IsNoetherian Y := isNoetherian_of_compactSpace_over_field s
  exact descendsAfterFrobenius_of_closedEmbedding k Y ⊤ s (𝟙 Y)
    Topology.IsClosedEmbedding.id (Set.subset_univ _) f hX hY E hE

end AlgebraicGeometry

end
