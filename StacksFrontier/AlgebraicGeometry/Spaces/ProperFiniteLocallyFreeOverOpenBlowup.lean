module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteTypeMorphismByBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCompositeCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeIdealOfQuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentImpliesCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformOverAdmissibleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFlatCompositionUnassumed
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCondition2
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineFinitePresentationFactorizationQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase

/-!
# A proper morphism finite locally free over an open becomes finite locally free after a blowup

Let `S` be a scheme, let `f : X ⟶ B` be a morphism of algebraic spaces over `S` and let `U ⊆ B`
be an open subspace.  Suppose that `B` is quasi-compact and quasi-separated, that `U` is
quasi-compact, that `f` is proper and that `f⁻¹(U) ⟶ U` is finite locally free.  Then there is
a `U`-admissible blowup `B' ⟶ B` such that the strict transform `X'` of `X` is finite locally
free over `B'`.  This is the content of Stacks 0B4K.

The argument follows the source, with the order of its two blowups exchanged as in the proof of
Stacks 0GUW.  Blow `B` up in a finitely presented closed subspace `Z₀` whose points are the
complement of those of `U` (Stacks 0855); the inverse image `U₁` of `U` is the complement of an
effective Cartier divisor, hence scheme-theoretically dense (Stacks 085T and 083S), and the strict
transform `X₁` of `X` is proper over the blowup `B₁`, and over `U₁` it is the base change of
`f⁻¹(U) ⟶ U`, so finite, flat and locally of finite presentation there. Flattening by blowing up
(Stacks 087E) gives a `U₁`-admissible blowup `B₂ ⟶ B₁` over which the strict transform `X₂` of
`X₁` is flat and of finite presentation. The inverse image `U₂` of `U₁` is still
scheme-theoretically dense, in particular its points are dense, and `X₂ ⟶ B₂` is flat, proper, of
finite presentation and finite over `U₂`, so it is finite (Stacks 0B4J), hence finite locally free
(Stacks 0416). The composite `B₂ ⟶ B` is the blowup of `B` in a finitely presented centre `Y`
whose points are the complement of those of `U` (Stacks 0860), and `X₂` is the strict transform
of `X` along it (Stacks 0868, part (2)).

## Main results

* `Space.exists_isPullback_pullbackSnd_strictTransformSpaceToBlowUp`: over the inverse image of
  an open subspace avoiding the centre, the strict transform is the base change of the restriction
  of the morphism.
* `Space.exists_isBlowupAlong_isFiniteLocallyFree_strictTransformSpaceToBlowUp_of_isProper`: a
  proper morphism finite locally free over a quasi-compact open becomes finite locally free after
  an admissible blowup (Stacks 0B4K).

## Implementation notes

A `U`-admissible blowup is the blowup in a finitely presented closed subspace disjoint from `U`
(`AlgebraicGeometry.Space.IsAdmissibleBlowup`, Stacks 086B).  The strict transform depends on the
centre and not only on the morphism `B' ⟶ B`, so the conclusion names the centre `Z`.  Finite
local freeness is `AlgebraicGeometry.Space.IsFiniteLocallyFree` (Stacks 03ZV), the hypothesis
being read on the restriction `X ×_B U ⟶ U` of `f`.  Quasi-separatedness of `B` is absolute
quasi-separatedness.

## References

* [Stacks Project, Tag 0B4K](https://stacks.math.columbia.edu/tag/0B4K)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0B4J](https://stacks.math.columbia.edu/tag/0B4J)
* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A quasi-compact open subspace of a quasi-compact quasi-separated algebraic space is the
complement of a closed subspace of finite presentation: by Stacks 0855 there is a finite type
quasi-coherent sheaf of ideals with zero locus the complement, which defines a closed subspace
(Stacks 03MB), of finite presentation by Stacks 084Q. -/
private theorem exists_closedSubspace_isFinitePresentation_points_eq_compl_of_qcqs
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {O : Subfunctor X.1} (hO : IsOpenSubspace B S hS O)
    (hOqc : IsQuasiCompactSpace B S hS O.toFunctor) :
    ∃ Z : ClosedSubspaces B S hS X.1, IsFinitePresentation B S hS Z.1.ι ∧
      subspacePointSet B S hS X.1 Z.1 = (subspacePointSet B S hS X.1 O)ᶜ := by
  obtain ⟨I, ⟨hIqc, hIft⟩, hIzero⟩ :=
    hasFiniteTypeQuasicoherentIdealZeroLocus_of_isQuasiCompactSpace B S hS hZ X hXqc hXqs hO
      hOqc
  obtain ⟨Z, hZI⟩ := exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts B S hS X I
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _ hIqc)
  refine ⟨Z, (isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf B S hS
    (ObjectProperty.homMk Z.1.ι : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
    Z.2.2).2 ?_, ?_⟩
  · rw [kernelIdealSheaf_eq_definingIdealSheaf, hZI]
    exact hIft
  · rw [subspacePointSet, range_pointsMap_ι_eq_idealZeroLocus B S hS X Z, hZI, ← hIzero]

/-- The strict transform of a proper morphism is proper: it is the closed immersion of the strict
transform into the base change, followed by the base change of the proper morphism. -/
private theorem isProper_strictTransformSpaceToBlowUp_of_isProper {A X A' : AlgebraicSpaces B S hS}
    (f : X ⟶ A) (b : A' ⟶ A) (E : Subfunctor A'.1) (hf : IsProper B S hS f.hom) :
    IsProper B S hS (strictTransformSpaceToBlowUp B S hS f b E).hom :=
  isProper_comp B S hS (strictTransformSpace B S hS f b E).2
    (strictTransformPullback B S hS f b).2 A'.2 _ _
    (isProper_of_isClosedImmersion B S hS (strictTransformSpace B S hS f b E).2
      (strictTransformPullback B S hS f b).2 _ (strictTransform B S hS f b E).2.2)
    ((isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b) hf)

/-- Being finite, flat and locally of finite presentation passes to a base change. -/
private theorem finite_flat_lfp_of_isPullback {P X' Y' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hX' : IsAlgebraicSpace B S hS X')
    (hY' : IsAlgebraicSpace B S hS Y') (hZ' : IsAlgebraicSpace B S hS Z')
    {a : P ⟶ X'} {b : P ⟶ Y'} {f : X' ⟶ Z'} {g : Y' ⟶ Z'} (sq : IsPullback a b f g)
    (h : IsFinite B S hS f ∧ IsFlat B S hS f ∧ IsLocallyOfFinitePresentation B S hS f) :
    IsFinite B S hS b ∧ IsFlat B S hS b ∧ IsLocallyOfFinitePresentation B S hS b :=
  ⟨isFinite_of_isPullback B S hS sq h.1,
    isFlat_of_isPullback_of_isAlgebraicSpace B S hS sq.flip hX' hZ' h.2.1,
    IsLocallyOfFinitePresentation.of_isPullback B S hS hP hX' hY' hZ' sq h.2.2⟩

/-- **Over the inverse image of an open subspace avoiding the centre, the strict transform is a
base change of the restriction.**  Let `b : A' ⟶ A` be the blowup of `A` in a closed subspace
`Z`, let `U ⊆ A` be an open subspace whose points avoid those of `Z`, and let `f : X ⟶ A`.  Then
the restriction of the strict transform `X' ⟶ A'` of `X` to `b⁻¹(U)` is the base change of
`X ×_A U ⟶ U` along `b⁻¹(U) ⟶ U`.

Over `b⁻¹(U)` the strict transform is all of `X ×_A A'`
(`AlgebraicGeometry.Space.range_pullbackFst_preimage_le_strictTransform`), and the part of
`X ×_A A'` over `b⁻¹(U)` is `(X ×_A U) ×_U b⁻¹(U)`. -/
theorem exists_isPullback_pullbackSnd_strictTransformSpaceToBlowUp
    {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)
    (Z : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (U : OpenSubspaces B S hS A.1)
    (hUZ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1)) :
    ∃ k : pullback (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom
        (U.1.preimage b.hom).ι ⟶ pullback f.hom U.1.ι,
      IsPullback k (pullback.snd (strictTransformSpaceToBlowUp B S hS f b
          (Z.1.preimage b.hom)).hom (U.1.preimage b.hom).ι)
        (pullback.snd f.hom U.1.ι) (U.1.fromPreimage b.hom) := by
  set U' := U.1.preimage b.hom
  set p := (strictTransformPullbackToBlowUp B S hS f b).hom
  set i := (strictTransform B S hS f b (Z.1.preimage b.hom)).1.ι
  -- the square for `X ×_A A' ⟶ A'`
  have sq1 : IsPullback (pullback.fst f.hom b.hom) (pullback.snd f.hom b.hom) f.hom b.hom :=
    IsPullback.of_hasPullback _ _
  have sq2 : IsPullback (pullback.fst (pullback.snd f.hom b.hom) U'.ι)
      (pullback.snd (pullback.snd f.hom b.hom) U'.ι) (pullback.snd f.hom b.hom) U'.ι :=
    IsPullback.of_hasPullback _ _
  have sq3 := Subfunctor.isPullback_preimage b.hom U.1
  have sq4 : IsPullback (pullback.fst f.hom U.1.ι) (pullback.snd f.hom U.1.ι) f.hom U.1.ι :=
    IsPullback.of_hasPullback _ _
  have outer := sq2.paste_horiz sq1
  rw [← sq3.w] at outer
  have hw : (pullback.fst (pullback.snd f.hom b.hom) U'.ι ≫ pullback.fst f.hom b.hom) ≫ f.hom =
      (pullback.snd (pullback.snd f.hom b.hom) U'.ι ≫ U.1.fromPreimage b.hom) ≫ U.1.ι := by
    rw [outer.w, Category.assoc]
  have hs : IsPullback ((pullback.lift _ _ hw) ≫ pullback.fst f.hom U.1.ι)
      (pullback.snd (pullback.snd f.hom b.hom) U'.ι) f.hom
      (U.1.fromPreimage b.hom ≫ U.1.ι) := by
    rw [pullback.lift_fst]
    exact outer
  have top : IsPullback (pullback.lift _ _ hw) (pullback.snd p U'.ι)
      (pullback.snd f.hom U.1.ι) (U.1.fromPreimage b.hom) :=
    IsPullback.of_right hs (pullback.lift_snd _ _ hw) sq4
  -- the strict transform is everything over `U'`
  have hfac := range_pullbackFst_preimage_le_strictTransform f b Z hb U hUZ
  set h := Subfunctor.lift (pullback.fst p U'.ι) hfac
  have hh : h ≫ i = pullback.fst p U'.ι := Subfunctor.lift_ι _ _
  have : Mono i := inferInstance
  let φ : pullback (i ≫ p) U'.ι ⟶ pullback p U'.ι :=
    pullback.lift (pullback.fst (i ≫ p) U'.ι ≫ i) (pullback.snd (i ≫ p) U'.ι)
      (by rw [Category.assoc, pullback.condition])
  let ψ : pullback p U'.ι ⟶ pullback (i ≫ p) U'.ι :=
    pullback.lift h (pullback.snd p U'.ι) (by rw [reassoc_of% hh, pullback.condition])
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← cancel_mono i, Category.assoc,
        hh, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.lift_snd]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hh,
        Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp, pullback.lift_snd]
  have : IsIso φ := ⟨⟨ψ, hφψ, hψφ⟩⟩
  have hiso : IsPullback φ (pullback.snd (i ≫ p) U'.ι) (pullback.snd p U'.ι) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [pullback.lift_snd, Category.comp_id]⟩
  have hpaste := hiso.paste_horiz top
  rw [Category.id_comp] at hpaste
  exact ⟨_, hpaste⟩

/-- If `f` is finite, flat and locally of finite presentation over an open `U` avoiding the centre
of a blowup `b`, then so is the strict transform over `b⁻¹(U)`. -/
private theorem finite_flat_lfp_strictTransformSpaceToBlowUp_preimage
    {A X A' : AlgebraicSpaces B S hS} (f : X ⟶ A) (b : A' ⟶ A)
    (Z : ClosedSubspaces B S hS A.1) (hb : IsBlowupAlong B S hS Z b)
    (U : OpenSubspaces B S hS A.1)
    (hUZ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1))
    (h : IsFinite B S hS (pullback.snd f.hom U.1.ι) ∧ IsFlat B S hS (pullback.snd f.hom U.1.ι) ∧
      IsLocallyOfFinitePresentation B S hS (pullback.snd f.hom U.1.ι)) :
    IsFinite B S hS (pullback.snd (strictTransformSpaceToBlowUp B S hS f b
        (Z.1.preimage b.hom)).hom (U.1.preimage b.hom).ι) ∧
      IsFlat B S hS (pullback.snd (strictTransformSpaceToBlowUp B S hS f b
        (Z.1.preimage b.hom)).hom (U.1.preimage b.hom).ι) ∧
      IsLocallyOfFinitePresentation B S hS (pullback.snd (strictTransformSpaceToBlowUp B S hS f b
        (Z.1.preimage b.hom)).hom (U.1.preimage b.hom).ι) := by
  obtain ⟨k, hk⟩ := exists_isPullback_pullbackSnd_strictTransformSpaceToBlowUp f b Z hb U hUZ
  exact finite_flat_lfp_of_isPullback
    (isAlgebraicSpace_pullback B S hS _ (U.1.preimage b.hom).ι
      (strictTransformSpace B S hS f b (Z.1.preimage b.hom)).2
      (isOpenSubspace_preimage B S hS b.hom U.1 A.2 A'.2 U.2).1 A'.2)
    (isAlgebraicSpace_pullback B S hS f.hom U.1.ι X.2 U.2.1 A.2)
    (isOpenSubspace_preimage B S hS b.hom U.1 A.2 A'.2 U.2).1 U.2.1 hk h

/-- **A proper morphism finite locally free over a quasi-compact open becomes finite locally free
after a blowup (the content of Stacks 0B4K).**  Let `f : X ⟶ A` be a morphism of algebraic
spaces over `S` and let `U ⊆ A` be an open subspace.  Assume that `A` is quasi-compact and
quasi-separated, that `U` is quasi-compact, that `f` is proper and that `f⁻¹(U) ⟶ U` is finite
locally free.  Then there is a `U`-admissible blowup `b : A' ⟶ A`, with finitely presented
centre `Z` whose points avoid those of `U`, such that the strict transform of `X` is finite
locally free over `A'`.

See the module documentation for the argument. -/
theorem exists_isBlowupAlong_isFiniteLocallyFree_strictTransformSpaceToBlowUp_of_isProper
    (hZ : B.Contains (⊤_ Scheme.{u})) {A X : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (U : OpenSubspaces B S hS A.1)
    (hAqc : IsQuasiCompactSpace B S hS A.1) (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hf : IsProper B S hS f.hom) (hflf : IsFiniteLocallyFree B S hS (restrictOverHom f U)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
          IsBlowupAlong B S hS Z b ∧
            IsFiniteLocallyFree B S hS
              (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  -- `f⁻¹(U) ⟶ U` is finite, flat and locally of finite presentation (Stacks 03ZW, 0416)
  have hU := (isFiniteLocallyFree_presheaf_iff B S hS (restrictOver f U).2 U.2.1
    (restrictOverHom f U).hom).1
    ((isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS (restrictOverHom f U)).2 hflf)
  have hUι : IsQuasiCompact B S hS U.1.ι :=
    (isQuasiCompact_iff_isQuasiCompactSpace_openSubspace B S hS hZ A hAqc hAqs U).2 hUqc
  -- Blow up a finitely presented closed subspace with complement `U`.
  obtain ⟨Z₀, hZ₀fp, hZ₀pts⟩ :=
    exists_closedSubspace_isFinitePresentation_points_eq_compl_of_qcqs hZ hAqc hAqs U.2 hUqc
  have hUZ₀ : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z₀.1) := by
    rw [hZ₀pts]
    exact disjoint_compl_right
  obtain ⟨A₁, b₁, hb₁⟩ := exists_isBlowupAlong_of_isFinitePresentation Z₀ hZ₀fp
  have hb₁p : IsProper B S hS b₁.hom :=
    isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Z₀ b₁ hZ₀fp hb₁
  have _ : IsIso (pullback.snd (𝟙 A.1) b₁.hom) := inferInstance
  have hA₁qc : IsQuasiCompactSpace B S hS A₁.1 :=
    (hb₁p.isFiniteType.2 A.1 A.2 hAqc (𝟙 A.1)).of_iso B S hS
      (asIso (pullback.snd (𝟙 A.1) b₁.hom))
  have hA₁qs : IsAbsolutelyQuasiSeparated B S hS hZ A₁.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ A₁.2 hAqs
      (isQuasiSeparated_of_isSeparated B S hS hb₁p.isSeparated)
  let U₁ : OpenSubspaces B S hS A₁.1 :=
    ⟨U.1.preimage b₁.hom, isOpenSubspace_preimage B S hS b₁.hom U.1 A.2 A₁.2 U.2⟩
  have hU₁ι : IsQuasiCompact B S hS U₁.1.ι :=
    isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage b₁.hom U.1) hUι
  have hU₁dense : IsSchemeTheoreticallyDense B S hS U₁.1 :=
    isSchemeTheoreticallyDense_preimage_of_isBlowupAlong U Z₀ hb₁ hZ₀pts
  have hU₁qc : IsQuasiCompactSpace B S hS U₁.1.toFunctor :=
    (isQuasiCompact_iff_isQuasiCompactSpace_openSubspace B S hS hZ A₁ hA₁qc hA₁qs U₁).1 hU₁ι
  -- The strict transform `X₁ ⟶ A₁`: proper, and finite, flat, lfp over `U₁`.
  set f₁ := strictTransformSpaceToBlowUp B S hS f b₁ (Z₀.1.preimage b₁.hom) with hf₁def
  have hf₁ : IsProper B S hS f₁.hom := isProper_strictTransformSpaceToBlowUp_of_isProper f b₁ _ hf
  have hU₁ := finite_flat_lfp_strictTransformSpaceToBlowUp_preimage f b₁ Z₀ hb₁ U hUZ₀ hU
  -- Flattening by blowing up.
  obtain ⟨A₂, b₂, Z₁, hZ₁fp, hU₁Z₁, hb₂, hflat₂, hfp₂⟩ :=
    exists_isBlowupAlong_isFlat_isFinitePresentation_strictTransformSpaceToBlowUp_of_isFiniteType
      hZ f₁ U₁ hA₁qc hA₁qs hU₁qc hf₁.isFiniteType
      (isQuasiSeparated_of_isSeparated B S hS hf₁.isSeparated) hU₁.2.1 hU₁.2.2
  -- The composite blowup, whose centre has complement `U`.
  obtain ⟨Y, hYfp, hYcomp, hYb⟩ := exists_isCompositeCentre_isBlowupAlong hb₁ hZ₀fp hb₂ hZ₁fp
    (hasSecondCentre hZ hAqc hAqs hZ₀fp hb₁)
  have hYpts : subspacePointSet B S hS A.1 Y.1 = (subspacePointSet B S hS A.1 U.1)ᶜ := by
    have hY : subspacePointSet B S hS A.1 Y.1 = subspacePointSet B S hS A.1 Z₀.1 ∪
        pointsMap B S hS A₁.1 b₁.hom '' subspacePointSet B S hS A₁.1 Z₁.1 := hYcomp
    rw [hY, Set.union_eq_left.2, hZ₀pts]
    rintro _ ⟨w, hw, rfl⟩
    rw [hZ₀pts]
    intro hu
    have hwU : w ∈ subspacePointSet B S hS A₁.1 U₁.1 := by
      rw [subspacePointSet_preimage, Set.mem_preimage]
      exact hu
    exact Set.disjoint_left.1 hU₁Z₁ hwU hw
  have hUY : Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Y.1) := by
    rw [hYpts]
    exact disjoint_compl_right
  -- The second strict transform `X₂ ⟶ A₂` is finite over `U₂`, hence finite (Stacks 0B4J).
  set f₂ := strictTransformSpaceToBlowUp B S hS f₁ b₂ (Z₁.1.preimage b₂.hom) with hf₂def
  let U₂ : OpenSubspaces B S hS A₂.1 :=
    ⟨U₁.1.preimage b₂.hom, isOpenSubspace_preimage B S hS b₂.hom U₁.1 A₁.2 A₂.2 U₁.2⟩
  have hf₂ : IsProper B S hS f₂.hom := isProper_strictTransformSpaceToBlowUp_of_isProper f₁ b₂ _ hf₁
  have hU₂ := finite_flat_lfp_strictTransformSpaceToBlowUp_preimage f₁ b₂ Z₁ hb₂ U₁ hU₁Z₁ hU₁
  have hU₂dense : IsSchemeTheoreticallyDense B S hS U₂.1 :=
    isSchemeTheoreticallyDense_preimage_of_isBlowupAlong_of_isSchemeTheoreticallyDense b₂ Z₁ hb₂
      U₁.1 hU₁dense
  have hf₂fin : IsFinite B S hS f₂.hom :=
    isFinite_of_isFinite_over_dense_open B S hS
      (strictTransformSpace B S hS f₁ b₂ (Z₁.1.preimage b₂.hom)).2 A₂.2 f₂.hom hflat₂ hf₂
      U₂.1 U₂.2 (dense_subspacePointSet_of_isSchemeTheoreticallyDense B S hS (X := A₂) U₂.1
        hU₂dense) hU₂.1 (Or.inl hfp₂.1)
  -- The strict transform along the composite is the second strict transform.
  obtain ⟨k, j, -, hk, hj⟩ :=
    exists_strictTransformSpace_comp_iso_unconditional B S hS f b₁ b₂ Z₀ Z₁ Y hb₁ hb₂ hYcomp hYb
  refine ⟨A₂, b₂ ≫ b₁, Y, hYfp, hUY, hYb, ?_⟩
  have hcomp : j.hom ≫ strictTransformSpaceToBlowUp B S hS f (b₂ ≫ b₁)
      (Y.1.preimage (b₂ ≫ b₁).hom) = f₂ := by
    change j.hom ≫ strictTransformSpaceι B S hS f (b₂ ≫ b₁) (Y.1.preimage (b₂ ≫ b₁).hom) ≫
        strictTransformPullbackToBlowUp B S hS f (b₂ ≫ b₁) =
      strictTransformSpaceι B S hS f₁ b₂ (Z₁.1.preimage b₂.hom) ≫
        strictTransformPullbackToBlowUp B S hS f₁ b₂
    rw [reassoc_of% hj, hk]
  have heq : strictTransformSpaceToBlowUp B S hS f (b₂ ≫ b₁) (Y.1.preimage (b₂ ≫ b₁).hom) =
      j.inv ≫ f₂ := by
    rw [← hcomp, Iso.inv_hom_id_assoc]
  rw [heq]
  have hjinv : IsIso j.inv.hom :=
    ⟨⟨j.hom.hom, by simp, by simp⟩⟩
  -- `j⁻¹ ≫ f₂` is finite, flat and locally of finite presentation, hence finite locally free.
  have hsq : IsPullback j.inv.hom (j.inv ≫ f₂).hom f₂.hom (𝟙 A₂.1) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h₃ := finite_flat_lfp_of_isPullback (strictTransformSpace B S hS f (b₂ ≫ b₁)
      (Y.1.preimage (b₂ ≫ b₁).hom)).2
    (strictTransformSpace B S hS f₁ b₂ (Z₁.1.preimage b₂.hom)).2 A₂.2 A₂.2 hsq
    ⟨hf₂fin, hflat₂, hfp₂.1⟩
  exact (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS _).1
    ((isFiniteLocallyFree_presheaf_iff B S hS (strictTransformSpace B S hS f (b₂ ≫ b₁)
      (Y.1.preimage (b₂ ≫ b₁).hom)).2 A₂.2 _).2 h₃)

end AlgebraicGeometry.Space

end
