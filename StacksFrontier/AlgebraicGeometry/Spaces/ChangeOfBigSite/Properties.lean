module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite.Charts
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmoothEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFibreProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableAtlasTest
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Properties of algebraic spaces preserved and reflected by enlarging the big fppf site

Let `B ⊆ B'` be big fppf sites and let `G = AlgebraicGeometry.changeBigSite B B' h S hS` be
the inverse image of Stacks 04W1 from algebraic spaces over `S` on `B` to algebraic spaces over
`S` on `B'`. This file shows that `G` preserves and reflects quasi-compactness of algebraic
spaces, preserves quasi-separatedness of quasi-compact algebraic spaces, and preserves and
reflects the following properties of morphisms: properties of morphisms of schemes étale local
on source and target, checked on étale charts; properties of the represented base changes that
are stable under base change and fppf local on the target; finite presentation (preserved
between quasi-compact quasi-separated spaces); and separatedness.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_changeBigSite_obj_iff`: `G X` is quasi-compact if
  and only if `X` is.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_changeBigSite_obj`: if `X` is
  quasi-compact and quasi-separated, then `G X` is quasi-separated.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_changeBigSite_map_iff`: a property étale local
  on source and target holds on every étale chart of `G f` if and only if it holds on every
  étale chart of `f`.
* `AlgebraicGeometry.Space.presheaf_changeBigSite_map`: a property of the represented base
  changes of `f`, stable under base change and fppf local on the target, holds for `G f` when
  `G f` is representable.
* `AlgebraicGeometry.Space.isFinitePresentation_of_changeBigSite_map`: if `G f` is of finite
  presentation, then so is `f`.
* `AlgebraicGeometry.Space.isFinitePresentation_changeBigSite_map`: a morphism of finite
  presentation between quasi-compact quasi-separated spaces is carried to one of finite
  presentation.
* `AlgebraicGeometry.Space.isSeparated_changeBigSite_map_iff`: `G f` is separated if and only if
  `f` is.

## References

* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
* [Stacks Project, Tag 02WZ](https://stacks.math.columbia.edu/tag/02WZ)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S)

/-- Pullbacks of presheaves on a big fppf site, given directly: instance search for them times
out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ChangeOfBigSiteProperties
    (C : BigFppfSite.{u}) (T : Scheme.{u}) (hT : C.Contains T) :
    HasPullbacks ((BigFppfOver C T hT)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ChangeOfBigSiteProperties
    {C : BigFppfSite.{u}} {T : Scheme.{u}} {hT : C.Contains T}
    {X Y Z : (BigFppfOver C T hT)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_ChangeOfBigSiteProperties C T hT).has_limit _

/-- Pullbacks of transported morphisms, given directly: instance search does not find
`hasPullback_presheaf_ChangeOfBigSiteProperties` for them under Lean v4.35.0. -/
local instance (priority := high) hasPullback_changeBigSite_map_ChangeOfBigSiteProperties
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan ((changeBigSite B B' h S hS).map f).hom
      ((changeBigSite B B' h S hS).map g).hom) :=
  hasPullback_presheaf_ChangeOfBigSiteProperties _ _

/-! ### Transported charts -/

/-- The transport of a chart followed by the transport of a morphism is the transport of the
composite chart. -/
theorem changeBigSiteChart_comp_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ X.obj) :
    (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk a)).hom ≫
        ((changeBigSite B B' h S hS).map f).hom =
      (changeBigSiteChart B B' h S hS Y (CostructuredArrow.mk (a ≫ f.hom))).hom := by
  rw [changeBigSiteChart_hom, changeBigSiteChart_hom]
  refine (Category.assoc _ _ _).trans (congrArg (changeBigSiteYonedaHom B B' h S hS T ≫ ·) ?_)
  exact (congrArg (fun k => k.hom)
    ((changeBigSite B B' h S hS).map_comp
      (ObjectProperty.homMk a : (schemeSpaceFunctor B S hS).obj T ⟶ X) f)).symm

/-- **Cartesian squares of charts are transported to cartesian squares of charts.** If the
represented fibre product of two charts `a : U ⟶ X` and `b : V ⟶ X` is the object `R` of the
smaller site, then `R` read in the larger site is the fibre product of the transported charts. -/
theorem isPullback_changeBigSiteChart_of_isPullback {X : AlgebraicSpaces B S hS}
    {R U V : BigFppfOver B S hS} {r₁ : R ⟶ U} {r₂ : R ⟶ V} {a : yoneda.obj U ⟶ X.obj}
    {b : yoneda.obj V ⟶ X.obj} (hpb : IsPullback (yoneda.map r₁) (yoneda.map r₂) a b) :
    IsPullback (yoneda.map ((inclusionOver h S hS).map r₁))
      (yoneda.map ((inclusionOver h S hS).map r₂))
      (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk a)).hom
      (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk b)).hom := by
  have h1 := isPullback_changeBigSiteChart B B' h S hS (X := (schemeSpaceFunctor B S hS).obj U)
    (Y := X) (ObjectProperty.homMk a) (yoneda.map r₁) r₂ b hpb
  let e := changeBigSiteYonedaIso B B' h S hS U
  have hc₁ : (changeBigSiteChart B B' h S hS ((schemeSpaceFunctor B S hS).obj U)
      (CostructuredArrow.mk (yoneda.map r₁))).hom =
        yoneda.map ((inclusionOver h S hS).map r₁) ≫ e.hom := by
    rw [changeBigSiteChart_hom]
    exact (changeBigSiteYonedaHom_naturality B B' h S hS r₁).symm
  exact IsPullback.of_iso h1 (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    ((Iso.comp_inv_eq e).mpr (hc₁.trans (congrArg (· ≫ e.hom) (Category.id_comp _).symm)))
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans ((Iso.eq_inv_comp e).mpr
      (changeBigSiteChart_hom B B' h S hS X (CostructuredArrow.mk a)).symm))
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The transport of an étale chart is étale. -/
theorem isEtale_changeBigSiteChart {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    {a : yoneda.obj T ⟶ X.obj} (ha : IsEtale B S hS a) :
    IsEtale B' S (largerContains h hS)
      (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk a)).hom :=
  isEtale_hom_of_isEtaleChart B' S (largerContains h hS)
    (isEtaleChart_changeBigSiteChart B B' h S hS X
      ((isEtale_iff_presheaf_of_yoneda B S hS a).mp ha))

/-! ### Quasi-compact algebraic spaces -/

/-- **Enlarging the big fppf site preserves quasi-compact algebraic spaces.** -/
theorem isQuasiCompactSpace_changeBigSite_obj {X : AlgebraicSpaces B S hS}
    (hX : IsQuasiCompactSpace B S hS X.obj) :
    IsQuasiCompactSpace B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj := by
  obtain ⟨U, q, hc, hs, he⟩ := hX
  exact ⟨(inclusionOver h S hS).obj U,
    (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk q)).hom, hc,
    presheaf_surjective_changeBigSiteChart B B' h S hS X hs
      ((isEtale_iff_presheaf_of_yoneda B S hS q).mp he),
    isEtale_changeBigSiteChart B B' h S hS he⟩

/-- **Enlarging the big fppf site reflects quasi-compact algebraic spaces.** -/
theorem isQuasiCompactSpace_of_changeBigSite_obj {X : AlgebraicSpaces B S hS}
    (hX : IsQuasiCompactSpace B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj) :
    IsQuasiCompactSpace B S hS X.obj := by
  let hS' : B'.Contains S := largerContains h hS
  obtain ⟨V, v, hVaff, hvs, hve⟩ := (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
    B' S hS' _ ((changeBigSite B B' h S hS).obj X).property).mp hX
  have hve' := (isEtale_iff_presheaf_of_yoneda B' S hS' v).mp hve
  obtain ⟨T, e, g, hg⟩ := exists_changeBigSiteChart_eq B B' h S hS
    (size_lt_cutoff_of_isAffineChart_changeBigSite B B' h S hS X
      ⟨CostructuredArrow.mk v, hve'⟩ hVaff) v
  have hg' : ∀ {P : MorphismProperty Scheme.{u}},
      MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B' S hS')) v →
      MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B' S hS'))
        (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk g)).hom := fun {P} hv =>
    hg ▸ @MorphismProperty.RespectsIso.precomp _ _ _ (MorphismProperty.relative_respectsIso _)
      _ _ _ (yoneda.map e.hom) (Iso.isIso_hom (yoneda.mapIso e)) v hv
  have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    @IsAffine.of_isIso _ _ ((BigFppfOver.toScheme B' S hS').map e.hom)
      (Iso.isIso_hom ((BigFppfOver.toScheme B' S hS').mapIso e)) hVaff
  exact (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _
    X.property).mpr ⟨T, g, hTaff,
      presheaf_of_presheaf_changeBigSiteChart B B' h S hS _ g (hg' hvs),
      (isEtale_iff_presheaf_of_yoneda B S hS g).mpr
        (presheaf_of_presheaf_changeBigSiteChart B B' h S hS _ g (hg' hve'))⟩

/-- **Quasi-compactness of an algebraic space is invariant under enlarging the big fppf
site.** -/
theorem isQuasiCompactSpace_changeBigSite_obj_iff (X : AlgebraicSpaces B S hS) :
    IsQuasiCompactSpace B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj ↔
      IsQuasiCompactSpace B S hS X.obj :=
  ⟨isQuasiCompactSpace_of_changeBigSite_obj B B' h S hS,
    isQuasiCompactSpace_changeBigSite_obj B B' h S hS⟩

/-! ### Quasi-separated algebraic spaces -/

/-- **Enlarging the big fppf site carries a quasi-compact quasi-separated algebraic space to a
quasi-separated one.** -/
theorem isAbsolutelyQuasiSeparated_changeBigSite_obj (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} (hqc : IsQuasiCompactSpace B S hS X.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.obj) :
    IsAbsolutelyQuasiSeparated B' S (largerContains h hS) (largerContains h hZ)
      ((changeBigSite B B' h S hS).obj X).obj := by
  let hS' : B'.Contains S := largerContains h hS
  obtain ⟨U, q, hUaff, hqS, hqE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ X.property).mp hqc
  have hqE' : IsEtaleChart B S hS X.obj (CostructuredArrow.mk q) :=
    (isEtale_iff_presheaf_of_yoneda B S hS q).mp hqE
  have hUc : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) :=
    @Scheme.compactSpace_of_isAffine _ hUaff
  obtain ⟨W, hWc, ⟨eW⟩⟩ := (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback B S hS hZ
    X.obj X.property).mp hqs U U q q hUc hUc
  let r₁ : W ⟶ U := yoneda.preimage (eW.hom ≫ pullback.fst q q)
  let r₂ : W ⟶ U := yoneda.preimage (eW.hom ≫ pullback.snd q q)
  have hR : IsPullback (yoneda.map r₁) (yoneda.map r₂) q q := by
    rw [Functor.map_preimage, Functor.map_preimage]
    exact IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, Category.assoc, pullback.condition]⟩ eW rfl rfl
  have hr₂ : QuasiCompact ((BigFppfOver.toScheme B S hS).map r₂) :=
    @quasiCompact_of_compactSpace _ _ _ hWc (@quasiSeparatedSpace_of_isAffine _ hUaff)
  exact isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection B' S hS'
    (largerContains h hZ) ((changeBigSite B B' h S hS).obj X).property
    (presheaf_surjective_changeBigSiteChart B B' h S hS X hqS hqE')
    (isEtaleChart_changeBigSiteChart B B' h S hS X hqE')
    (@QuasiSeparated.of_quasiSeparatedSpace _ _ _ (@quasiSeparatedSpace_of_isAffine _ hUaff))
    (isPullback_changeBigSiteChart_of_isPullback B B' h S hS hR) hr₂

/-! ### Properties checked on étale charts -/

/-- **Enlarging the big fppf site reflects properties checked on every étale chart.** -/
theorem holdsOnEveryEtaleChart_of_changeBigSite_map (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : HoldsOnEveryEtaleChart B' S (largerContains h hS) P
      ((changeBigSite B B' h S hS).map f).hom) :
    HoldsOnEveryEtaleChart B S hS P f.hom := by
  intro U V a b c ha hb hw
  refine hf _ _ (changeBigSiteChart B B' h S hS X (CostructuredArrow.mk a)).hom
    (changeBigSiteChart B B' h S hS Y (CostructuredArrow.mk b)).hom
    ((inclusionOver h S hS).map c)
    (isEtaleChart_changeBigSiteChart B B' h S hS X (U := CostructuredArrow.mk a) ha)
    (isEtaleChart_changeBigSiteChart B B' h S hS Y (U := CostructuredArrow.mk b) hb) ?_
  rw [changeBigSiteChart_comp_map]
  exact changeBigSiteChart_w B B' h S hS Y (CostructuredArrow.homMk c hw :
    CostructuredArrow.mk (Y := U) (a ≫ f.hom) ⟶ CostructuredArrow.mk (Y := V) b)

/-- **Enlarging the big fppf site preserves properties étale local on source and target.** -/
theorem holdsOnEveryEtaleChart_changeBigSite_map {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : HoldsOnEveryEtaleChart B S hS P f.hom) :
    HoldsOnEveryEtaleChart B' S (largerContains h hS) P
      ((changeBigSite B B' h S hS).map f).hom :=
  (holdsOnEveryEtaleChart_iff_surjectiveChart B' S (largerContains h hS) P hP
    ((changeBigSite B B' h S hS).obj X).property ((changeBigSite B B' h S hS).obj Y).property
    _).mpr (changeBigSite_holdsOnSurjectiveEtaleChart B B' h S hS f P hf)

/-- **A property étale local on source and target holds for `G f` exactly when it holds for
`f`.** -/
theorem holdsOnEveryEtaleChart_changeBigSite_map_iff {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    HoldsOnEveryEtaleChart B' S (largerContains h hS) P
        ((changeBigSite B B' h S hS).map f).hom ↔
      HoldsOnEveryEtaleChart B S hS P f.hom :=
  ⟨holdsOnEveryEtaleChart_of_changeBigSite_map B B' h S hS P f,
    holdsOnEveryEtaleChart_changeBigSite_map B B' h S hS hP f⟩

/-! ### Properties of represented base changes -/

/-- **Enlarging the big fppf site preserves the properties of represented base changes**, for a
property `P` of morphisms of schemes stable under base change and fppf local on the target, and
a morphism whose transport is representable. -/
theorem presheaf_changeBigSite_map (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)) f.hom)
    (hrep : yoneda.relativelyRepresentable ((changeBigSite B B' h S hS).map f).hom) :
    MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B' S (largerContains h hS)))
      ((changeBigSite B B' h S hS).map f).hom := by
  let hS' : B'.Contains S := largerContains h hS
  obtain ⟨V, φ, hφS, hφE⟩ := Y.property.exists_atlas
  have hφE' : IsEtaleChart B S hS Y.obj (CostructuredArrow.mk φ) := hφE
  let φ' := (changeBigSiteChart B B' h S hS Y (CostructuredArrow.mk φ)).hom
  rw [presheaf_inverseImage_iff_atlas_snd B' S hS' P _ hrep _ φ'
    (presheaf_surjective_changeBigSiteChart B B' h S hS Y hφS hφE')
    (isEtaleChart_changeBigSiteChart B B' h S hS Y hφE')]
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact property_of_isPullback_of_isPullback B' S hS' (hrep.isPullback φ')
    (isPullback_changeBigSiteChart B B' h S hS f (hf.rep.fst φ) (hf.rep.snd φ) φ
      (hf.rep.isPullback φ)) (hf.property_snd φ)

/-! ### The diagonal -/

/-- The fibre product `X ×_Y X` of algebraic spaces, as an algebraic space. -/
noncomputable abbrev selfPullbackSpace {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    AlgebraicSpaces B S hS :=
  ⟨pullback f.hom f.hom,
    isAlgebraicSpace_pullback B S hS f.hom f.hom X.property X.property Y.property⟩

/-- The relative diagonal `X ⟶ X ×_Y X` of a morphism of algebraic spaces. -/
noncomputable abbrev diagonalSpace {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    X ⟶ selfPullbackSpace B S hS f :=
  ObjectProperty.homMk (pullback.diagonal f.hom)

/-- **The change of big site carries the relative diagonal to the relative diagonal.** Under
the identification of `G (X ×_Y X)` with `G X ×_{G Y} G X`, the transport of the diagonal of
`f` is the diagonal of `G f`. -/
theorem changeBigSite_map_diagonalSpace {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    ((changeBigSite B B' h S hS).map (diagonalSpace B S hS f)).hom ≫
        (isPullback_changeBigSite_map B B' h S hS
          (fst := (ObjectProperty.homMk (pullback.fst f.hom f.hom) :
            selfPullbackSpace B S hS f ⟶ X))
          (snd := (ObjectProperty.homMk (pullback.snd f.hom f.hom) :
            selfPullbackSpace B S hS f ⟶ X)) (f := f) (g := f)
          (IsPullback.of_hasPullback f.hom f.hom)).isoPullback.hom =
      pullback.diagonal ((changeBigSite B B' h S hS).map f).hom := by
  let G := changeBigSite B B' h S hS
  have hfst : diagonalSpace B S hS f ≫
      (ObjectProperty.homMk (pullback.fst f.hom f.hom) : selfPullbackSpace B S hS f ⟶ X) = 𝟙 X :=
    ObjectProperty.hom_ext _ (pullback.diagonal_fst f.hom)
  have hsnd : diagonalSpace B S hS f ≫
      (ObjectProperty.homMk (pullback.snd f.hom f.hom) : selfPullbackSpace B S hS f ⟶ X) = 𝟙 X :=
    ObjectProperty.hom_ext _ (pullback.diagonal_snd f.hom)
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.diagonal_fst,
      ← ObjectProperty.FullSubcategory.comp_hom, ← G.map_comp, hfst, G.map_id]
    rfl
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.diagonal_snd,
      ← ObjectProperty.FullSubcategory.comp_hom, ← G.map_comp, hsnd, G.map_id]
    rfl

/-! ### Quasi-compact and quasi-separated morphisms -/

/-- **Enlarging the big fppf site reflects quasi-compact morphisms.** -/
theorem isQuasiCompact_of_changeBigSite_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsQuasiCompact B' S (largerContains h hS) ((changeBigSite B B' h S hS).map f).hom) :
    IsQuasiCompact B S hS f.hom := by
  intro Z hZ hZqc g
  let Z' : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let P : AlgebraicSpaces B S hS :=
    ⟨pullback g f.hom, isAlgebraicSpace_pullback B S hS g f.hom hZ X.property Y.property⟩
  have hpb := isPullback_changeBigSite_map B B' h S hS
    (fst := (ObjectProperty.homMk (pullback.fst g f.hom) : P ⟶ Z'))
    (snd := (ObjectProperty.homMk (pullback.snd g f.hom) : P ⟶ X))
    (f := (ObjectProperty.homMk g : Z' ⟶ Y)) (g := f) (IsPullback.of_hasPullback g f.hom)
  exact isQuasiCompactSpace_of_changeBigSite_obj B B' h S hS (X := P)
    (isQuasiCompactSpace_of_iso B' S (largerContains h hS) hpb.isoPullback.symm
      (hf _ ((changeBigSite B B' h S hS).obj Z').property
        (isQuasiCompactSpace_changeBigSite_obj B B' h S hS (X := Z') hZqc)
        ((changeBigSite B B' h S hS).map (ObjectProperty.homMk g : Z' ⟶ Y)).hom))

/-- **Enlarging the big fppf site reflects quasi-separated morphisms.** -/
theorem isQuasiSeparated_of_changeBigSite_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsQuasiSeparated B' S (largerContains h hS) ((changeBigSite B B' h S hS).map f).hom) :
    IsQuasiSeparated B S hS f.hom :=
  isQuasiCompact_of_changeBigSite_map B B' h S hS (diagonalSpace B S hS f)
    (isQuasiCompact_of_isPullback B' S (largerContains h hS)
      (@IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ (IsIso.id _) (Iso.isIso_hom _)
        ⟨(Category.id_comp _).trans (changeBigSite_map_diagonalSpace B B' h S hS f).symm⟩) hf)

/-! ### Finite presentation -/

/-- **Enlarging the big fppf site reflects morphisms of finite presentation.** -/
theorem isFinitePresentation_of_changeBigSite_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFinitePresentation B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).map f).hom) :
    IsFinitePresentation B S hS f.hom :=
  ⟨holdsOnEveryEtaleChart_of_changeBigSite_map B B' h S hS _ f hf.1,
    isQuasiCompact_of_changeBigSite_map B B' h S hS f hf.2.1,
    isQuasiSeparated_of_changeBigSite_map B B' h S hS f hf.2.2⟩

/-- **Enlarging the big fppf site preserves morphisms of finite presentation between
quasi-compact quasi-separated algebraic spaces.** -/
theorem isFinitePresentation_changeBigSite_map (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hXqc : IsQuasiCompactSpace B S hS X.obj)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.obj)
    (hYqc : IsQuasiCompactSpace B S hS Y.obj)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.obj)
    (hf : IsFinitePresentation B S hS f.hom) :
    IsFinitePresentation B' S (largerContains h hS) ((changeBigSite B B' h S hS).map f).hom :=
  ⟨holdsOnEveryEtaleChart_changeBigSite_map B B' h S hS
      isEtaleLocalOnSourceAndTarget_locallyOfFinitePresentation f hf.1,
    isQuasiCompact_of_isQuasiCompactSpace B' S (largerContains h hS) (largerContains h hZ)
      ((changeBigSite B B' h S hS).obj Y).property
      (isAbsolutelyQuasiSeparated_changeBigSite_obj B B' h S hS hZ hYqc hYqs)
      (isQuasiCompactSpace_changeBigSite_obj B B' h S hS hXqc) _,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B' S (largerContains h hS)
      (largerContains h hZ) ((changeBigSite B B' h S hS).obj X).property
      (isAbsolutelyQuasiSeparated_changeBigSite_obj B B' h S hS hZ hXqc hXqs) _⟩

/-! ### Separated morphisms -/

/-- A property of represented base changes holds for the transported diagonal of `f` if and only
if it holds for the diagonal of the transport of `f`. -/
private theorem presheaf_changeBigSite_map_diagonalSpace_iff (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B' S (largerContains h hS)))
        ((changeBigSite B B' h S hS).map (diagonalSpace B S hS f)).hom ↔
      MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B' S (largerContains h hS)))
        (pullback.diagonal ((changeBigSite B B' h S hS).map f).hom) := by
  let e := (isPullback_changeBigSite_map B B' h S hS
    (fst := (ObjectProperty.homMk (pullback.fst f.hom f.hom) : selfPullbackSpace B S hS f ⟶ X))
    (snd := (ObjectProperty.homMk (pullback.snd f.hom f.hom) : selfPullbackSpace B S hS f ⟶ X))
    (f := f) (g := f) (IsPullback.of_hasPullback f.hom f.hom)).isoPullback
  have hcomp := changeBigSite_map_diagonalSpace B B' h S hS f
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rw [← hcomp]
    exact @MorphismProperty.RespectsIso.postcomp _ _ _ (MorphismProperty.relative_respectsIso _)
      _ _ _ e.hom (Iso.isIso_hom e) _ hd
  · rw [(Iso.eq_comp_inv e).mpr hcomp]
    exact @MorphismProperty.RespectsIso.postcomp _ _ _ (MorphismProperty.relative_respectsIso _)
      _ _ _ e.inv (Iso.isIso_inv e) _ hd

/-- **Enlarging the big fppf site reflects separated morphisms.** -/
theorem isSeparated_of_changeBigSite_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsSeparated B' S (largerContains h hS) ((changeBigSite B B' h S hS).map f).hom) :
    IsSeparated B S hS f.hom :=
  presheaf_of_presheaf_changeBigSite_map B B' h S hS _ (diagonalSpace B S hS f)
    (Stacks.SeparationLocal.relativelyRepresentable_diagonal B S hS X.property f.hom)
    ((presheaf_changeBigSite_map_diagonalSpace_iff B B' h S hS _ f).mpr hf)

/-- **Enlarging the big fppf site preserves separated morphisms.** -/
theorem isSeparated_changeBigSite_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsSeparated B S hS f.hom) :
    IsSeparated B' S (largerContains h hS) ((changeBigSite B B' h S hS).map f).hom := by
  have := Stacks.Descent.isLocalAtTarget_fppfPrecoverage
    (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})
  let e := (isPullback_changeBigSite_map B B' h S hS
    (fst := (ObjectProperty.homMk (pullback.fst f.hom f.hom) : selfPullbackSpace B S hS f ⟶ X))
    (snd := (ObjectProperty.homMk (pullback.snd f.hom f.hom) : selfPullbackSpace B S hS f ⟶ X))
    (f := f) (g := f) (IsPullback.of_hasPullback f.hom f.hom)).isoPullback
  have hrep : yoneda.relativelyRepresentable
      ((changeBigSite B B' h S hS).map (diagonalSpace B S hS f)).hom := by
    rw [(Iso.eq_comp_inv e).mpr (changeBigSite_map_diagonalSpace B B' h S hS f)]
    exact @MorphismProperty.RespectsIso.postcomp _ _ _
      (Functor.relativelyRepresentable.respectsIso _) _ _ _ e.inv (Iso.isIso_inv e) _
      (Stacks.SeparationLocal.relativelyRepresentable_diagonal B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).property _)
  exact (presheaf_changeBigSite_map_diagonalSpace_iff B B' h S hS _ f).mp
    (presheaf_changeBigSite_map B B' h S hS
      (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})
      (diagonalSpace B S hS f) hf hrep)

/-- **Separatedness of a morphism of algebraic spaces is invariant under enlarging the big fppf
site.** -/
theorem isSeparated_changeBigSite_map_iff {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    IsSeparated B' S (largerContains h hS) ((changeBigSite B B' h S hS).map f).hom ↔
      IsSeparated B S hS f.hom :=
  ⟨isSeparated_of_changeBigSite_map B B' h S hS f, isSeparated_changeBigSite_map B B' h S hS f⟩

end AlgebraicGeometry.Space

end
