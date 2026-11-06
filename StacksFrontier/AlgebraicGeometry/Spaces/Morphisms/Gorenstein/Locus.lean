module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.BaseChangeLocus
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The Gorenstein locus of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over a scheme `S` which is locally of
finite presentation. The set
`W = {x ∈ |X| : f is Gorenstein at x}`
is open in `|X|`, and its formation commutes with arbitrary base change: for any `g : Y' ⟶ Y`,
the set `W'` attached to the base change `f' : X ×_Y Y' ⟶ Y'` is the inverse image of `W` under
the projection `g' : X ×_Y Y' ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.isOpen_setOf_isGorensteinAt`: **Stacks 0E19**, openness of the
  Gorenstein locus.
* `AlgebraicGeometry.Space.isGorensteinAt_pullback_locus`: **Stacks 0E19**, the behaviour of the
  Gorenstein locus under base change.

The two together state the source lemma: the point set is the one of Tag 03BU, carrying the
topology of Tag 03BX, and the base change is the presheaf fibre product with its second
projection, so that `g'` is the first projection and `(g')^{-1}` is a preimage along the induced
map on points.

## Implementation notes

Both halves are the scheme-level statements of Tags 0C09 and 0E0Q transported along étale charts,
exactly as the source reduces to the morphism `U ⟶ V` in a commuting square of charts. The
comparison of the chart condition with the scheme condition is
`AlgebraicGeometry.Space.isGorensteinAt_chart_iff` and, in the represented case,
`AlgebraicGeometry.Space.isGorensteinAt_yoneda_iff`, both of Tag 0E15; local Noetherianity of
the fibres of a chart morphism is automatic from its local finite presentation, so the Noetherian
condition of Tag 0E14 costs nothing here.

For openness the source is presented by a surjective étale chart lying over a chart of the target
(Tag 02X1), whose presenting morphism of the site is again flat and locally of finite presentation
because flatness and local finite presentation of a morphism of algebraic spaces are chart
conditions. On that chart the locus is the preimage of the locus on `X`, and it is open by Tag
0C09. Since an étale morphism of presheaves is open on points (Tag 03BX) and the chart is
surjective on points, the locus on `X` is the image of an open set under an open map.

For base change the four corners of the square are charted compatibly, so that the chart of
`X ×_Y Y'` is a fibre product of the charts of `X` and of `Y'` over the chart of `Y`. Tag 0E0Q
applies to the *canonical* pullback of the two chart morphisms, so the compatible chart is moved
across the canonical isomorphism of the two pullbacks; that move is an instance of the invariance
of Gorensteinness at a point under restriction along open immersions, an isomorphism being one.

## References

* [Stacks Project, Tag 0E19](https://stacks.math.columbia.edu/tag/0E19)
* [Stacks Project, Tag 0C09](https://stacks.math.columbia.edu/tag/0C09)
* [Stacks Project, Tag 0E0Q](https://stacks.math.columbia.edu/tag/0E0Q)
* [Stacks Project, Tag 0E14](https://stacks.math.columbia.edu/tag/0E14)
* [Stacks Project, Tag 0E15](https://stacks.math.columbia.edu/tag/0E15)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_GorensteinLocus :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_GorensteinLocus
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_GorensteinLocus B S hS).has_limit _

/-- For a flat morphism of represented presheaves locally of finite presentation, the set of
points of the source at which it is Gorenstein is open in the canonical topology of Tag 03BX. -/
theorem isOpen_setOf_isGorensteinAt_yoneda (U V : BigFppfOver B S hS) (h : U ⟶ V)
    [Flat ((BigFppfOver.toScheme B S hS).map h)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h)] :
    IsOpen {u : points B S hS (yoneda.obj U) | IsGorensteinAt B S hS (yoneda.map h) u} := by
  let g := (BigFppfOver.toScheme B S hS).map h
  let hg : ∀ y : (BigFppfOver.toScheme B S hS).obj V, IsLocallyNoetherian (g.fiber y) :=
    fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation g y
  refine (isOpen_yoneda_iff_isSchemeOpen B S hS U _).mpr
    ⟨{z | g.IsGorensteinAt hg z}, Scheme.Hom.isOpen_setOf_isGorensteinAt g, fun p => ?_⟩
  exact isGorensteinAt_yoneda_iff B S hS U V h hg p

/-- **Stacks 0E19.** The Gorenstein locus of a flat morphism of algebraic spaces over `S` which
is locally of finite presentation is open in the canonical topology of Tag 03BX on the point
space of its source. -/
@[stacks 0E19 "openness of the Gorenstein locus"]
theorem isOpen_setOf_isGorensteinAt {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf_flat : IsFlat B S hS f) (hf_lfp : IsLocallyOfFinitePresentation B S hS f) :
    IsOpen {x : points B S hS X | IsGorensteinAt B S hS f x} := by
  obtain ⟨V, q, hq_surjective, hq_etale⟩ := hY.exists_atlas
  obtain ⟨U, p, h, hcomm, hp_surjective, hp_etale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hq_surjective hq_etale
  have : Flat ((BigFppfOver.toScheme B S hS).map h) :=
    hf_flat U V p q h hp_etale hq_etale hcomm.symm
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h) :=
    hf_lfp U V p q h hp_etale hq_etale hcomm.symm
  have hfib : ∀ y : (BigFppfOver.toScheme B S hS).obj V,
      IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map h).fiber y) :=
    fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _ y
  have hsurjective : Function.Surjective (pointsMap B S hS (yoneda.obj U) p) :=
    (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hp_surjective
  have hpreimage :
      {z : points B S hS (yoneda.obj U) | IsGorensteinAt B S hS (yoneda.map h) z} =
      pointsMap B S hS (yoneda.obj U) p ⁻¹'
        {x : points B S hS X | IsGorensteinAt B S hS f x} := by
    refine Set.ext fun z => ?_
    induction z using Quot.ind with
    | _ t =>
      exact isGorensteinAt_chart_iff B S hS f U V p q h hp_etale hq_etale hcomm hfib t
        (IsLocalRing.closedPoint t.carrier)
  have himage : pointsMap B S hS (yoneda.obj U) p ''
      {z : points B S hS (yoneda.obj U) | IsGorensteinAt B S hS (yoneda.map h) z} =
      {x : points B S hS X | IsGorensteinAt B S hS f x} := by
    rw [hpreimage, Set.image_preimage_eq _ hsurjective]
  rw [← himage]
  exact isOpenMap_pointsMap_of_presheafEtale B S hS p hp_etale _
    (isOpen_setOf_isGorensteinAt_yoneda B S hS U V h)

/-- **Stacks 0E19.** The Gorenstein locus of a flat morphism of algebraic spaces over `S` which
is locally of finite presentation commutes with arbitrary base change: the locus of the base
change `X ×_Y Y' ⟶ Y'` is the inverse image of the locus of `f : X ⟶ Y` under the projection
to `X`. -/
@[stacks 0E19 "base change of the Gorenstein locus"]
theorem isGorensteinAt_pullback_locus {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hf_flat : IsFlat B S hS f.hom)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    {x' : points B S hS (pullback f.hom g.hom) |
        IsGorensteinAt B S hS (pullback.snd f.hom g.hom) x'} =
      pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom) ⁻¹'
        {x : points B S hS X.1 | IsGorensteinAt B S hS f.hom x} := by
  let T := BigFppfOver.toScheme B S hS
  let E := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  have : E.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have : E.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have : E.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition E
  have : E.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange E
  obtain ⟨U, V, U', V', p, q, pU, pV', v, a, b, c, hsquare, havp, -, hcfst, hcsnd,
      -, hv_etale, -, ha_etale, -, hb_etale, hc_surjective, hc_etale⟩ :=
    exists_compatible_etale_charts B S hS f g
  -- The charts of the source and of the base change, read as charts over `v`.
  let pX := a ≫ pullback.snd v f.hom
  let qY' := b ≫ pullback.snd v g.hom
  have hcommF : yoneda.map p ≫ v = pX ≫ f.hom := by
    calc
      yoneda.map p ≫ v = (a ≫ pullback.fst v f.hom) ≫ v := by rw [havp]
      _ = a ≫ pullback.snd v f.hom ≫ f.hom := by
        simp only [Category.assoc, pullback.condition]
      _ = pX ≫ f.hom := by simp only [pX, Category.assoc]
  have hcommF' : c ≫ pullback.snd f.hom g.hom = yoneda.map pV' ≫ qY' := by
    simpa only [qY', Category.assoc] using hcsnd
  have hpX : E.presheaf pX :=
    MorphismProperty.comp_mem E.presheaf _ _ ha_etale
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback v f.hom) hv_etale)
  have hqY' : E.presheaf qY' :=
    MorphismProperty.comp_mem E.presheaf _ _ hb_etale
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback v g.hom) hv_etale)
  -- The presenting morphism of schemes and its base change along the chart of `Y'`.
  have : Flat (T.map p) := hf_flat U V pX v p hpX hv_etale hcommF
  have : LocallyOfFinitePresentation (T.map p) := hf_lfp U V pX v p hpX hv_etale hcommF
  have : Flat (T.map pV') :=
    Flat.isStableUnderBaseChange.of_isPullback hsquare inferInstance
  have : LocallyOfFinitePresentation (T.map pV') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsquare inferInstance
  let hfP := fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (T.map p) y
  let hfP' := fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (T.map pV') y
  have : Flat (pullback.snd (T.map p) (T.map q)) :=
    Flat.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (T.map p) (T.map q)) inferInstance
  have : LocallyOfFinitePresentation (pullback.snd (T.map p) (T.map q)) := inferInstance
  let hfC := fun y =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation
      (pullback.snd (T.map p) (T.map q)) y
  -- The compatible chart square is the canonical pullback of schemes, up to isomorphism.
  let e := hsquare.isoIsPullback _ _ (IsPullback.of_hasPullback (T.map p) (T.map q))
  have hefst : e.hom ≫ pullback.fst (T.map p) (T.map q) = T.map pU :=
    hsquare.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback (T.map p) (T.map q))
  have hesnd : e.hom ≫ pullback.snd (T.map p) (T.map q) = T.map pV' :=
    hsquare.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback (T.map p) (T.map q))
  have hSpace := isAlgebraicSpace_pullback B S hS f.hom g.hom X.property Y'.property Y.property
  -- The pointwise statement on the chart of the base change.
  have hpointwise (t : FieldValuedPoint B S hS (yoneda.obj U')) :
      IsGorensteinAt B S hS (pullback.snd f.hom g.hom)
          (pointsMap B S hS (yoneda.obj U') c (t.class B S hS (yoneda.obj U'))) ↔
        IsGorensteinAt B S hS f.hom
          (pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom)
            (pointsMap B S hS (yoneda.obj U') c (t.class B S hS (yoneda.obj U')))) := by
    let z := schemePoint B S hS U' t
    let tU := FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) t
    -- Transfer from the base change to its chart, then to schemes.
    have hchart' := isGorensteinAt_chart_iff B S hS (pullback.snd f.hom g.hom) U' V' c qY'
      pV' hc_etale hqY' hcommF' hfP' t (IsLocalRing.closedPoint t.carrier)
    have hscheme' := isGorensteinAt_yoneda_iff B S hS U' V' pV' hfP' t
    -- Transfer from `f` to its chart, then to schemes.
    have hchart := isGorensteinAt_chart_iff B S hS f.hom U V pX v p hpX hv_etale
      hcommF.symm hfP tU (IsLocalRing.closedPoint tU.carrier)
    have hscheme := isGorensteinAt_yoneda_iff B S hS U V p hfP tU
    -- The scheme-level base change of Tag 0E0Q, read on the compatible chart square.
    have hif : ∀ y, IsLocallyNoetherian
        ((e.hom ≫ pullback.snd (T.map p) (T.map q)).fiber y) := by
      rw [hesnd]; exact hfP'
    have hiso : Scheme.Hom.IsGorensteinAt (pullback.snd (T.map p) (T.map q)) hfC (e.hom z) ↔
        Scheme.Hom.IsGorensteinAt (T.map pV') hfP' z :=
      Scheme.Hom.isGorensteinAt_iff_of_comp_eq e.hom (𝟙 _)
        (pullback.snd (T.map p) (T.map q)) (T.map pV') (by simpa using hesnd) hfC hfP' hif z
    have hbase := Scheme.Hom.setOf_isGorensteinAt_pullback_eq_preimage_of_locallyOfFiniteType
      (T.map p) (T.map q)
    have hbaseAt :
        Scheme.Hom.IsGorensteinAt (pullback.snd (T.map p) (T.map q)) hfC (e.hom z) ↔
        Scheme.Hom.IsGorensteinAt (T.map p) hfP
          (pullback.fst (T.map p) (T.map q) (e.hom z)) := by
      simpa using congrArg (fun W : Set _ => e.hom z ∈ W) hbase
    have hprojPoint : pullback.fst (T.map p) (T.map q) (e.hom z) = T.map pU z := by
      rw [← Scheme.Hom.comp_apply, hefst]
    have hschemePoint : schemePoint B S hS U tU = T.map pU z :=
      schemePoint_map_yoneda B S hS pU t
    have hTransfer : Scheme.Hom.IsGorensteinAt (T.map pV') hfP' z ↔
        Scheme.Hom.IsGorensteinAt (T.map p) hfP (schemePoint B S hS U tU) := by
      rw [hschemePoint, ← hprojPoint]
      exact hiso.symm.trans hbaseAt
    -- The two chart projections agree on points.
    have hPointTransfer :
        pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom)
            (pointsMap B S hS (yoneda.obj U') c (t.class B S hS (yoneda.obj U'))) =
          pointsMap B S hS (yoneda.obj U) pX (tU.class B S hS (yoneda.obj U)) := by
      have harrow : c ≫ pullback.fst f.hom g.hom = yoneda.map pU ≫ pX := by
        simpa only [pX, Category.assoc] using hcfst
      rw [← pointsMap_comp_apply, harrow, pointsMap_comp_apply]
      rfl
    rw [hPointTransfer]
    exact hchart'.symm.trans (hscheme'.trans (hTransfer.trans (hscheme.symm.trans hchart)))
  have hcPoints : Function.Surjective (pointsMap B S hS (yoneda.obj U') c) :=
    (surjective_iff_surjective_pointsMap B S hS (pullback f.hom g.hom) hSpace U' c).mp
      hc_surjective
  refine Set.ext fun x' => ?_
  obtain ⟨w, rfl⟩ := hcPoints x'
  obtain ⟨t, rfl⟩ := Quot.exists_rep w
  exact hpointwise t

end AlgebraicGeometry.Space

end
