module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The Cohen–Macaulay locus of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over a scheme `S` which is locally of
finite presentation. The set of points of `X` at which `f` is Cohen–Macaulay is open, and it
commutes with arbitrary base change: the Cohen–Macaulay locus of `X ×_Y Y' ⟶ Y'` is the
inverse image of the Cohen–Macaulay locus of `f` under the projection to `X`.

## Main results

* `AlgebraicGeometry.Space.isOpen_setOf_isCohenMacaulayAt`: **Stacks 0E10**, openness of the
  Cohen–Macaulay locus.
* `AlgebraicGeometry.Space.isCohenMacaulayAt_pullback_locus`: **Stacks 0E10**, the behaviour of
  the Cohen–Macaulay locus under base change.

## Implementation notes

Both statements are transported from their scheme-level counterparts of Tag 045U along étale
charts, through the presentation of Tag 0E0V
(`AlgebraicGeometry.Space.exists_etale_presentation_cohenMacaulayLocus`) and the comparison
`AlgebraicGeometry.Space.isCohenMacaulayAt_yoneda_iff` of the pointed-chart condition with the
scheme-level condition of Tag 045R.

For openness, the locus on a surjective étale chart of the source is the inverse image of the
locus on `X`, and it is open because the chart presents `f` by a flat morphism of the site
locally of finite presentation. An étale morphism of presheaves is open on points (Tag 03BX),
so the locus on `X`, being the image of the locus on the chart under a surjection, is open.

For base change the four corners of the square are charted compatibly (Tag 02X1), so that the
chart of `X ×_Y Y'` is the fibre product of the charts of `X` and `Y'` over the chart of `Y`.
The scheme-level base-change statement applies to the *canonical* pullback of the charts, so
the compatible chart has to be moved across the canonical isomorphism of the two pullbacks.
That move is an instance of the transfer of Cohen–Macaulayness of a morphism of schemes at a
point across an arbitrary étale square, which is in turn the étale locality on source and
target of the germ-level fibre condition of Tag 0E0U.

## References

* [Stacks Project, Tag 045U](https://stacks.math.columbia.edu/tag/045U)
* [Stacks Project, Tag 0E10](https://stacks.math.columbia.edu/tag/0E10)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Two germ morphisms induced by equal morphisms of schemes at the same point agree. -/
private theorem MorphismOfGerms.ofSchemeHomOfEq_congr {X Y : Scheme.{u}} {m n : X ⟶ Y}
    (hmn : m = n) (x : X) (y : Y) (hm : m x = y) (hn : n x = y) :
    MorphismOfGerms.ofSchemeHomOfEq m x y hm =
      MorphismOfGerms.ofSchemeHomOfEq n x y hn := by
  cases hmn
  rfl

/-- The fibre local ring condition of Tag 0E0U on a germ morphism induced by a morphism of
schemes does not depend on how the image point is presented. -/
private theorem hasCohenMacaulayFiberLocalRing_ofSchemeHomOfEq_iff {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (y : Y) (hxy : f x = y) :
    HasCohenMacaulayFiberLocalRing (MorphismOfGerms.ofSchemeHomOfEq f x y hxy) ↔
      HasCohenMacaulayFiberLocalRing (MorphismOfGerms.ofSchemeHom f x) := by
  cases hxy
  rfl

/-- **The fibre local ring condition of Tag 0E0U transfers across an étale square of
schemes.** In a commuting square `a ≫ h = h' ≫ b` of morphisms of schemes with `a` and `b`
étale, the germ morphism of `h` at the image of a point of the source of `h'` satisfies the
Cohen–Macaulay fibre local ring condition if and only if the germ morphism of `h'` at that
point does.

This is the étale locality of the condition on source and target (Tag 0E0U), applied to the
square of germ morphisms induced by the given one. -/
private theorem hasCohenMacaulayFiberLocalRing_iff_of_etale_square {U' U V' V : Scheme.{u}}
    (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V) (ha : Etale a) (hb : Etale b)
    (hsq : a ≫ h = h' ≫ b) (x' : U') :
    HasCohenMacaulayFiberLocalRing (MorphismOfGerms.ofSchemeHom h (a x')) ↔
      HasCohenMacaulayFiberLocalRing (MorphismOfGerms.ofSchemeHom h' x') := by
  have hy : h (a x') = b (h' x') := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : U' ⟶ V => k x') hsq
  refine (hasCohenMacaulayFiberLocalRing_ofSchemeHomOfEq_iff h (a x') (b (h' x')) hy).symm.trans
    (hasCohenMacaulayFiberLocalRing_isEtaleLocalOnSourceAndTarget.iff_of_etale_square
      (MorphismOfGerms.ofSchemeHom a x') (MorphismOfGerms.ofSchemeHom b (h' x'))
      (MorphismOfGerms.ofSchemeHom h' x')
      (MorphismOfGerms.ofSchemeHomOfEq h (a x') (b (h' x')) hy)
      (MorphismOfGerms.isEtale_ofSchemeHomOfEq _ _ _ _ ha)
      (MorphismOfGerms.isEtale_ofSchemeHomOfEq _ _ _ _ hb) ?_)
  rw [MorphismOfGerms.ofSchemeHomOfEq_comp, MorphismOfGerms.ofSchemeHomOfEq_comp]
  exact MorphismOfGerms.ofSchemeHomOfEq_congr hsq.symm _ _ _ _

/-- **Cohen–Macaulayness of a morphism of schemes transfers across an étale square.** In a
commuting square `a ≫ h = h' ≫ b` of morphisms of schemes with `a` and `b` étale and `h`,
`h'` flat with locally Noetherian fibres, `h` is Cohen–Macaulay at the image of a point of the
source of `h'` if and only if `h'` is Cohen–Macaulay at that point.

Both flatness conjuncts hold outright, so only the fibre conditions have to be compared, and
that comparison is the étale locality of Tag 0E0U. -/
@[ega "IV 18.4.11" "(iii)"]
private theorem schemeIsCohenMacaulayAt_iff_of_etale_square {U' U V' V : Scheme.{u}}
    (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V) (ha : Etale a) (hb : Etale b)
    [Flat h] [Flat h'] (hf : ∀ y : V, IsLocallyNoetherian (h.fiber y))
    (hf' : ∀ y' : V', IsLocallyNoetherian (h'.fiber y'))
    (hsq : a ≫ h = h' ≫ b) (x' : U') :
    h.IsCohenMacaulayAt hf (a x') ↔ h'.IsCohenMacaulayAt hf' x' := by
  rw [Scheme.Hom.isCohenMacaulayAt_iff_germ, Scheme.Hom.isCohenMacaulayAt_iff_germ]
  have hgerm := hasCohenMacaulayFiberLocalRing_iff_of_etale_square a b h' h ha hb hsq x'
  exact ⟨fun hcm => ⟨Flat.stalkMap h' x', hgerm.mp hcm.2⟩,
    fun hcm => ⟨Flat.stalkMap h (a x'), hgerm.mpr hcm.2⟩⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **Stacks 0E10.** The Cohen–Macaulay locus of a flat morphism of algebraic spaces over `S`
which is locally of finite presentation is open in the canonical topology of Tag 03BX on the
point space of its source. -/
@[stacks 0E10 "openness of the Cohen–Macaulay locus", ega "IV 12.1.1" "(vi), F = O_X"]
theorem isOpen_setOf_isCohenMacaulayAt {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf_flat : IsFlat B S hS f) (hf_lfp : IsLocallyOfFinitePresentation B S hS f) :
    IsOpen {x : points B S hS X | IsCohenMacaulayAt B S hS f x} := by
  obtain ⟨V, q, hq_surjective, hq_etale⟩ := hY.exists_atlas
  obtain ⟨U, p, h, -, hp_surjective, hp_etale, hh_flat, hh_lfp, hlocus⟩ :=
    exists_etale_presentation_cohenMacaulayLocus B S hS hX hY f hf_flat hf_lfp V q
      hq_surjective hq_etale
  have : Flat ((BigFppfOver.toScheme B S hS).map h) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Flat.isEtaleLocalOnSourceAndTarget h).mp hh_flat
  have : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget h).mp hh_lfp
  have hsurjective : Function.Surjective (pointsMap B S hS (yoneda.obj U) p) :=
    (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hp_surjective
  have himage : pointsMap B S hS (yoneda.obj U) p ''
      {z : points B S hS (yoneda.obj U) | IsCohenMacaulayAt B S hS (yoneda.map h) z} =
      {x : points B S hS X | IsCohenMacaulayAt B S hS f x} := by
    rw [hlocus, Set.image_preimage_eq _ hsurjective]
  rw [← himage]
  exact isOpenMap_pointsMap_of_presheafEtale B S hS p hp_etale _
    (isOpen_setOf_isCohenMacaulayAt_yoneda B S hS U V h)

/-- **Stacks 0E10.** The Cohen–Macaulay locus of a flat morphism of algebraic spaces over `S`
which is locally of finite presentation commutes with arbitrary base change: the locus of the
base change `X ×_Y Y' ⟶ Y'` is the inverse image of the locus of `f : X ⟶ Y` under the
projection to `X`. -/
@[stacks 0E10 "base change of the Cohen–Macaulay locus", ega "IV 6.8.2" "(ii)"]
theorem isCohenMacaulayAt_pullback_locus {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hf_flat : IsFlat B S hS f.hom)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    {x' : points B S hS (pullback f.hom g.hom) |
        IsCohenMacaulayAt B S hS (pullback.snd f.hom g.hom) x'} =
      pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom) ⁻¹'
        {x : points B S hS X.1 | IsCohenMacaulayAt B S hS f.hom x} := by
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
      IsCohenMacaulayAt B S hS (pullback.snd f.hom g.hom)
          (pointsMap B S hS (yoneda.obj U') c (t.class B S hS (yoneda.obj U'))) ↔
        IsCohenMacaulayAt B S hS f.hom
          (pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom)
            (pointsMap B S hS (yoneda.obj U') c (t.class B S hS (yoneda.obj U')))) := by
    let z := schemePoint B S hS U' t
    let tU := FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) t
    -- Transfer from the base change to its chart, then to schemes.
    have hchart' := isCohenMacaulayAt_chart_iff B S hS (pullback.snd f.hom g.hom) U' V' c qY'
      pV' hc_etale hqY' hcommF' t (IsLocalRing.closedPoint t.carrier)
    have hscheme' := isCohenMacaulayAt_yoneda_iff B S hS U' V' pV' hfP' t
    -- Transfer from `f` to its chart, then to schemes.
    have hchart := isCohenMacaulayAt_chart_iff B S hS f.hom U V pX v p hpX hv_etale
      hcommF.symm tU (IsLocalRing.closedPoint tU.carrier)
    have hscheme := isCohenMacaulayAt_yoneda_iff B S hS U V p hfP tU
    -- The scheme-level base change of Tag 045U, read on the compatible chart square.
    have hiso := schemeIsCohenMacaulayAt_iff_of_etale_square e.hom (𝟙 _) (T.map pV')
      (pullback.snd (T.map p) (T.map q)) inferInstance inferInstance hfC hfP'
      (by simpa using hesnd) z
    have hbase := _root_.AlgebraicGeometry.isCohenMacaulayAt_pullback_locus
      (T.map p) (T.map q)
    have hbaseAt : (pullback.snd (T.map p) (T.map q)).IsCohenMacaulayAt hfC (e.hom z) ↔
        (T.map p).IsCohenMacaulayAt hfP (pullback.fst (T.map p) (T.map q) (e.hom z)) := by
      simpa using congrArg (fun W : Set _ => e.hom z ∈ W) hbase
    have hprojPoint : pullback.fst (T.map p) (T.map q) (e.hom z) = T.map pU z := by
      rw [← Scheme.Hom.comp_apply, hefst]
    have hschemePoint : schemePoint B S hS U tU = T.map pU z :=
      schemePoint_map_yoneda B S hS pU t
    have hTransfer : (T.map pV').IsCohenMacaulayAt hfP' z ↔
        (T.map p).IsCohenMacaulayAt hfP (schemePoint B S hS U tU) := by
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

end Space

end AlgebraicGeometry

end
