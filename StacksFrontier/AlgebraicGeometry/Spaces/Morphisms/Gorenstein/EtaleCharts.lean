module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.EtaleLocalList
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Fibres
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.BaseChange

/-!
# Gorenstein morphisms of algebraic spaces and étale charts of the target

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose fibres are locally Noetherian.
Then `f` is Gorenstein exactly when it is flat and the fibres of its base change to one,
equivalently to every, étale scheme chart of `Y` are Gorenstein algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.HasGorensteinFibersOnChart` is Gorensteinness of the fibres over the
  points of one étale scheme chart of the target.

## Main results

* `AlgebraicGeometry.Space.isGorensteinAt_chart_iff`: Gorensteinness at a point is unchanged on
  passing between a morphism of algebraic spaces and the morphism of charts in a commuting
  square of étale charts over it.
* `AlgebraicGeometry.Space.isGorensteinAt_yoneda_iff`: for a morphism of represented presheaves
  with locally Noetherian fibres, Gorensteinness at a point of the source is Gorensteinness of
  the underlying morphism of schemes at the corresponding scheme point.
* `AlgebraicGeometry.Space.isGorenstein_yoneda_map_iff`: for a morphism of represented
  presheaves with locally Noetherian fibres, Gorensteinness is flatness together with
  Gorensteinness of all scheme-theoretic fibres.
* `AlgebraicGeometry.Space.isGorenstein_tfae_etaleCharts`: **Stacks 0E15**, the three equivalent
  conditions.

## Implementation notes

Gorensteinness of schemes is local for the étale topology,
`AlgebraicGeometry.isGorenstein_isLocal_etale`, which is item (5) of Remark 03E7 and is taken
from `StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.EtaleLocalList`. This is the only
place where the Gorenstein case cannot reuse the Cohen–Macaulay route of Tag 036B, which goes
through syntomic locality.

Everything generic in the Cohen–Macaulay case, Tag 0E0W, is reused rather than repeated: the
fibre at a field-valued point of the target, the local Noetherianity hypothesis
`AlgebraicGeometry.Space.HasLocallyNoetherianFibers`, the comparison of the fibre over a chart
point with the scheme-theoretic fibre of a chart square
(`AlgebraicGeometry.Space.hasEtaleLocalProperty_fiberAt_iff`), and the existence of a surjective
étale scheme chart of the base change presented over the target chart. The three conditions then
reduce to Tag 0C05 for the morphism of schemes presenting the square, through the chart
description of Gorensteinness of Tag 0E14 recorded as
`AlgebraicGeometry.Space.isGorensteinAt_iff_chart`.

Unlike the Cohen–Macaulay case, the passage between a morphism of represented presheaves and the
underlying morphism of schemes needs no standing flatness hypothesis: flatness is one of the two
conjuncts of `AlgebraicGeometry.Space.IsGorensteinAt` and is transported by the chart criterion
along with the fibre condition.

## References

* [Stacks Project, Tag 0E15](https://stacks.math.columbia.edu/tag/0E15)
* [Stacks Project, Tag 0C05](https://stacks.math.columbia.edu/tag/0C05)
* [Stacks Project, Tag 0E13](https://stacks.math.columbia.edu/tag/0E13)
* [Stacks Project, Tag 0E14](https://stacks.math.columbia.edu/tag/0E14)
* [Stacks Project, Tag 0E0W](https://stacks.math.columbia.edu/tag/0E0W)
* [Stacks Project, Tag 034C](https://stacks.math.columbia.edu/tag/034C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0E15.** The fibres of `f` over the points of the étale scheme chart
`g : h_V ⟶ Y` are Gorenstein algebraic spaces. -/
abbrev HasGorensteinFibersOnChart (f : X ⟶ Y) (V : BigFppfOver B S hS)
    (g : yoneda.obj V ⟶ Y) : Prop :=
  ∀ (v : V.left.1) (hv : B.Contains (Spec (.of (V.left.1.residueField v)))),
    FiberHasEtaleLocalProperty B S hS f
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsGorenstein T)
      (chartResidueFieldPoint B S hS V g v hv)

/-! ### Charts of a morphism of algebraic spaces -/

/-- Gorensteinness at a point is unchanged on passing between a morphism of algebraic spaces and
the morphism of charts in a commuting square of étale charts over it. -/
theorem isGorensteinAt_chart_iff (f : X ⟶ Y)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (comm : a ≫ f = yoneda.map h ≫ b)
    (hc : ∀ y : (BigFppfOver.toScheme B S hS).obj V,
      IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map h).fiber y))
    (p : FieldValuedPoint B S hS (yoneda.obj U)) (t : Spec (.of p.carrier)) :
    IsGorensteinAt B S hS (yoneda.map h) (p.class B S hS (yoneda.obj U)) ↔
      IsGorensteinAt B S hS f
        (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) := by
  let cf : EtaleChartAtPoint B S hS f
      (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) :=
    { U := U, V := V, a := a, b := b, h := h, a_etale := ha, b_etale := hb
      comm := comm.symm, representative := p, point := t, maps_to := rfl }
  exact (isGorensteinAt_iff_chart B S hS (yoneda.map h) _
      (etaleChartAtPointOfId B S hS U V h p t) hc).trans
    (isGorensteinAt_iff_chart B S hS f _ cf hc).symm

/-- For a morphism of represented presheaves with locally Noetherian fibres, Gorensteinness at a
point of the source is Gorensteinness of the underlying morphism of schemes at the corresponding
scheme point. -/
theorem isGorensteinAt_yoneda_iff (U V : BigFppfOver B S hS) (h : U ⟶ V)
    (hf : ∀ y : (BigFppfOver.toScheme B S hS).obj V,
      IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map h).fiber y))
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    IsGorensteinAt B S hS (yoneda.map h) (p.class B S hS (yoneda.obj U)) ↔
      Scheme.Hom.IsGorensteinAt ((BigFppfOver.toScheme B S hS).map h) hf
        (schemePoint B S hS U p) :=
  isGorensteinAt_iff_chart B S hS (yoneda.map h) _
    (etaleChartAtPointOfId B S hS U V h p (IsLocalRing.closedPoint p.carrier)) hf

/-- For a morphism of represented presheaves with locally Noetherian fibres, Gorensteinness is
flatness of the underlying morphism of schemes together with Gorensteinness of all of its
scheme-theoretic fibres. -/
theorem isGorenstein_yoneda_map_iff (U V : BigFppfOver B S hS) (h : U ⟶ V)
    (hf : ∀ y : (BigFppfOver.toScheme B S hS).obj V,
      IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map h).fiber y)) :
    IsGorenstein B S hS (yoneda.map h) ↔
      Flat ((BigFppfOver.toScheme B S hS).map h) ∧
        ∀ y : (BigFppfOver.toScheme B S hS).obj V,
          _root_.AlgebraicGeometry.IsGorenstein
            (((BigFppfOver.toScheme B S hS).map h).fiber y) := by
  have key (x : (BigFppfOver.toScheme B S hS).obj U) :
      IsGorensteinAt B S hS (yoneda.map h)
        ((schemePointRepresentative B S hS U x).class B S hS (yoneda.obj U)) ↔
      Scheme.Hom.IsGorensteinAt ((BigFppfOver.toScheme B S hS).map h) hf x := by
    have hiff := isGorensteinAt_yoneda_iff B S hS U V h hf
      (schemePointRepresentative B S hS U x)
    rwa [schemePointRepresentative_point B S hS U x] at hiff
  refine ⟨fun hg => (Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber _ hf).mp
    fun x => (key x).mp (hg _), fun hg z => Quot.inductionOn z fun p => ?_⟩
  have h1 := (key ((BigFppfOver.toScheme B S hS).map p.value
    (IsLocalRing.closedPoint p.carrier))).mpr
    ((Scheme.Hom.isGorenstein_iff_flat_and_isGorenstein_fiber _ hf).mpr hg _)
  rwa [schemePointRepresentative_class B S hS U p] at h1

/-! ### The equivalent conditions -/

/-- A Gorenstein morphism of algebraic spaces is flat. -/
theorem isFlat_of_isGorenstein (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hg : IsGorenstein B S hS f) :
    IsFlat B S hS f :=
  ((isFlat_tfae B S hS hX hY f).out 2 1).mp fun x => (hg x).1

/-- An étale scheme chart `g` of the target carries a surjective étale scheme chart of the base
change along `g`, presented over a morphism of schemes `h` with locally Noetherian fibres whose
scheme-theoretic fibres are Gorenstein exactly when the fibres of `f` over `g` are. -/
private theorem exists_chart_hasGorensteinFibersOnChart_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : HasLocallyNoetherianFibers B S hS f)
    (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y) (hg : IsEtale B S hS g) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ pullback f g) (h : U ⟶ V),
      a ≫ pullback.snd f g = yoneda.map h ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      (∀ v : (BigFppfOver.toScheme B S hS).obj V,
        IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map h).fiber v)) ∧
      (HasGorensteinFibersOnChart B S hS f V g ↔
        ∀ v : (BigFppfOver.toScheme B S hS).obj V,
          _root_.AlgebraicGeometry.IsGorenstein
            (((BigFppfOver.toScheme B S hS).map h).fiber v)) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (a ≫ pullback.fst f g) ∧
      (a ≫ pullback.fst f g) ≫ f = yoneda.map h ≫ g := by
  obtain ⟨U, a, h, comm, haSurjective, haEtale⟩ :=
    exists_surjective_etale_atlas_over_chart B S hS hX hY f V g
  have key (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
      (v : (BigFppfOver.toScheme B S hS).obj V)
      (hv : B.Contains (Spec (.of (V.left.1.residueField v)))) :=
    hasEtaleLocalProperty_fiberAt_iff B S hS hX hY f V g U a h comm haSurjective haEtale P v hv
  refine ⟨U, a, h, comm, haSurjective, haEtale, fun v => ?_, ?_, ?_, ?_⟩
  · exact (key _ v (B.residueField_spec_contains V.left.2 v)).mp
      (hf V g hg v (B.residueField_spec_contains V.left.2 v))
  · exact ⟨fun hchart v => (key _ v (B.residueField_spec_contains V.left.2 v)).mp
      (hchart v (B.residueField_spec_contains V.left.2 v)),
      fun hscheme v hv => (key _ v hv).mpr (hscheme v)⟩
  · exact chartSource_property B S hS (@Etale.{u}) Etale.etale_isStableUnderBaseChange.{u}
      etale_isStableUnderComposition.{u} f V g ((isEtale_iff_presheaf_of_yoneda B S hS g).mp hg)
      U a haEtale
  · rw [Category.assoc, pullback.condition, ← Category.assoc, comm]

/-- **Stacks 0E15.** For a morphism of algebraic spaces over `S` with locally Noetherian fibres,
Gorensteinness is equivalent to flatness together with Gorensteinness of the fibres after some,
equivalently after every, étale scheme chart of the target. -/
@[stacks 0E15 "global_gorenstein_equivalence"]
theorem isGorenstein_tfae_etaleCharts (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : HasLocallyNoetherianFibers B S hS f) :
    List.TFAE [
      IsGorenstein B S hS f,
      IsFlat B S hS f ∧
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))) g ∧
          IsEtale B S hS g ∧ HasGorensteinFibersOnChart B S hS f V g,
      IsFlat B S hS f ∧
        ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
          IsEtale B S hS g → HasGorensteinFibersOnChart B S hS f V g] := by
  tfae_have 1 → 3 := by
    intro hgor
    refine ⟨isFlat_of_isGorenstein B S hS hX hY f hgor, fun V g hg => ?_⟩
    obtain ⟨U, a, h, comm, haSurjective, haEtale, hfib, hequiv, hpEtale, hpcomm⟩ :=
      exists_chart_hasGorensteinFibersOnChart_iff B S hS hX hY f hf V g hg
    have hgEtale := (isEtale_iff_presheaf_of_yoneda B S hS g).mp hg
    refine hequiv.mpr (((isGorenstein_yoneda_map_iff B S hS U V h hfib).mp ?_).2)
    exact fun z => Quot.inductionOn z fun t => (isGorensteinAt_chart_iff B S hS f U V
      (a ≫ pullback.fst f g) g h hpEtale hgEtale hpcomm hfib t
      (IsLocalRing.closedPoint t.carrier)).mpr (hgor _)
  tfae_have 3 → 2 := by
    rintro ⟨hflat, hcharts⟩
    obtain ⟨V, g, hgSurjective, hgEtale⟩ := hY.exists_atlas
    have hg : IsEtale B S hS g := (isEtale_iff_presheaf_of_yoneda B S hS g).mpr hgEtale
    exact ⟨hflat, V, g, hgSurjective, hg, hcharts V g hg⟩
  tfae_have 2 → 1 := by
    rintro ⟨hflat, V, g, hgSurjective, hg, hchart⟩
    obtain ⟨U, a, h, comm, haSurjective, haEtale, hfib, hequiv, hpEtale, hpcomm⟩ :=
      exists_chart_hasGorensteinFibersOnChart_iff B S hS hX hY f hf V g hg
    have hgEtale := (isEtale_iff_presheaf_of_yoneda B S hS g).mp hg
    have hpSurjective := chartSource_property B S hS (@Surjective.{u}) inferInstance
      surjective_isStableUnderComposition.{u} f V g hgSurjective U a haSurjective
    have hflatChart : Flat ((BigFppfOver.toScheme B S hS).map h) :=
      flat_chart_of_isFlat B S hS f hflat U V (a ≫ pullback.fst f g) g h hpEtale hgEtale
        hpcomm.symm
    have hgorChart : IsGorenstein B S hS (yoneda.map h) :=
      (isGorenstein_yoneda_map_iff B S hS U V h hfib).mpr ⟨hflatChart, hequiv.mp hchart⟩
    intro x
    obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U
      (a ≫ pullback.fst f g)).mp hpSurjective x
    rw [← hz]
    exact Quot.inductionOn z fun t => (isGorensteinAt_chart_iff B S hS f U V
      (a ≫ pullback.fst f g) g h hpEtale hgEtale hpcomm hfib t
      (IsLocalRing.closedPoint t.carrier)).mp (hgorChart _)
  tfae_finish

end Space

end AlgebraicGeometry

end
