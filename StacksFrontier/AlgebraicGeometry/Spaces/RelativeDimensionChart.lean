module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionAtPoint

/-!
# Reading the relative dimension at a point off a single étale chart

The relative dimension of a morphism of algebraic spaces at a point of its source is defined
in `StacksFrontier/AlgebraicGeometry/Spaces/RelativeDimensionAtPoint.lean` as the condition that
the germ property of Tag 04NL hold in *every* pointed pair of étale charts at the point. That
definition is a quantifier over charts and over representatives of a germ, and a client with
one concrete chart square in hand cannot use it directly. This file turns it into a numerical
equation: the relative dimension at `x` is `d` exactly when the local dimension of the fibre
of the chart morphism at the chart point is `d`, for one chart.

## Main definitions

* `AlgebraicGeometry.Space.EtaleChartAtPoint.ofFieldValuedPoint` builds the pointed chart
  determined by an étale chart square together with a field-valued point of the source chart.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_etale_square`: in a commutative square
  of schemes with étale vertical arrows, the two horizontal arrows have fibres of the same
  local dimension at corresponding points.
* `AlgebraicGeometry.MorphismOfGerms.topologicalKrullDimAt_fiber_eq_of_agreeNear`: the local
  dimension of the fibre at the distinguished point depends only on the germ of a
  representative, and
  `AlgebraicGeometry.hasFiberDimensionAt_iff_of_rep`,
  `AlgebraicGeometry.hasFiberDimensionAt_ofSchemeHom_iff` read the property of Tag 04NL off
  an arbitrary, respectively the canonical, representative.
* `AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_of_chart` and
  `AlgebraicGeometry.Space.hasRelativeDimensionAt_pointsMap_iff` are the chart equations for
  the relative dimension at a point of a morphism of algebraic spaces.

## Implementation notes

The square lemma is the fibre-dimension analogue of the stalk-dimension statement proved
inside `StacksFrontier/AlgebraicGeometry/Descent/Germs/FiberLocalRingDimension.lean`: the
morphism of fibres induced by the square is étale (Tag 04NI,
`AlgebraicGeometry.etale_fiberMap`), and an étale morphism preserves the local Krull dimension
(Tag 04N4, `AlgebraicGeometry.topologicalKrullDimAt_eq_of_etale`). It is stated here publicly
because both the germ-invariance statement and the two chart equations need it, and the
corresponding statement in the tag 04NL file is private.

`AlgebraicGeometry.HasFiberDimensionAt` is an existential over representatives of the germ, so
reading it off one representative needs invariance under
`AlgebraicGeometry.MorphismOfGerms.Representative.AgreeNear`; that is the square lemma applied
twice, with the inclusion of a common smaller neighbourhood as the étale vertical arrow on the
source and the identity on the target.

Chart independence at the level of the space is Tag 04NC
(`AlgebraicGeometry.Space.chart_property_iff_of_pointedCharts`), which needs no
algebraic-space hypothesis, so neither chart equation assumes one. The second equation indexes
the point of the space by a point of the source chart through the comparison bijection
`AlgebraicGeometry.Space.pointsEquivScheme` of Tag 03BX clause (1); this is the form a
localisation argument on a chart consumes.

## References

* [Stacks Project, Tag 04NB](https://stacks.math.columbia.edu/tag/04NB)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04NI](https://stacks.math.columbia.edu/tag/04NI)
* [Stacks Project, Tag 04NL](https://stacks.math.columbia.edu/tag/04NL)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Transporting a point of a fibre along an equality of base points does not change its image
in the ambient scheme. -/
public theorem fiberι_cast_pt {X Y : Scheme.{u}} (f : X ⟶ Y) {y z : Y} (e : y = z)
    (p : f.fiber y) : f.fiberι z (e ▸ p) = f.fiberι y p := by
  cases e
  rfl

/-- Transporting a point of a fibre along an equality of base points does not change the local
dimension of the fibre there. -/
private theorem fiberDim_cast_pt {X Y : Scheme.{u}} (f : X ⟶ Y) {y z : Y} (e : y = z)
    (p : f.fiber y) :
    topologicalKrullDimAt (f.fiber z) (e ▸ p) = topologicalKrullDimAt (f.fiber y) p := by
  cases e
  rfl

/-- In a commutative square of schemes whose vertical arrows are étale, the fibre of the top
arrow at a point of its source has the same local dimension as the fibre of the bottom arrow
at the image of that point. -/
public theorem topologicalKrullDimAt_fiber_eq_of_etale_square {U' U V' V : Scheme.{u}}
    (f' : U' ⟶ V') (g' : U' ⟶ U) (g : V' ⟶ V) (f : U ⟶ V) [Etale g'] [Etale g]
    (h : g' ≫ f = f' ≫ g) (x' : U') :
    topologicalKrullDimAt (f'.fiber (f' x')) (f'.asFiber x') =
      topologicalKrullDimAt (f.fiber (f (g' x'))) (f.asFiber (g' x')) := by
  have hg : g (f' x') = f (g' x') := by
    simpa [Scheme.Hom.comp_apply] using (congrArg (fun q : U' ⟶ V => q x') h).symm
  let fm := fiberMap f' g' g f h (f' x')
  have : Etale fm :=
    @etale_fiberMap U' U V' V f' g' g f h (f' x') inferInstance inferInstance
  have hp : hg ▸ fm (f'.asFiber x') = f.asFiber (g' x') := by
    apply (f.fiberι (f (g' x'))).isEmbedding.injective
    calc
      f.fiberι (f (g' x')) (hg ▸ fm (f'.asFiber x')) =
          f.fiberι (g (f' x')) (fm (f'.asFiber x')) := fiberι_cast_pt f hg _
      _ = g' x' := by
        simpa using congrArg (fun q => q (f'.asFiber x')) (fiberMap_fiberι f' g' g f h (f' x'))
      _ = f.fiberι (f (g' x')) (f.asFiber (g' x')) := by simp
  calc
    topologicalKrullDimAt (f'.fiber (f' x')) (f'.asFiber x') =
        topologicalKrullDimAt (f.fiber (g (f' x'))) (fm (f'.asFiber x')) :=
      topologicalKrullDimAt_eq_of_etale fm (f'.asFiber x')
    _ = topologicalKrullDimAt (f.fiber (f (g' x'))) (hg ▸ fm (f'.asFiber x')) :=
      (fiberDim_cast_pt f hg _).symm
    _ = topologicalKrullDimAt (f.fiber (f (g' x'))) (f.asFiber (g' x')) := by rw [hp]

/-- Precomposing with an étale morphism does not change the local dimension of the fibre. -/
private theorem topologicalKrullDimAt_fiber_comp_etale {U' U V : Scheme.{u}} (g' : U' ⟶ U)
    (f : U ⟶ V) [Etale g'] (x' : U') :
    topologicalKrullDimAt ((g' ≫ f).fiber ((g' ≫ f) x')) ((g' ≫ f).asFiber x') =
      topologicalKrullDimAt (f.fiber (f (g' x'))) (f.asFiber (g' x')) :=
  topologicalKrullDimAt_fiber_eq_of_etale_square (g' ≫ f) g' (𝟙 V) f (by simp) x'

namespace MorphismOfGerms

/-- The local dimension of the fibre of a representative of a morphism of germs at the
distinguished point depends only on the morphism of germs: two representatives which agree
near the distinguished point give the same value. -/
public theorem topologicalKrullDimAt_fiber_eq_of_agreeNear {X Y : GermOfScheme.{u}}
    (r s : Representative X Y) (hrs : r.AgreeNear s) :
    topologicalKrullDimAt (r.hom.fiber (r.hom ⟨X.point, r.mem_source⟩))
        (r.hom.asFiber ⟨X.point, r.mem_source⟩) =
      topologicalKrullDimAt (s.hom.fiber (s.hom ⟨X.point, s.mem_source⟩))
        (s.hom.asFiber ⟨X.point, s.mem_source⟩) := by
  obtain ⟨W, hxW, hWr, hWs, heq⟩ := hrs
  have key (t : Representative X Y) (hWt : W ≤ t.source) :
      topologicalKrullDimAt
          (((X.scheme.homOfLE hWt ≫ t.hom).fiber
            ((X.scheme.homOfLE hWt ≫ t.hom) ⟨X.point, hxW⟩)))
          ((X.scheme.homOfLE hWt ≫ t.hom).asFiber ⟨X.point, hxW⟩) =
        topologicalKrullDimAt (t.hom.fiber (t.hom ⟨X.point, t.mem_source⟩))
          (t.hom.asFiber ⟨X.point, t.mem_source⟩) := by
    have hetale : Etale (X.scheme.homOfLE hWt) :=
      HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities
    have hpt : X.scheme.homOfLE hWt ⟨X.point, hxW⟩ = ⟨X.point, t.mem_source⟩ :=
      Subtype.ext (by simp)
    rw [topologicalKrullDimAt_fiber_comp_etale (X.scheme.homOfLE hWt) t.hom ⟨X.point, hxW⟩, hpt]
  rw [← key r hWr, ← key s hWs, heq]

end MorphismOfGerms

/-- The property of Tag 04NL read off an arbitrary representative: the fibre of a morphism of
germs has dimension `d` at the distinguished point exactly when one chosen representative
does. -/
public theorem hasFiberDimensionAt_iff_of_rep {X Y : GermOfScheme.{u}} (d : ℕ∞)
    {f : MorphismOfGerms X Y} (r : MorphismOfGerms.Representative X Y)
    (hr : MorphismOfGerms.mk r = f) :
    HasFiberDimensionAt d f ↔
      topologicalKrullDimAt (r.hom.fiber (r.hom ⟨X.point, r.mem_source⟩))
        (r.hom.asFiber ⟨X.point, r.mem_source⟩) = (d : WithBot ℕ∞) := by
  refine ⟨fun hd ↦ ?_, fun hd ↦ ⟨r, hr, hd⟩⟩
  obtain ⟨s, hs, hsd⟩ := hd
  exact (MorphismOfGerms.topologicalKrullDimAt_fiber_eq_of_agreeNear s r
    (MorphismOfGerms.mk_eq_mk_iff.mp (hs.trans hr.symm))).symm.trans hsd

/-- The property of Tag 04NL for the germ morphism induced by a morphism of schemes at a point
is the equation on the local dimension of the fibre of that morphism of schemes. -/
public theorem hasFiberDimensionAt_ofSchemeHom_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (d : ℕ∞) :
    HasFiberDimensionAt d (MorphismOfGerms.ofSchemeHom f x) ↔
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) := by
  have hpt : X.topIso.hom (⟨x, by simp⟩ : (⊤ : X.Opens)) = x := by simp
  have hrep : MorphismOfGerms.mk
      ({ source := ⊤
         mem_source := by simp
         hom := X.topIso.hom ≫ f
         map_point := rfl } :
        MorphismOfGerms.Representative ⟨X, x⟩ ⟨Y, f x⟩) =
      MorphismOfGerms.ofSchemeHom f x := rfl
  rw [hasFiberDimensionAt_iff_of_rep d _ hrep,
    topologicalKrullDimAt_fiber_comp_etale X.topIso.hom f (⟨x, by simp⟩ : (⊤ : X.Opens)), hpt]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The pointed étale chart at a point of an algebraic space determined by a commuting square
of étale charts together with a field-valued point of the source chart. The point of the space
is the image of the class of that field-valued point. -/
noncomputable def EtaleChartAtPoint.ofFieldValuedPoint (f : F ⟶ G)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    EtaleChartAtPoint B S hS f
      (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) where
  U := U
  V := V
  a := a
  b := b
  h := h
  a_etale := ha
  b_etale := hb
  comm := hcomm
  representative := p
  point := IsLocalRing.closedPoint p.carrier
  maps_to := rfl

/-- The chart point of `AlgebraicGeometry.Space.EtaleChartAtPoint.ofFieldValuedPoint` is the
scheme point underlying the chosen field-valued point. -/
theorem EtaleChartAtPoint.sourcePoint_ofFieldValuedPoint (f : F ⟶ G)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    (EtaleChartAtPoint.ofFieldValuedPoint B S hS f U V a b h ha hb hcomm p).sourcePoint
        B S hS = schemePoint B S hS U p :=
  rfl

/-- **The chart equation for Tag 04NM, relative dimension at a point.** The relative dimension
of a morphism of algebraic spaces at a point is `d` exactly when the fibre of the chart
morphism of one pointed étale chart has local dimension `d` at the chart point. -/
theorem hasRelativeDimensionAt_iff_of_chart (d : ℕ∞) (f : F ⟶ G) (x : points B S hS F)
    (c : EtaleChartAtPoint B S hS f x) :
    HasRelativeDimensionAt d B S hS f x ↔
      topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map c.h).fiber
            ((BigFppfOver.toScheme B S hS).map c.h (c.sourcePoint B S hS)))
          (((BigFppfOver.toScheme B S hS).map c.h).asFiber (c.sourcePoint B S hS)) =
        (d : WithBot ℕ∞) := by
  rw [← hasFiberDimensionAt_ofSchemeHom_iff
    ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) d]
  exact ⟨fun hall ↦ hall c, fun hc d' ↦
    (chart_property_iff_of_pointedCharts B S hS (@HasFiberDimensionAt.{u} d)
      (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d) f x c d').mp hc⟩

/-- **The chart equation for Tag 04NM at a point of the chart.** For a commuting square of
étale charts and a point `u` of the source chart, the relative dimension of the morphism of
algebraic spaces at the point of the space below `u` is `d` exactly when the fibre of the chart
morphism has local dimension `d` at `u`. -/
theorem hasRelativeDimensionAt_pointsMap_iff (d : ℕ∞) (f : F ⟶ G)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f)
    (u : (BigFppfOver.toScheme B S hS).obj U) :
    HasRelativeDimensionAt d B S hS f
        (pointsMap B S hS (yoneda.obj U) a ((pointsEquivScheme B S hS U).symm u)) ↔
      topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map h).fiber
            ((BigFppfOver.toScheme B S hS).map h u))
          (((BigFppfOver.toScheme B S hS).map h).asFiber u) = (d : WithBot ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS U u
  have hclass : (pointsEquivScheme B S hS U).symm u = p.class B S hS (yoneda.obj U) :=
    (pointsEquivScheme B S hS U).symm_apply_eq.mpr hp.symm
  rw [hclass, hasRelativeDimensionAt_iff_of_chart B S hS d f _
    (EtaleChartAtPoint.ofFieldValuedPoint B S hS f U V a b h ha hb hcomm p),
    EtaleChartAtPoint.sourcePoint_ofFieldValuedPoint, hp]
  exact Iff.rfl

end Space

end AlgebraicGeometry

end
