module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart

/-!
# Reading the dimension of the local ring of a fibre off a single étale chart

The first of the three invariants of Stacks 04NM, the dimension of the local ring of the fibre
at a point of a morphism of algebraic spaces, is defined in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeDimensionAtPoint.lean` as the condition that the
germ property of Tag 04NJ hold in *every* pointed pair of étale charts at the point. This file
turns that quantifier into a numerical equation read off one chart, exactly as
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeDimensionChart.lean` does for the relative
dimension of Tag 04NL.

## Main results

* `AlgebraicGeometry.MorphismOfGerms.ringKrullDim_stalk_fiber_eq_of_agreeNear`: the Krull
  dimension of the local ring of the fibre of a representative at the distinguished point
  depends only on the germ of that representative, and
  `AlgebraicGeometry.hasFiberLocalRingDimension_iff_of_rep`,
  `AlgebraicGeometry.hasFiberLocalRingDimension_ofSchemeHom_iff` read the property of Tag 04NJ
  off an arbitrary, respectively the canonical, representative.
* `AlgebraicGeometry.Space.hasFiberLocalRingDimension_iff_of_chart` and
  `AlgebraicGeometry.Space.hasFiberLocalRingDimension_pointsMap_iff` are the chart equations for
  the dimension of the local ring of the fibre at a point of a morphism of algebraic spaces.

## Implementation notes

The square lemma `AlgebraicGeometry.ringKrullDim_stalk_fiber_eq_of_etale_square` is imported
from `StacksFrontier/AlgebraicGeometry/Descent/Germs/FiberLocalRingDimension.lean`. Its proof is
the composite of two facts about the morphism of fibres induced by the square: it is étale
(Tag 04NI, `AlgebraicGeometry.etale_fiberMap`), and an étale morphism preserves the Krull
dimension of local rings (Tag 04N8, `AlgebraicGeometry.ringKrullDim_stalk_eq_of_etale`).

`AlgebraicGeometry.HasFiberLocalRingDimension` is an existential over representatives of the
germ, so reading it off one representative needs invariance under
`AlgebraicGeometry.MorphismOfGerms.Representative.AgreeNear`; that is the square lemma applied
twice, with the inclusion of a common smaller neighbourhood as the étale vertical arrow on the
source and the identity on the target.

Chart independence at the level of the space is Tag 04NC
(`AlgebraicGeometry.Space.chart_property_iff_of_pointedCharts`), which needs no
algebraic-space hypothesis; the hypotheses `hF` and `hG` appear only because they are recorded
in the definition of `AlgebraicGeometry.Space.HasFiberLocalRingDimension`, following the source.
The second equation indexes the point of the space by a point of the source chart through the
comparison bijection `AlgebraicGeometry.Space.pointsEquivScheme` of Tag 03BX clause (1); this is
the form a localisation argument on a chart consumes. The pointed chart built from a
field-valued point of the source chart is
`AlgebraicGeometry.Space.EtaleChartAtPoint.ofFieldValuedPoint`, reused from the Tag 04NL file.

## References

* [Stacks Project, Tag 04N8](https://stacks.math.columbia.edu/tag/04N8)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04NI](https://stacks.math.columbia.edu/tag/04NI)
* [Stacks Project, Tag 04NJ](https://stacks.math.columbia.edu/tag/04NJ)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Precomposing with an étale morphism does not change the Krull dimension of the local ring of
the fibre. -/
private theorem ringKrullDim_stalk_fiber_comp_etale {X' X Y : Scheme.{u}} (g : X' ⟶ X) [Etale g]
    (f : X ⟶ Y) (x' : X') :
    ringKrullDim (((g ≫ f).fiber ((g ≫ f) x')).presheaf.stalk ((g ≫ f).asFiber x')) =
      ringKrullDim ((f.fiber (f (g x'))).presheaf.stalk (f.asFiber (g x'))) :=
  ringKrullDim_stalk_fiber_eq_of_etale_square (g ≫ f) g (𝟙 Y) f (by simp) x'

namespace MorphismOfGerms

/-- The Krull dimension of the local ring of the fibre of a representative of a morphism of
germs at the distinguished point depends only on the morphism of germs: two representatives
which agree near the distinguished point give the same value. -/
public theorem ringKrullDim_stalk_fiber_eq_of_agreeNear {X Y : GermOfScheme.{u}}
    (r s : Representative X Y) (hrs : r.AgreeNear s) :
    ringKrullDim ((r.hom.fiber (r.hom ⟨X.point, r.mem_source⟩)).presheaf.stalk
        (r.hom.asFiber ⟨X.point, r.mem_source⟩)) =
      ringKrullDim ((s.hom.fiber (s.hom ⟨X.point, s.mem_source⟩)).presheaf.stalk
        (s.hom.asFiber ⟨X.point, s.mem_source⟩)) := by
  obtain ⟨W, hxW, hWr, hWs, heq⟩ := hrs
  have key (t : Representative X Y) (hWt : W ≤ t.source) :
      ringKrullDim
          (((X.scheme.homOfLE hWt ≫ t.hom).fiber
            ((X.scheme.homOfLE hWt ≫ t.hom) ⟨X.point, hxW⟩)).presheaf.stalk
            ((X.scheme.homOfLE hWt ≫ t.hom).asFiber ⟨X.point, hxW⟩)) =
        ringKrullDim ((t.hom.fiber (t.hom ⟨X.point, t.mem_source⟩)).presheaf.stalk
          (t.hom.asFiber ⟨X.point, t.mem_source⟩)) := by
    have hetale : Etale (X.scheme.homOfLE hWt) :=
      HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities
    have hpt : X.scheme.homOfLE hWt ⟨X.point, hxW⟩ = ⟨X.point, t.mem_source⟩ :=
      Subtype.ext (by simp)
    rw [ringKrullDim_stalk_fiber_comp_etale (X.scheme.homOfLE hWt) t.hom ⟨X.point, hxW⟩, hpt]
  rw [← key r hWr, ← key s hWs, heq]

end MorphismOfGerms

/-- The property of Tag 04NJ read off an arbitrary representative: the local ring of the fibre
of a morphism of germs at the distinguished point has dimension `d` exactly when the one of a
chosen representative does. -/
public theorem hasFiberLocalRingDimension_iff_of_rep {X Y : GermOfScheme.{u}} (d : ℕ∞)
    {f : MorphismOfGerms X Y} (r : MorphismOfGerms.Representative X Y)
    (hr : MorphismOfGerms.mk r = f) :
    HasFiberLocalRingDimension d f ↔
      ringKrullDim ((r.hom.fiber (r.hom ⟨X.point, r.mem_source⟩)).presheaf.stalk
        (r.hom.asFiber ⟨X.point, r.mem_source⟩)) = (d : WithBot ℕ∞) := by
  refine ⟨fun hd ↦ ?_, fun hd ↦ ⟨r, hr, hd⟩⟩
  obtain ⟨s, hs, hsd⟩ := hd
  exact (MorphismOfGerms.ringKrullDim_stalk_fiber_eq_of_agreeNear s r
    (MorphismOfGerms.mk_eq_mk_iff.mp (hs.trans hr.symm))).symm.trans hsd

/-- The property of Tag 04NJ for the germ morphism induced by a morphism of schemes at a point
is the equation on the Krull dimension of the local ring of the fibre of that morphism of
schemes. -/
public theorem hasFiberLocalRingDimension_ofSchemeHom_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (d : ℕ∞) :
    HasFiberLocalRingDimension d (MorphismOfGerms.ofSchemeHom f x) ↔
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) = (d : WithBot ℕ∞) := by
  have hpt : X.topIso.hom (⟨x, by simp⟩ : (⊤ : X.Opens)) = x := by simp
  have hrep : MorphismOfGerms.mk
      ({ source := ⊤
         mem_source := by simp
         hom := X.topIso.hom ≫ f
         map_point := by change f x = f x; rfl } :
        MorphismOfGerms.Representative ⟨X, x⟩ ⟨Y, f x⟩) =
      MorphismOfGerms.ofSchemeHom f x := rfl
  rw [hasFiberLocalRingDimension_iff_of_rep d _ hrep,
    ringKrullDim_stalk_fiber_comp_etale X.topIso.hom f (⟨x, by simp⟩ : (⊤ : X.Opens)), hpt]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The chart equation for Tag 04NM, dimension of the local ring of a fibre.** The local ring
of the fibre of a morphism of algebraic spaces at a point has dimension `d` exactly when the
local ring of the fibre of the chart morphism of one pointed étale chart has dimension `d` at
the chart point. -/
theorem hasFiberLocalRingDimension_iff_of_chart (d : ℕ∞)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (x : points B S hS F) (c : EtaleChartAtPoint B S hS f x) :
    HasFiberLocalRingDimension d B S hS hF hG f x ↔
      ringKrullDim ((((BigFppfOver.toScheme B S hS).map c.h).fiber
            ((BigFppfOver.toScheme B S hS).map c.h (c.sourcePoint B S hS))).presheaf.stalk
          (((BigFppfOver.toScheme B S hS).map c.h).asFiber (c.sourcePoint B S hS))) =
        (d : WithBot ℕ∞) := by
  rw [← hasFiberLocalRingDimension_ofSchemeHom_iff
    ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) d]
  exact ⟨fun hall ↦ hall c, fun hc d' ↦ (chart_property_iff_of_pointedCharts B S hS
    (@_root_.AlgebraicGeometry.HasFiberLocalRingDimension.{u} d)
    (fiberLocalRingDimension_isEtaleLocalOnSourceAndTarget d) f x c d').mp hc⟩

/-- **The chart equation for Tag 04NM at a point of the chart.** For a commuting square of
étale charts and a point `u` of the source chart, the local ring of the fibre of the morphism of
algebraic spaces at the point of the space below `u` has dimension `d` exactly when the local
ring of the fibre of the chart morphism at `u` does. -/
theorem hasFiberLocalRingDimension_pointsMap_iff (d : ℕ∞)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map h ≫ b = a ≫ f)
    (u : (BigFppfOver.toScheme B S hS).obj U) :
    HasFiberLocalRingDimension d B S hS hF hG f
        (pointsMap B S hS (yoneda.obj U) a ((pointsEquivScheme B S hS U).symm u)) ↔
      ringKrullDim ((((BigFppfOver.toScheme B S hS).map h).fiber
            ((BigFppfOver.toScheme B S hS).map h u)).presheaf.stalk
          (((BigFppfOver.toScheme B S hS).map h).asFiber u)) = (d : WithBot ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS U u
  have hclass : (pointsEquivScheme B S hS U).symm u = p.class B S hS (yoneda.obj U) :=
    (pointsEquivScheme B S hS U).symm_apply_eq.mpr hp.symm
  rw [hclass, hasFiberLocalRingDimension_iff_of_chart B S hS d hF hG f _
    (EtaleChartAtPoint.ofFieldValuedPoint B S hS f U V a b h ha hb hcomm p),
    EtaleChartAtPoint.sourcePoint_ofFieldValuedPoint, hp]
  exact Iff.rfl

end Space

end AlgebraicGeometry

end
