module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology

/-!
# Cohen–Macaulay morphisms of algebraic spaces, read on étale charts

Cohen–Macaulayness of a morphism of algebraic spaces at a point of its source is a
pointed-chart condition, so it can be computed on any one pointed étale chart. Two
consequences are recorded: the condition at a point is unchanged when the morphism is
replaced by the morphism of charts in a commuting square of étale charts, and for a morphism
between represented presheaves it is exactly Cohen–Macaulayness of the underlying morphism of
schemes at the corresponding scheme point.

## Main results

* `AlgebraicGeometry.MorphismOfGerms.isFlat_ofSchemeHom` is flatness of the germ morphism
  induced by a flat morphism of schemes.
* `AlgebraicGeometry.Scheme.Hom.isCohenMacaulayAt_iff_germ` reads Cohen–Macaulayness of a
  morphism of schemes at a point off the induced morphism of germs.
* `AlgebraicGeometry.Space.isCohenMacaulayAt_chart_iff` transfers the condition between a
  morphism of algebraic spaces and the morphism of charts presenting it.
* `AlgebraicGeometry.Space.isCohenMacaulayAt_yoneda_iff` identifies the condition on a
  morphism of represented presheaves with the scheme-level condition of Tag 045R.
* `AlgebraicGeometry.Space.isOpen_setOf_isCohenMacaulayAt_yoneda` is openness of the
  Cohen–Macaulay locus of a flat morphism of represented presheaves locally of finite
  presentation.

## References

* [Stacks Project, Tag 045R](https://stacks.math.columbia.edu/tag/045R)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 0E0V](https://stacks.math.columbia.edu/tag/0E0V)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The morphism of germs induced by a flat morphism of schemes at a point of its source is
flat on local rings. -/
theorem MorphismOfGerms.isFlat_ofSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X) :
    MorphismOfGerms.IsFlat (MorphismOfGerms.ofSchemeHom f x) := by
  exact ⟨⟨⊤, by simp, X.topIso.hom ≫ f, rfl⟩, rfl, Flat.stalkMap (X.topIso.hom ≫ f) _⟩

/-- Cohen–Macaulayness of a morphism of schemes with locally Noetherian fibres at a point of
its source is flatness there together with the fibre local ring condition on the induced
morphism of germs. -/
theorem Scheme.Hom.isCohenMacaulayAt_iff_germ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) (x : X) :
    f.IsCohenMacaulayAt hf x ↔
      IsFlatAt f.toLRSHom.toShHom x ∧
        HasCohenMacaulayFiberLocalRing (MorphismOfGerms.ofSchemeHom f x) := by
  have : IsLocallyNoetherian (f.fiber (f x)) := hf (f x)
  rw [hasCohenMacaulayFiberLocalRing_ofSchemeHom_iff_of_isNoetherianRing]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Cohen–Macaulayness at a point is flatness and the fibre condition on the germ morphism of
any one pointed étale chart. -/
private theorem isCohenMacaulayAt_iff_of_chart {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (x : points B S hS F) (c : EtaleChartAtPoint B S hS f x) :
    IsCohenMacaulayAt B S hS f x ↔
      MorphismOfGerms.IsFlat (MorphismOfGerms.ofSchemeHom
        ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)) ∧
      HasCohenMacaulayFiberLocalRing (MorphismOfGerms.ofSchemeHom
        ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)) :=
  (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS (@MorphismOfGerms.IsFlat.{u})
    MorphismOfGerms.isEtaleLocalOnSourceAndTarget_isFlat f x c).and
    (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS (@HasCohenMacaulayFiberLocalRing.{u})
      hasCohenMacaulayFiberLocalRing_isEtaleLocalOnSourceAndTarget f x c)

/-- Cohen–Macaulayness at a point is unchanged on passing between a morphism of algebraic
spaces and the morphism of charts in a commuting square of étale charts over it. -/
theorem isCohenMacaulayAt_chart_iff
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (comm : a ≫ f = yoneda.map h ≫ b)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) (t : Spec (.of p.carrier)) :
    IsCohenMacaulayAt B S hS (yoneda.map h) (p.class B S hS (yoneda.obj U)) ↔
      IsCohenMacaulayAt B S hS f
        (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) := by
  let cf : EtaleChartAtPoint B S hS f
      (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) :=
    { U := U, V := V, a := a, b := b, h := h, a_etale := ha, b_etale := hb
      comm := comm.symm, representative := p, point := t, maps_to := rfl }
  exact (isCohenMacaulayAt_iff_of_chart B S hS _ _ (etaleChartAtPointOfId B S hS U V h p t)).trans
    (isCohenMacaulayAt_iff_of_chart B S hS _ _ cf).symm

/-- For a morphism of represented presheaves which is flat and has locally Noetherian fibres,
Cohen–Macaulayness at a point of the source is Cohen–Macaulayness of the underlying morphism
of schemes at the corresponding scheme point. -/
theorem isCohenMacaulayAt_yoneda_iff (U V : BigFppfOver B S hS) (h : U ⟶ V)
    [Flat ((BigFppfOver.toScheme B S hS).map h)]
    (hf : ∀ y : (BigFppfOver.toScheme B S hS).obj V,
      IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map h).fiber y))
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    IsCohenMacaulayAt B S hS (yoneda.map h) (p.class B S hS (yoneda.obj U)) ↔
      ((BigFppfOver.toScheme B S hS).map h).IsCohenMacaulayAt hf
        (schemePoint B S hS U p) := by
  let g := (BigFppfOver.toScheme B S hS).map h
  let z := schemePoint B S hS U p
  let c := etaleChartAtPointOfId B S hS U V h p (IsLocalRing.closedPoint p.carrier)
  have hsource : c.sourcePoint B S hS = z := rfl
  rw [isCohenMacaulayAt_iff_of_chart B S hS _ _ c, hsource, Scheme.Hom.isCohenMacaulayAt_iff_germ]
  exact and_congr (iff_of_true (MorphismOfGerms.isFlat_ofSchemeHom g z) (Flat.stalkMap g z))
    Iff.rfl

/-- For a flat morphism of represented presheaves locally of finite presentation, the set of
points of the source at which it is Cohen–Macaulay is open in the canonical topology of
Tag 03BX. -/
theorem isOpen_setOf_isCohenMacaulayAt_yoneda (U V : BigFppfOver B S hS) (h : U ⟶ V)
    [Flat ((BigFppfOver.toScheme B S hS).map h)]
    [LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map h)] :
    letI := pointTopology B S hS (yoneda.obj U)
    IsOpen {u : points B S hS (yoneda.obj U) |
      IsCohenMacaulayAt B S hS (yoneda.map h) u} := by
  let g := (BigFppfOver.toScheme B S hS).map h
  let hf : ∀ y : (BigFppfOver.toScheme B S hS).obj V, IsLocallyNoetherian (g.fiber y) :=
    fun y ↦ isLocallyNoetherian_fiber_of_locallyOfFinitePresentation g y
  exact (isOpen_yoneda_iff_isSchemeOpen B S hS U _).mpr ⟨{z | g.IsCohenMacaulayAt hf z},
    isOpen_setOf_isCohenMacaulayAt g, fun p ↦ isCohenMacaulayAt_yoneda_iff B S hS U V h hf p⟩

end Space

end AlgebraicGeometry

end
