module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusOnBase

/-!
# Unramifiedness at a point, read off a commuting square of étale charts

`AlgebraicGeometry.Space.IsUnramifiedAt` (**Stacks 03ZH**, part (2)) is a condition on a
morphism of algebraic spaces at a point of its source, stated as the existence of an open
subspace of the source, having a point over the given one, on which the morphism is unramified.
What the chart constructions produce instead is `AlgebraicGeometry.UnramifiedAt` — Stacks 02G4
for a morphism of *schemes* — at a point of one étale chart. This file is the passage between
the two.

It is the mirror at unramifiedness of `AlgebraicGeometry.Space.isFlatAt_chart_iff` of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/FlatLocus.lean`, and it is proved the same way:
unramifiedness of morphisms of schemes is étale local on the source and target
(**Stacks 04R3**), so unramifiedness at a point of an algebraic space is the pointed-chart
condition of **Stacks 04NC** for the germ property that unramifiedness induces
(`AlgebraicGeometry.Space.isUnramifiedAt_iff_holdsOnEveryEtaleChartAtPoint`), and that condition
may be tested on any one pointed chart supplied as data
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_of_chart`). The commuting square of
étale charts given here *is* such a chart, its field-valued representative being the one the
point supplies, and the germ condition at it is unramifiedness of the morphism of charts at the
underlying scheme point by
`AlgebraicGeometry.unramifiedAt_iff_hasRepresentativeWithProperty'`.

`AlgebraicGeometry.Space.IsUnramifiedAt` is not, on its nose, in the
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChartAtPoint` shape that `isFlatAt_chart_iff`
exploits — `AlgebraicGeometry.Space.IsFlatAt` is *defined* as such a condition, whereas this one
is defined by an open subspace — but it is equivalent to it, which is all the argument needs.

## Main results

* `AlgebraicGeometry.Space.isUnramifiedAt_chart_iff`: unramifiedness of a morphism of algebraic
  spaces at the image of a field-valued point of a source chart is unramifiedness of the induced
  morphism of charts at the underlying scheme point.
* `AlgebraicGeometry.Space.isUnramifiedAt_pointsMap_chart_iff`: the same, at an arbitrary point
  of the source chart, with the scheme point taken through the comparison map of **Stacks 03BV**.
* `AlgebraicGeometry.Space.isUnramifiedAt_chartPoint_iff`: the same, at a point of the source
  chart scheme, which is the form the chart constructions consume.

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
* [Stacks Project, Tag 03ZH](https://stacks.math.columbia.edu/tag/03ZH)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 04RE](https://stacks.math.columbia.edu/tag/04RE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Unramifiedness at a point, read on a commuting square of étale charts.** Let `f : X ⟶ Y`
be a morphism of algebraic spaces over `S`, let `a : U ⟶ X` and `b : V ⟶ Y` be étale charts and
let `h : U ⟶ V` be a morphism of the site with `a ≫ f = h ≫ b`. Then `f` is unramified at the
point of `|X|` carried by a field-valued point `p` of `U` exactly when the morphism of schemes
underlying `h` is unramified at the scheme point underlying `p`.

Unramifiedness of morphisms of schemes is étale local on the source and the target
(**Stacks 04R3**), so unramifiedness at a point of an algebraic space is the pointed-chart
condition of **Stacks 04NC** for the germ property unramifiedness induces, by
`AlgebraicGeometry.Space.isUnramifiedAt_iff_holdsOnEveryEtaleChartAtPoint`; the given square,
pointed at `p` and at the closed point of its field spectrum, is one such chart, so
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_of_chart` tests the condition there,
and `AlgebraicGeometry.unramifiedAt_iff_hasRepresentativeWithProperty'` identifies the germ
condition with Stacks 02G4 for the morphism of charts. -/
theorem isUnramifiedAt_chart_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (comm : a ≫ f = yoneda.map h ≫ b)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    IsUnramifiedAt B S hS f
        (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) ↔
      _root_.AlgebraicGeometry.UnramifiedAt ((BigFppfOver.toScheme B S hS).map h)
        (schemePoint B S hS U p) := by
  have hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget
      (MorphismOfGerms.HasRepresentativeWithProperty
        (@_root_.AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})) :=
    MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget _
      _root_.AlgebraicGeometry.unramified_isEtaleLocalOnSourceAndTarget
  let c : EtaleChartAtPoint B S hS f
      (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) :=
    { U := U, V := V, a := a, b := b, h := h, a_etale := ha, b_etale := hb
      comm := comm.symm, representative := p
      point := IsLocalRing.closedPoint p.carrier, maps_to := rfl }
  rw [isUnramifiedAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hX hY f _,
    holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS _ hQ f _ c,
    ← _root_.AlgebraicGeometry.unramifiedAt_iff_hasRepresentativeWithProperty']
  exact Iff.rfl

/-- **Unramifiedness at a point, read on a commuting square of étale charts, at an arbitrary
point of the source chart.** The point of the chart scheme is taken through the comparison map
of **Stacks 03BV**, `AlgebraicGeometry.Space.pointsToScheme`.

Every point of a represented presheaf is the class of a field-valued point, where this is
`AlgebraicGeometry.Space.isUnramifiedAt_chart_iff`. -/
theorem isUnramifiedAt_pointsMap_chart_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (comm : a ≫ f = yoneda.map h ≫ b) (x : points B S hS (yoneda.obj U)) :
    IsUnramifiedAt B S hS f (pointsMap B S hS (yoneda.obj U) a x) ↔
      _root_.AlgebraicGeometry.UnramifiedAt ((BigFppfOver.toScheme B S hS).map h)
        (pointsToScheme B S hS U x) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  exact isUnramifiedAt_chart_iff B S hS hX hY f U V a b h ha hb comm p

/-- **Unramifiedness at a point of the source chart scheme.** The point of `|X|` is the image of
the point of the chart presheaf which `v` determines under the bijection of **Stacks 03BX**,
part (1), `AlgebraicGeometry.Space.pointsEquivScheme`; this is the form the chart constructions
consume, their point being a point of a chart scheme.

`AlgebraicGeometry.Space.isUnramifiedAt_pointsMap_chart_iff` at that point. -/
theorem isUnramifiedAt_chartPoint_iff (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (U V : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (comm : a ≫ f = yoneda.map h ≫ b) (v : (BigFppfOver.toScheme B S hS).obj U) :
    IsUnramifiedAt B S hS f
        (pointsMap B S hS (yoneda.obj U) a ((pointsEquivScheme B S hS U).symm v)) ↔
      _root_.AlgebraicGeometry.UnramifiedAt ((BigFppfOver.toScheme B S hS).map h) v := by
  rw [isUnramifiedAt_pointsMap_chart_iff B S hS hX hY f U V a b h ha hb comm]
  exact iff_of_eq (congrArg _
    ((pointsEquivScheme B S hS U).apply_symm_apply v))

end AlgebraicGeometry.Space

end
