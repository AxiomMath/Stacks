module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom

/-!
# Flatness of a module on an algebraic space over the target of a morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be an `𝒪_X`-module.  Stacks 05VV calls `F` *flat over* `Y` when, at every point of `X`, the
equivalent conditions of Stacks 05VU hold.  One of those conditions is chartwise: on every
commuting square of étale scheme charts of `f`, the restriction of `F` to the chart of `X` is
flat over the chart of `Y`, in the stalkwise sense of Stacks 08KT for ringed spaces.  That
chartwise condition is taken as the definition here.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatOverOnChartDiagram`: flatness of the restriction of `F` to the
  source chart of one commuting square of étale scheme charts, over the target chart.
* `AlgebraicGeometry.Space.IsFlatOver`: **Stacks 05VV**, flatness of `F` over `Y`.
* `AlgebraicGeometry.Space.IsFlatOverAtPoint`: **Stacks 05VV at a point of `|X|`**, the
  pointwise form of the above, in the some-chart shape which is condition (1) of Stacks 05VU.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtPoint_of_isFlatOver`: flatness of `F` over `Y` gives
  flatness over `Y` at every point of every chart of `X`, so the pointwise predicate really is
  a localisation of the global one.  The two are equivalent for a quasi-coherent module, which
  is `AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtPoint` of
  `StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleAllPoints.lean`.

## Implementation notes

The chartwise form is taken as the definition for the same reason as in
`AlgebraicGeometry.Space.IsLocallyProjective` of
`StacksFrontier/AlgebraicGeometry/Spaces/LocallyProjective.lean`: it is the form that restricts
along a morphism of charts without choosing a presentation, and it is the form a consumer
tests.  Stacks 05VU identifies it with the geometric-stalk form, at every point of `X` and for
a single chosen chart rather than for all of them; that lemma is registered downstream of this
file, as
`AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleAtGeometricPointEquiv.lean`, so the
identification is made there rather than here and the geometric-stalk form is not stated in this
file.  Flatness of a morphism of algebraic spaces is treated the same way — it is
`AlgebraicGeometry.Space.IsFlat` of
`StacksFrontier/AlgebraicGeometry/Spaces/Flat.lean`, the chartwise condition on every commuting
square of étale scheme charts.

The commuting squares are `AlgebraicGeometry.Space.ChartDiagram`, which carries an arbitrary
vertical morphism of schemes between the two charts, so the definition quantifies over all of
them rather than over a chosen étale atlas.  The condition on one square is the ringed-space
predicate `AlgebraicGeometry.IsFlatOver` of Stacks 08KT applied to the sheafed space of the
vertical scheme morphism, and the module is
`AlgebraicGeometry.Space.restrictToChart`, the restriction `F|_U` of `F` to the source chart.

The predicate is defined for every `𝒪_X`-module, although the source applies it to
quasi-coherent ones; as with `AlgebraicGeometry.Scheme.Modules.IsLocallyProjective` this lets
quasi-coherence stay an independent hypothesis in results that use the definition.

The module universe is the universe of the structure rings.  That is not a restriction coming
from here — `AlgebraicGeometry.Space.restrictToChart` raises an arbitrary module universe `m`
to `max u m` and the ringed-space predicate is stated at the universe of the ambient space —
but at a larger `m` the restriction no longer lands in `AlgebraicGeometry.Scheme.Modules` of
the chart, which is what `AlgebraicGeometry.IsFlatOver` consumes.  It is also the universe at
which `AlgebraicGeometry.Space.modulePullback` exists, so it is the only one at which the
consumers of this predicate can state anything.

## References

* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- Flatness of a module on an algebraic space over the target, on one commuting square of
étale scheme charts: the restriction of `F` to the source chart is flat over the target chart,
relative to the vertical morphism of schemes of the square. -/
noncomputable abbrev IsFlatOverOnChartDiagram (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (F : Modules.{u, u} B S hS X hX) (d : ChartDiagram B S hS X Y f) : Prop :=
  AlgebraicGeometry.IsFlatOver
    (LocallyRingedSpace.forgetToSheafedSpace.map
      ((BigFppfOver.toScheme B S hS).map d.g).toLRSHom)
    (restrictToChart B S hS hX F d.U)

/-- **Stacks 05VV.** An `𝒪_X`-module is *flat over* `Y` along `f : X ⟶ Y` when, on every
commuting square of étale scheme charts of `f`, its restriction to the chart of `X` is flat
over the chart of `Y`. -/
@[stacks 05VV "flatness over the target"]
noncomputable abbrev IsFlatOver (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) : Prop :=
  ∀ d : ChartDiagram B S hS X Y f, IsFlatOverOnChartDiagram B S hS hX F d

/-- **Stacks 05VV at a point of `|X|`.** An `𝒪_X`-module is *flat over* `Y` *at* a point `x` of
`|X|` when, on some commuting square of étale scheme charts of `f` and at some point of the
chart of `X` lying over `x`, the restriction of `F` to that chart is flat over the chart of `Y`
at that point, in the stalkwise sense of Stacks 08KT part (1) for ringed spaces.

Quantifying existentially over the charts is what the source does: this is condition (1) of
Stacks 05VU, which that lemma identifies with the geometric-stalk condition (2) at `x`.  That
lemma is *not* unavailable in this development — it is registered, for a quasi-coherent module,
as `AlgebraicGeometry.Space.isFlatOverAt_exists_chartDiagram_iff_isFlatOverAtGeometricPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleAtGeometricPointEquiv.lean`, which is downstream
of this file; so the identification, and with it the independence of the chosen square, is made
there and not here.  The consequence this definition's consumers want is
`AlgebraicGeometry.Space.isFlatOverAtPoint_iff_isFlatOverAtOnChartDiagram` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModulePointChartIndependence.lean`: the condition may
be read on any one square through the point.

This is the pointwise form of `AlgebraicGeometry.Space.IsFlatOver`, which asks the same
ringed-space condition at *every* point of *every* chart square; the global predicate restricts
to this one at every chart point, which is
`AlgebraicGeometry.Space.isFlatOverAtPoint_of_isFlatOver`; that the global predicate is exactly
the conjunction of this one over all `x` of `|X|` is
`AlgebraicGeometry.Space.isFlatOver_iff_forall_isFlatOverAtPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleAllPoints.lean`, again downstream of this file
because the converse direction rests on the chart independence. -/
@[stacks 05VV "flatness over the target at a point of |X|"]
noncomputable def IsFlatOverAtPoint (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X hX) (x : points B S hS X) : Prop :=
  ∃ (d : ChartDiagram B S hS X Y f) (u : etaleChartScheme B S hS d.U),
    pointsMap B S hS (yoneda.obj d.U.obj.left) d.U.obj.hom
        ((pointsEquivScheme B S hS d.U.obj.left).symm u) = x ∧
      AlgebraicGeometry.IsFlatOverAt
        (LocallyRingedSpace.forgetToSheafedSpace.map
          ((BigFppfOver.toScheme B S hS).map d.g).toLRSHom)
        (restrictToChart B S hS hX F d.U) u

/-- Flatness of `F` over `Y` gives flatness of `F` over `Y` at every point of the source chart
of every commuting square of étale scheme charts: the global predicate is the same ringed-space
condition on the restriction of `F` to that chart, asked at every point of it. -/
theorem isFlatOverAtPoint_of_isFlatOver {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y} (F : Modules.{u, u} B S hS X hX)
    (h : IsFlatOver B S hS hX f F) (d : ChartDiagram B S hS X Y f)
    (u : etaleChartScheme B S hS d.U) :
    IsFlatOverAtPoint B S hS hX f F
      (pointsMap B S hS (yoneda.obj d.U.obj.left) d.U.obj.hom
        ((pointsEquivScheme B S hS d.U.obj.left).symm u)) :=
  ⟨d, u, rfl, h d u⟩

end AlgebraicGeometry.Space

end
