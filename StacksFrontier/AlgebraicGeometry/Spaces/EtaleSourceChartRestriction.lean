module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleEtaleChartTransport

/-!
# The chart restriction of a module pulled back along an étale morphism of algebraic spaces

Let `a : X' ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` of a big fppf site
and let `F` be a quasi-coherent `𝒪_X`-module.  An étale scheme chart `W` of `X'` is also an
étale scheme chart of `X`, étale morphisms composing, and under that reading this file identifies
the restriction of `a^*F` to `W` with the restriction of `F` to the same chart of `X`.

This is the identification a statement about a module on an étale `X`-space needs in order to be
read on the charts of that space.  The chartwise conditions on `a^*F` —
`AlgebraicGeometry.Space.IsFlatOver` of Tag 05VV,
`AlgebraicGeometry.Space.IsFinitePresentationOnCharts`, and the rest — are conditions on
`AlgebraicGeometry.Space.restrictToChart` at the charts of `X'`, and this file turns each of them
into a condition on the restriction of `F` to a chart of `X`.  The case of an open subspace
`X' ⊆ X`, where `a` is étale by
`AlgebraicGeometry.Space.isEtale_ι_of_isOpenSubspace`, is the one Stacks 0DLR needs.

## Main definitions

* `AlgebraicGeometry.Space.chartOfEtaleSource`: an étale scheme chart of `X'`, read as an étale
  scheme chart of `X`.
* `AlgebraicGeometry.Space.chartDiagramOfEtaleSource`: a commuting square of étale scheme charts
  of `a ≫ f` for `f : X ⟶ Y`, read as one of `f` itself.

## Main results

* `AlgebraicGeometry.Space.pointOfEtaleChart_chartOfEtaleSource`: the point of `|X|` cut out by a
  point of the chart is the image of the point of `|X'|` it cuts out.
* `AlgebraicGeometry.Space.restrictToChartEtaleSourceIso`: **the chart restriction of `a^*F`.**

## Implementation notes

The isomorphism is the base change of the chart restriction,
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, on the square joining the chart `W` of
`X'` to the same chart read on `X` by the *identity* morphism of the underlying object of the
site; the Zariski inverse image along that identity is stripped by
`AlgebraicGeometry.Space.pullbackToSchemeMapIdIso`.  The square is not asked to be cartesian, so
no pullback of charts is formed and the two charts have literally the same underlying scheme.

Quasi-coherence of `F` on the small étale site is what the base change consumes, as Tag 05VP does
in the proof of Tag 05VU; the chartwise reading of quasi-coherence does not suffice, for the
reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestriction.lean`.

The module universe is the universe of the structure rings, as it must be for
`AlgebraicGeometry.Space.restrictToChart` to land in `AlgebraicGeometry.Scheme.Modules` of the
chart and for `AlgebraicGeometry.Space.modulePullback` of Tag 03LU to exist.

## References

* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Xs' Xs Ys : AlgebraicSpaces B S hS} {a : Xs' ⟶ Xs}

/-- An étale scheme chart of `X'`, read as an étale scheme chart of `X` along an étale morphism
`a : X' ⟶ X`: the composite of the chart's structure morphism with `a` is étale. -/
def chartOfEtaleSource (ha : IsEtale B S hS a.hom) (W : SmallEtale B S hS Xs'.1) :
    SmallEtale B S hS Xs.1 :=
  etaleChartOfIsEtale B S hS (W.obj.hom ≫ a.hom)
    (isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS W.obj.hom).2 W.property) ha)

/-- The point of `|X|` cut out by a point of a chart of `X'`, read as a chart of `X`, is the
image in `|X|` of the point of `|X'|` that it cuts out. -/
theorem pointOfEtaleChart_chartOfEtaleSource (ha : IsEtale B S hS a.hom)
    (W : SmallEtale B S hS Xs'.1) (w : etaleChartScheme B S hS W) :
    pointOfEtaleChart B S hS (chartOfEtaleSource B S hS ha W) w =
      pointsMap B S hS Xs'.1 a.hom (pointOfEtaleChart B S hS W w) :=
  congrFun (pointsMap_comp B S hS (yoneda.obj W.obj.left) W.obj.hom a.hom) _

/-- **The chart restriction of the inverse image along an étale morphism.**  For an étale
morphism `a : X' ⟶ X` of algebraic spaces, a quasi-coherent `𝒪_X`-module `F` and an étale scheme
chart `W` of `X'`, the restriction of `a^*F` to `W` is the restriction of `F` to `W` read as a
chart of `X`.

Both are chart restrictions on one and the same scheme, and the comparison is the base change of
the chart restriction along the identity of that scheme. -/
def restrictToChartEtaleSourceIso (ha : IsEtale B S hS a.hom)
    (F : Modules.{u, u} B S hS Xs.1 Xs.2) (hF : F.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS Xs'.1) :
    restrictToChart B S hS Xs.2 F (chartOfEtaleSource B S hS ha W) ≅
      restrictToChart B S hS Xs'.2 ((modulePullback B S hS a).obj F) W :=
  (pullbackToSchemeMapIdIso B S hS W.obj.left
      (restrictToChart B S hS Xs.2 F (chartOfEtaleSource B S hS ha W))).symm ≪≫
    restrictToChartBaseChangeIso B S hS a F hF (chartOfEtaleSource B S hS ha W) W
      (𝟙 W.obj.left)
      (by exact (congrArg (fun φ : yoneda.obj W.obj.left ⟶ yoneda.obj W.obj.left =>
        φ ≫ (W.obj.hom ≫ a.hom)) (yoneda.map_id W.obj.left)).trans (Category.id_comp _))

/-- A commuting square of étale scheme charts of `a ≫ f`, for an étale `a : X' ⟶ X` and a
morphism `f : X ⟶ Y` of algebraic spaces, read as a commuting square of étale scheme charts of
`f`: the chart of `X'` becomes a chart of `X` and the vertical morphism of schemes is
unchanged. -/
def chartDiagramOfEtaleSource (ha : IsEtale B S hS a.hom) (f : Xs ⟶ Ys)
    (d : ChartDiagram B S hS Xs'.1 Ys.1 (a.hom ≫ f.hom)) :
    ChartDiagram B S hS Xs.1 Ys.1 f.hom where
  U := chartOfEtaleSource B S hS ha d.U
  V := d.V
  g := d.g
  comm := (Category.assoc _ _ _).trans d.comm

end AlgebraicGeometry.Space

end
