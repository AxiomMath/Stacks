module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order

/-!
# Affine étale charts of a first-order thickening of algebraic spaces

Let `W ⊂ W'` be a first-order thickening of algebraic spaces over a scheme `S`.  On an étale
chart `v : V ⟶ W'` with `V` affine, the inclusion restricts to a square-zero closed immersion
`U ⟶ V` of affine objects of the big fppf site, where `U = W ×_{W'} V`.  Such charts exist
through every point of `W'` and cover every étale chart of `W'`, so a deformation-theoretic
statement about square-zero closed immersions of affine schemes may be applied to `W ⊂ W'`
chartwise.

## Main results

* `AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening`: the restriction of
  a first-order thickening to an affine étale chart is a square-zero closed immersion of affine
  objects of the site.
* `AlgebraicGeometry.Space.exists_squareZeroChart_cover_of_isFirstOrderThickening`: every étale
  chart of `W'` is covered by affine étale charts carrying such a restriction.
* `AlgebraicGeometry.Space.exists_squareZeroChart_at_point_of_isFirstOrderThickening`: every
  point of `W'` lies in the image of such a chart.

## Implementation notes

The square-zero-ness is not re-derived from the defining ideal: it is the case `n = 1` of
`AlgebraicGeometry.Space.exists_nthOrderThickening_chart_pullback`, which descends the order of
a thickening to an étale scheme chart, and `AlgebraicGeometry.Space.IsSquareZeroClosedImmersion`
of a morphism of the site is by definition `Stacks.Thickenings.IsFirstOrderThickening` of the
underlying morphism of schemes.  Affineness of the chart of `W` is affineness of a closed
subscheme of an affine scheme; étaleness of that chart is stability of étaleness under base
change, `AlgebraicGeometry.Space.isEtale_of_isPullback_yoneda`.

Neither covering statement needs the affine chart diagrams of Stacks 03G2: the affine objects of
the site covering a given one are its affine open cover,
`AlgebraicGeometry.BigFppfOver.exists_affine_etale_cover`, and a chart through a prescribed point
is `AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`, neither of which refers to the
thickening.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 06BK](https://stacks.math.columbia.edu/tag/06BK)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The square-zero chart of a first-order thickening -/

/-- **A first-order thickening restricts to a square-zero closed immersion on an affine étale
chart.** Let `W ⊂ W'` be a first-order thickening of algebraic spaces over `S` and let
`v : V ⟶ W'` be an étale chart whose underlying scheme is affine.  The base change of the
inclusion of `W` along `v` is then an étale chart `u : U ⟶ W` whose underlying scheme is affine,
and the projection `t : U ⟶ V` is a square-zero closed immersion of objects of the site. -/
theorem exists_squareZeroChart_of_isFirstOrderThickening {W' : AlgebraicSpaces B S hS}
    {W : Subfunctor W'.1} (hW : IsFirstOrderThickening B S hS W' W) (V : BigFppfOver B S hS)
    (v : yoneda.obj V ⟶ W'.1) (hv : IsEtale B S hS v)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    ∃ (U : BigFppfOver B S hS) (t : U ⟶ V) (u : yoneda.obj U ⟶ W.toFunctor),
      IsPullback (yoneda.map t) u v W.ι ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
        IsEtale B S hS u ∧ IsSquareZeroClosedImmersion B S hS t := by
  obtain ⟨U, t, u, hpb, hci, hker⟩ :=
    exists_nthOrderThickening_chart_pullback B S hS hW V v
      ((isEtale_iff_presheaf_of_yoneda B S hS v).1 hv)
  have hciU : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map t) := hci
  exact ⟨U, t, u, hpb.flip, isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map t),
    isEtale_of_isPullback_yoneda B S hS hpb.flip hv, hciU, by simpa using hker⟩

/-! ### Covering a chart, and a chart through a point -/

/-- **Every étale chart of `W'` is covered by affine étale charts on which a first-order
thickening is a square-zero closed immersion.** The affine open cover of the chart is a covering
family of the big fppf site over `S`, and
`AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening` applies to each of its
members. -/
theorem exists_squareZeroChart_cover_of_isFirstOrderThickening {W' : AlgebraicSpaces B S hS}
    {W : Subfunctor W'.1} (hW : IsFirstOrderThickening B S hS W' W) (V : BigFppfOver B S hS)
    (v : yoneda.obj V ⟶ W'.1) (hv : IsEtale B S hS v) :
    ∃ (I : Type u) (V' : I → BigFppfOver B S hS) (π : ∀ i, V' i ⟶ V)
        (U : I → BigFppfOver B S hS) (t : ∀ i, U i ⟶ V' i)
        (u : ∀ i, yoneda.obj (U i) ⟶ W.toFunctor),
      Sieve.generate (Presieve.ofArrows V' π) ∈ BigFppfOver.topology B S hS V ∧
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V' i))) ∧
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (U i))) ∧
        (∀ i, IsEtale B S hS (yoneda.map (π i) ≫ v)) ∧ (∀ i, IsEtale B S hS (u i)) ∧
        (∀ i, IsPullback (yoneda.map (t i)) (u i) (yoneda.map (π i) ≫ v) W.ι) ∧
        ∀ i, IsSquareZeroClosedImmersion B S hS (t i) := by
  obtain ⟨I, V', π, hV'aff, hπ, hcov⟩ := BigFppfOver.exists_affine_etale_cover B S hS V
  have hchart : ∀ i, IsEtale B S hS (yoneda.map (π i) ≫ v) := fun i =>
    isEtale_comp B S hS (hπ i) hv
  choose U t u hpb hUaff hu hsq using fun i =>
    exists_squareZeroChart_of_isFirstOrderThickening B S hS hW (V' i) (yoneda.map (π i) ≫ v)
      (hchart i) (hV'aff i)
  exact ⟨I, V', π, U, t, u, hcov, hV'aff, hUaff, hchart, hu, hpb, hsq⟩

/-- **Every point of `W'` lies on an affine étale chart on which a first-order thickening is a
square-zero closed immersion.** The chart of `W'` is the one Stacks 082H uses,
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`, and the chart of `W` on it is
`AlgebraicGeometry.Space.exists_squareZeroChart_of_isFirstOrderThickening`. -/
theorem exists_squareZeroChart_at_point_of_isFirstOrderThickening {W' : AlgebraicSpaces B S hS}
    {W : Subfunctor W'.1} (hW : IsFirstOrderThickening B S hS W' W)
    (x : points B S hS W'.1) :
    ∃ (V U : BigFppfOver B S hS) (v : yoneda.obj V ⟶ W'.1) (t : U ⟶ V)
        (u : yoneda.obj U ⟶ W.toFunctor),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
        IsEtale B S hS v ∧ IsEtale B S hS u ∧
        IsPullback (yoneda.map t) u v W.ι ∧ IsSquareZeroClosedImmersion B S hS t ∧
        ∃ w : points B S hS (yoneda.obj V), pointsMap B S hS (yoneda.obj V) v w = x := by
  obtain ⟨V, v, hVaff, hvP, w, hw⟩ :=
    exists_affine_etale_chart_at_point B S hS W'.1 W'.2 x
  have hv : IsEtale B S hS v := (isEtale_iff_presheaf_of_yoneda B S hS v).2 hvP
  obtain ⟨U, t, u, hpb, hUaff, hu, hsq⟩ :=
    exists_squareZeroChart_of_isFirstOrderThickening B S hS hW V v hv hVaff
  exact ⟨V, U, v, t, u, hVaff, hUaff, hv, hu, hpb, hsq, w, hw⟩

end AlgebraicGeometry.Space

end
