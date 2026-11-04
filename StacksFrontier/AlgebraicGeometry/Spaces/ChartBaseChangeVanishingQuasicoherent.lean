module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeComparisonBijective

/-!
# Vanishing of the base change of a map of quasi-coherent modules on an affine chart diagram

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`, let
`u : F ⟶ G` be a map of quasi-coherent `𝒪_Y`-modules and let `d` be a commuting square of affine
étale scheme charts over `f` — a chart `d.U` of `X` above a chart `d.V` of `Y`.  This file
removes the presentation hypotheses from
`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_iff`: the base change `f^*u` vanishes
on the sections over `d.U` exactly when the extension of scalars of the sections of `u` over the
chart of `Y` vanishes.

## Main results

* `AlgebraicGeometry.Space.val_app_eq_zero_iff_lTensor_chartSpace`: the criterion, with no
  presentation hypothesis, **in the chart-space spelling** — the extension of scalars is the one
  attached to the diagram of identity charts of the two chart spaces.

## Implementation notes

`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_iff` proves the criterion for modules
carrying presentations which are right exact on the sections over the chart of `Y`; a
quasi-coherent module has such a presentation after restriction to the *chart space* of `d.V`
(`AlgebraicGeometry.Space.exists_presentation_rightExact_app_idEtaleChart`), so the criterion is
applied to the morphism of chart spaces `AlgebraicGeometry.Space.chartSpaceMapOver` attached to
the vertical morphism of `d`, at the diagram of identity charts
`AlgebraicGeometry.Space.chartSpaceIdChartDiagram`.  The *left*-hand side is moved back to `f`
and `d` by `AlgebraicGeometry.Space.val_app_eq_zero_iff_chartSpace`, which is a statement about
modules and costs nothing.

**What stays in the chart-space spelling, and why.**  The right-hand side is the extension of
scalars `𝒪(e.U) ⊗_{𝒪(e.V)} (-)` of the sections of the chart restriction of `u` over the identity
chart `e.V`, where `e` is the chart-space diagram.  Each of the three identifications that would
turn it into `𝒪_X(d.U) ⊗_{𝒪_Y(d.V)} u(d.V)` holds by `rfl` — the sections of the chart
restriction over the identity chart are the sections over the chart
(`AlgebraicGeometry.Space.etaleModulePullback_chartToSpace_obj_val_obj_idEtaleChart`), the
structure ring of the identity chart is the structure ring of the chart, and the pullback of
regular functions of `e` is that of `d`, so the two
`AlgebraicGeometry.Space.chartDiagramAlgebra` instances agree — and
`AlgebraicGeometry.Space.isCartesianOnAffineChartDiagrams_of_isQuasicoherentOnSite` performs
exactly this conversion on a `≃ₗ` by a single `exact`.  It does **not** go through on a
`LinearMap.lTensor`: the module instances on the two tensor products each mention the algebra, so
the conversion is one `isDefEq` that must unfold all three at once, and it exceeds the heartbeat
limit *on its own*, even in a declaration containing nothing but `Iff.rfl`.  So the conversion is
not made and the statement is left in the spelling in which it is proved.

A second route to the statement in the spelling of `f` and `d` avoids the conversion:
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange` proves the *canonical*
comparison bijective at a presented module, and the proof of
`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_iff` uses nothing of the presentation
beyond that bijectivity and the naturality
`AlgebraicGeometry.Space.modulePullbackChartBaseChange_map`, which is available at `f` and `d`
directly.  The bijectivity of `AlgebraicGeometry.Space.modulePullbackChartBaseChange B S hS f M d`
for quasi-coherent `M` over a diagram of affine charts is
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Over a diagram of affine étale charts, the base change of a map of quasi-coherent modules
vanishes on the sections over the chart of `X` exactly when an extension of scalars of its
sections over the chart of `Y` does.**

No presentation is assumed: the restrictions of `F` and `G` to the chart space of `d.V` carry
presentations which are right exact on the sections over its identity chart, so
`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_iff` applies to the morphism of chart
spaces, and `AlgebraicGeometry.Space.val_app_eq_zero_iff_chartSpace` brings the left-hand side
back to `f` and `d`.

The extension of scalars on the right is the one attached to the chart-space diagram of identity
charts.  It is definitionally the extension of scalars `𝒪_X(d.U) ⊗_{𝒪_Y(d.V)} u(d.V)`, but that
conversion exceeds the heartbeat limit; see the implementation notes of this file. -/
theorem val_app_eq_zero_iff_lTensor_chartSpace (f : X ⟶ Y)
    {F G : Modules.{u, u} B S hS Y.1 Y.2} (hF : F.IsQuasicoherentOnSite)
    (hG : G.IsQuasicoherentOnSite) (u : F ⟶ G)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    letI := chartDiagramAlgebra B S hS (chartSpaceMapOver B S hS d.g)
      (chartSpaceIdChartDiagram B S hS f d)
    ((modulePullback B S hS f).map u).val.app (op d.U) = 0 ↔
      LinearMap.lTensor
          (chartRing B S hS (chartSpace B S hS X d.U).1 (chartSpace B S hS X d.U).2
            (chartSpaceIdChartDiagram B S hS f d).U)
          (((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
              (isEtale_chartToSpace B S hS Y d.V)).map u).val.app
            (op (chartSpaceIdChartDiagram B S hS f d).V)).hom = 0 := by
  obtain ⟨P, hgenF, -, hexF⟩ :=
    exists_presentation_rightExact_app_idEtaleChart B S hS Y F hF d.V hV
  obtain ⟨Q, hgenG, -, hexG⟩ :=
    exists_presentation_rightExact_app_idEtaleChart B S hS Y G hG d.V hV
  refine Iff.trans (val_app_eq_zero_iff_chartSpace B S hS f u d).symm ?_
  exact modulePullback_map_val_app_eq_zero_iff B S hS (chartSpaceMapOver B S hS d.g)
    (isQuasicoherentOnSite_etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V) F hF)
    (isQuasicoherentOnSite_etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V) G hG)
    P Q ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V)).map u)
    (chartSpaceIdChartDiagram B S hS f d) hU hV hgenF hexF hgenG hexG

end AlgebraicGeometry.Space

end
