module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator

/-!
# The étale presentation of a projective bundle by its chart bundles

Let `X` be an algebraic space with its chosen étale presentation `X = U/R`, and let `ℰ` be a
finite locally free `𝒪_X`-module.  The projective bundle `P = 𝐏(ℰ)` of
`AlgebraicGeometry.Space.projectiveBundle` is the quotient of the étale equivalence relation
`P_R ⇉ P_U` formed by the projective bundles of the restrictions of `ℰ` to `U` and to `R`.  So
`P = P_U / P_R` is an étale presentation of `P`, with `P_U` and `P_R` as its presenting and
relation schemes on the nose.

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleChartPresentation`: the presentation `P = P_U/P_R`.

## Main results

* `AlgebraicGeometry.Space.projectiveBundleChartPresentation_toSpace`: its atlas is the chart
  `AlgebraicGeometry.Space.projectiveBundleChart`.

## References

* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
  (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- **The étale presentation `P = P_U/P_R` of the projective bundle by its chart bundles**: the
presenting scheme is the chart bundle over the presenting chart of `X`, the relation scheme the
chart bundle over the relation chart, and the two projections the morphisms of chart bundles over
the two legs of the relation. -/
abbrev projectiveBundleChartPresentation :
    Presentation B S hS (projectiveBundle E hfree).1 (projectiveBundle E hfree).2 where
  U := (projectiveBundleChartFamily E hfree).site
    (presentationChart (projectiveBundlePresentation X))
  R := (projectiveBundleChartFamily E hfree).site
    (presentationRelationChart (projectiveBundlePresentation X))
  target := (projectiveBundleChartFamily E hfree).siteMap
    (presentationRelationTargetHom (projectiveBundlePresentation X))
  source := (projectiveBundleChartFamily E hfree).siteMap
    (presentationRelationSourceHom (projectiveBundlePresentation X))
  isEtaleEquivalenceRelation := (projectiveBundleChartFamily E hfree).isEtaleEquivalenceRelation
    _ _ (isPullback_projectiveBundlePresentation X)
  toSpace := projectiveBundleChart E hfree
  surjective := (projectiveBundleChartFamily E hfree).surjective_quotientChart _ _
    (isPullback_projectiveBundlePresentation X)
  etale := (projectiveBundleChartFamily E hfree).etale_quotientChart _ _
    (isPullback_projectiveBundlePresentation X)
  isPullback := by
    have := (projectiveBundleChartFamily E hfree).isEtaleEquivalenceRelation _ _
      (isPullback_projectiveBundlePresentation X)
    rw [projectiveBundleChart, ← CartesianChartFamily.quotientChart,
      CartesianChartFamily.quotientChart_eq_quotientMap]
    exact quotientMap_isPullback B S hS _ _

/-- The atlas of the presentation is the chart of the projective bundle. -/
theorem projectiveBundleChartPresentation_toSpace :
    (projectiveBundleChartPresentation E hfree).toSpace = projectiveBundleChart E hfree :=
  rfl

end AlgebraicGeometry.Space

end
