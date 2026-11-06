module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ClosedPointInFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothRelationBaseChangeStepC

/-!
# Discharging the closedness input of the closed-fibre comparison (Stacks 0DS9)

`AlgebraicGeometry.Space.HasClosedChartFibreSquare` is the closedness input of the closed-fibre
comparison which the Step C identity of **Stacks 0DS9** turns on, and
`AlgebraicGeometry.Space.exists_chart_square_hasClosedChartFibreSquare_of_isPullback` reduces it,
for a leg sitting in a cartesian square of presheaves, to two statements about the chart square
it hands out: that the chart point is closed in the chart fibre of the leg, and that its image is
closed in the chart fibre of `h`.

This file discharges those two from the two routes of
`StacksFrontier/AlgebraicGeometry/Morphisms/ClosedPointInFibre.lean`, one lemma for each route.

**Neither is what the chart comparison of Stacks 0DS9 uses.** Both constrain a chart of the
APEX, and a caller comparing invariants has no handle on one. The comparison goes through
`AlgebraicGeometry.Space.hasClosedChartFibreSquare_of_isClosed_pointsToScheme` instead, which
asks for one closed point of the scheme `U'` and derives the condition on the leg from the
condition on `h` along the cartesian square of chart schemes. What remains here are the two
routes for a leg whose chart square can be constrained directly.

## Main results

* `AlgebraicGeometry.Space.exists_chart_square_hasClosedChartFibreSquare_of_isClosed_chartPoint`:
  closedness of the chart point in the chart *itself* — not in the fibre — suffices. This is the
  route along a refinement of smooth charts, where the source of Stacks 0DS9 shrinks the two
  charts until the two points are closed.
* `AlgebraicGeometry.Space.exists_chart_square_hasClosedChartFibreSquare_of_injective`:
  injectivity on points of the two chart realizations suffices, with NO hypothesis on the point
  at all, because then each chart fibre has at most one point. This is the route along the
  identity and along an open immersion, where the shrinking step replaces a chart by an open
  subscheme of it and the point is a finite type point, never a closed one.

## Why these are two lemmas and not one

The two hypotheses are incomparable. Closedness of the chart point in its chart says nothing
about injectivity, and injectivity of the chart realizations fails along a smooth refinement,
whose fibres are positive-dimensional. Baking either spelling into a single closedness lemma
therefore fits at most one of the two, and the pair is kept apart deliberately.

## References

* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W U U' Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Closedness of the chart point in its chart discharges the closedness input.** For a leg
`π₁` sitting in a cartesian square `IsPullback π₁ π₂ k h` of presheaves, the chart square of
`AlgebraicGeometry.Space.exists_chart_square_hasClosedChartFibreSquare_of_isPullback` gives
`AlgebraicGeometry.Space.HasClosedChartFibreSquare` as soon as the chart point of `M` is closed
in `M` and its image under `gsnd` is closed in the chart of the second coordinate — closed in the
CHART, which is stronger than, and implies, closed in the chart fibre
(`AlgebraicGeometry.isClosed_singleton_asFiber_of_isClosed`).

This asks for closedness in the CHART of the apex, which the shrinking of the two charts in
Stacks 0DS9 does not by itself deliver — the point whose closedness that step produces is a point
of `U'`. -/
theorem exists_chart_square_hasClosedChartFibreSquare_of_isClosed_chartPoint
    (hW : IsAlgebraicSpace B S hS W) (hU : IsAlgebraicSpace B S hS U)
    (hU' : IsAlgebraicSpace B S hS U') (k : W ⟶ U) (h : U' ⟶ U) (π₁ : Z ⟶ W) (π₂ : Z ⟶ U')
    (hsq₀ : IsPullback π₁ π₂ k h) (hZ : IsAlgebraicSpace B S hS Z)
    (a : GeometricPoint B S hS Z) :
    ∃ (M : SmallEtaleNeighborhood a)
      (N : SmallEtaleNeighborhood (geometricPointMap π₁ a))
      (P : SmallEtaleNeighborhood (geometricPointMap π₂ a))
      (Q : SmallEtaleNeighborhood (geometricPointMap h (geometricPointMap π₂ a)))
      (gfst : M.chart.obj.left ⟶ N.chart.obj.left)
      (gsnd : M.chart.obj.left ⟶ P.chart.obj.left)
      (gh : P.chart.obj.left ⟶ Q.chart.obj.left),
      IsClosed ({(chartGeometricPoint M).hom
                  (IsLocalRing.closedPoint (chartGeometricPoint M).residueField)} : Set _) →
        IsClosed ({((BigFppfOver.toScheme B S hS).map gsnd)
                    ((chartGeometricPoint M).hom (IsLocalRing.closedPoint
                      (chartGeometricPoint M).residueField))} : Set _) →
          HasClosedChartFibreSquare B S hS h π₁ π₂ a := by
  obtain ⟨M, N, P, Q, gfst, gsnd, gh, hcl⟩ :=
    exists_chart_square_hasClosedChartFibreSquare_of_isPullback B S hS hW hU hU' k h π₁ π₂
      hsq₀ hZ a
  exact ⟨M, N, P, Q, gfst, gsnd, gh, fun h₁ h₂ =>
    hcl (isClosed_singleton_asFiber_of_isClosed _ _ h₁)
      (isClosed_singleton_asFiber_of_isClosed _ _ h₂)⟩

/-- **Injectivity of the chart realizations discharges the closedness input, with no hypothesis
on the point.** For a leg `π₁` sitting in a cartesian square `IsPullback π₁ π₂ k h` of presheaves,
the chart square of
`AlgebraicGeometry.Space.exists_chart_square_hasClosedChartFibreSquare_of_isPullback` gives
`AlgebraicGeometry.Space.HasClosedChartFibreSquare` as soon as the two chart realizations `gfst`
and `gh` are injective on points: each chart fibre then has at most one point, so the singleton
of the chart point is the whole fibre and is closed for that reason
(`AlgebraicGeometry.isClosed_singleton_asFiber_of_injective`).

This is the route along the identity and along an open immersion, where the chart realizations
are injective and the point need not be constrained at all. -/
theorem exists_chart_square_hasClosedChartFibreSquare_of_injective
    (hW : IsAlgebraicSpace B S hS W) (hU : IsAlgebraicSpace B S hS U)
    (hU' : IsAlgebraicSpace B S hS U') (k : W ⟶ U) (h : U' ⟶ U) (π₁ : Z ⟶ W) (π₂ : Z ⟶ U')
    (hsq₀ : IsPullback π₁ π₂ k h) (hZ : IsAlgebraicSpace B S hS Z)
    (a : GeometricPoint B S hS Z) :
    ∃ (M : SmallEtaleNeighborhood a)
      (N : SmallEtaleNeighborhood (geometricPointMap π₁ a))
      (P : SmallEtaleNeighborhood (geometricPointMap π₂ a))
      (Q : SmallEtaleNeighborhood (geometricPointMap h (geometricPointMap π₂ a)))
      (gfst : M.chart.obj.left ⟶ N.chart.obj.left)
      (gsnd : M.chart.obj.left ⟶ P.chart.obj.left)
      (gh : P.chart.obj.left ⟶ Q.chart.obj.left),
      Function.Injective ((BigFppfOver.toScheme B S hS).map gfst).base →
        Function.Injective ((BigFppfOver.toScheme B S hS).map gh).base →
          HasClosedChartFibreSquare B S hS h π₁ π₂ a := by
  obtain ⟨M, N, P, Q, gfst, gsnd, gh, hcl⟩ :=
    exists_chart_square_hasClosedChartFibreSquare_of_isPullback B S hS hW hU hU' k h π₁ π₂
      hsq₀ hZ a
  exact ⟨M, N, P, Q, gfst, gsnd, gh, fun h₁ h₂ =>
    hcl (isClosed_singleton_asFiber_of_injective _ h₁ _)
      (isClosed_singleton_asFiber_of_injective _ h₂ _)⟩

end AlgebraicGeometry.Space

end
