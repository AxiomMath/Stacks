module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalChartAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection

/-!
# The target comparison at a presented chart is the general presented-chart comparison

`AlgebraicGeometry.Space.ChartLiftPresentation.chartTargetIso` is the target comparison at the
étale chart of the closed subspace that a chart presentation presents: the inverse image of
`𝒞_{X/X'}` to the small étale site of the chart space is the associated module of the Zariski
conormal sheaf of the chart thickening.  It is defined as
`AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso` at the presentation, and this
file says so.

This is the target-side counterpart of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafChartSourceEquation`, and it is
wanted for the same reason: every statement about the general comparison transfers to the
presentation by `congrArg` along this equation, and transferring **at the isomorphism** rather
than at a composite is, as on the source side, the only affordable crossing.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.chartTargetIso_eq`: the target comparison at a
  presented chart **is** the general presented-chart comparison of
  `AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso`, by `rfl`.

Before this, `AlgebraicGeometry.Space.ChartLiftPresentation.chartTargetIso` had no derived
statement of any kind.

## What the equation is read at

The presentation supplies every argument of the general comparison: the closed subspace is `Z`,
the ambient étale chart is `U'`, the presenting closed immersion is
`AlgebraicGeometry.Space.ChartLiftPresentation.incl` and its closedness is the first component of
`AlgebraicGeometry.Space.ChartLiftPresentation.isFirstOrderThickening`, the chart morphism is
`AlgebraicGeometry.Space.ChartLiftPresentation.subChart` and the cartesian square is
`AlgebraicGeometry.Space.ChartLiftPresentation.isPullback`.  The two readings of the target — the
presentation's `Stacks.Thickenings.conormalModules` of the chart thickening and the general
comparison's `Stacks.Conormal.conormalSheaf` of the presenting closed immersion — agree by
unfolding, so no transport appears.

No `@[stacks]` attribute is claimed: Tags 03LU, 04CO and 04G2 (1) are registered at the
isomorphisms that the general comparison composes, and this is an interior step of
[Stacks Project, Tag 04AM].

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

namespace ChartLiftPresentation

variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1}
  (P : ChartLiftPresentation C S hS p q a.hom U')

/-- **The target comparison at a presented chart is the general presented-chart comparison.**
The closed subspace, the ambient étale chart, the presenting closed immersion, the chart morphism
and the cartesian square are the ones the presentation carries, and the closedness of the
presenting immersion is the first component of
`AlgebraicGeometry.Space.ChartLiftPresentation.isFirstOrderThickening`.

This is `rfl`, and it is stated between the isomorphisms so that statements about the general
comparison transfer to the presentation by `congrArg`. -/
theorem chartTargetIso_eq :
    chartTargetIso C S hS P =
      conormalModulePresentedChartAssociatedIso C S hS Z U' P.incl
        P.isFirstOrderThickening.1 P.subChart P.isPullback :=
  rfl

end ChartLiftPresentation

end AlgebraicGeometry.Space

end
