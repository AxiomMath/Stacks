module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitStalkMathlibLinearEquiv

/-!
# The length of the structure sheaf at a geometric point, read on an étale chart

Let `X` be an algebraic space over a scheme `S`, let `W` be an étale scheme chart of `X` and let
`u` be a point of `W` lying over the image of a geometric point `x̄` of `X`. The length of the
structure sheaf `𝒪_X`, regarded as an `𝒪_X`-module, at `x̄` is the length of the local ring
`𝒪_{W, u}` of the chart over itself.

This is Stacks 0EE1 read on the chart
(`AlgebraicGeometry.Space.geometricLength_eq_length_stalk_restrictToChart`) at the structure
sheaf, followed by the two identifications that the structure sheaf asks for and a general
module does not: the chart restriction of `𝒪_X` is the structure sheaf of the chart scheme
(`AlgebraicGeometry.Space.restrictToChartUnitIso`), and the stalk of the structure sheaf of a
scheme, viewed as a module over itself, is the local ring
(`Stacks.SheafOfModules.FlatShortExact.unitAbStalkLinearEquivScheme`).

## Main results

* `AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_length_chartStalk`

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The length of the structure sheaf of an algebraic space at a geometric point is the length
of the local ring of a chart over itself.** If `u` is a point of an étale scheme chart `W` of `X`
whose image in `|X|` is the image of the geometric point `x̄`, then the length of `𝒪_X` at `x̄` is
the length of `𝒪_{W, u}` as a module over itself. -/
theorem geometricLength_structureSheafModule_eq_length_chartStalk
    (X : AlgebraicSpaces B S hS) (xbar : GeometricPoint B S hS X.1)
    (W : SmallEtale B S hS X.1) (u : chartScheme W)
    (hu : chartSchemeToPoints B S hS X.1 W u = xbar.image) :
    geometricLength B S hS X xbar (structureSheafModule B S hS X) =
      Module.length ((chartScheme W).presheaf.stalk u) ((chartScheme W).presheaf.stalk u) := by
  rw [geometricLength_eq_length_stalk_restrictToChart B S hS X
    (structureSheafModule B S hS X) xbar W u hu]
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule
    (X := (chartScheme W).toRingedSpace)
    (restrictToChart B S hS X.2 (structureSheafModule B S hS X) W) u
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule
    (X := (chartScheme W).toRingedSpace)
    (SheafOfModules.unit (chartScheme W).ringCatSheaf) u
  exact Eq.trans
    (Stacks.SheafOfModules.FlatShortExact.stalkLinearEquivOfIso (X := chartScheme W)
      (restrictToChartUnitIso B S hS X.1 X.2 W) u).length_eq
    (Stacks.SheafOfModules.FlatShortExact.unitAbStalkLinearEquivScheme
      (chartScheme W) u).length_eq

end AlgebraicGeometry.Space

end
