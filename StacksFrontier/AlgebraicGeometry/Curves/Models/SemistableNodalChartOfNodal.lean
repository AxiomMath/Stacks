module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableNodalChart
public import StacksFrontier.AlgebraicGeometry.Curves.NodalChartNeighbourhoodOfNodal

/-!
# Étale local charts of a nodal curve over a discrete valuation ring, unconditionally

[Stacks, Tag 0CDD] is `Stacks.Models.exists_etale_nodalChart_pow_uniformizer`, in
`StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableNodalChart`. Its input, the chart form of
the étale local structure at every point of an at-worst-nodal family
(`Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_isAtWorstNodal`), is proved
in `StacksFrontier.AlgebraicGeometry.Curves.NodalChartNeighbourhoodOfNodal`. This file keeps the
name `Stacks.Models.exists_etale_nodalChart_pow_uniformizer_of_isAtWorstNodal` for that theorem.

## Main results

* `AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE`,
  `Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_standardNodalDiagram`,
  `Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_smoothAt` and
  `Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_isAtWorstNodal` — aliases
  of the results of `StacksFrontier.AlgebraicGeometry.Curves.NodalChartNeighbourhoodOfNodal`.
* `Stacks.Models.exists_etale_nodalChart_pow_uniformizer_of_isAtWorstNodal` — **Tag 0CDD**, an
  alias of `Stacks.Models.exists_etale_nodalChart_pow_uniformizer`.

## References

* [Stacks Project, Tag 0CDD](https://stacks.math.columbia.edu/tag/0CDD)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

/-- A smooth morphism has, at a point whose fibre has dimension `n`, an affine chart which is
standard smooth of relative dimension `n`: an alias of
`AlgebraicGeometry.exists_affine_chart_isStandardSmoothOfRelativeDimension`. -/
public alias exists_isStandardSmoothOfRelativeDimension_appLE :=
  exists_affine_chart_isStandardSmoothOfRelativeDimension

end AlgebraicGeometry

namespace Stacks.NodalEtaleLocalStructure

/-- The diagram form of Tag 0CBY gives the chart form: an alias of
`Stacks.NodalEtaleLocalStructure.StandardNodalDiagram.nonempty_nodalChartNeighbourhood`. -/
public alias nonempty_nodalChartNeighbourhood_of_standardNodalDiagram :=
  StandardNodalDiagram.nonempty_nodalChartNeighbourhood

/-- At a smooth point with one-dimensional fibre the chart form holds with parameter `1`: an
alias of `Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_one_of_smoothAt`. -/
public alias nonempty_nodalChartNeighbourhood_of_smoothAt :=
  nonempty_nodalChartNeighbourhood_one_of_smoothAt

/-- The chart form of the étale local structure at every point of an at-worst-nodal family of
relative dimension one: an alias of
`Stacks.NodalEtaleLocalStructure.nonempty_nodalChartNeighbourhood_of_atWorstNodal`. -/
public alias nonempty_nodalChartNeighbourhood_of_isAtWorstNodal :=
  nonempty_nodalChartNeighbourhood_of_atWorstNodal

end Stacks.NodalEtaleLocalStructure

namespace Stacks.Models

/-- **Stacks 0CDD**, under the name recording that the at-worst-nodal hypothesis is all it needs:
an alias of `Stacks.Models.exists_etale_nodalChart_pow_uniformizer`. -/
public alias exists_etale_nodalChart_pow_uniformizer_of_isAtWorstNodal :=
  exists_etale_nodalChart_pow_uniformizer

end Stacks.Models

end
