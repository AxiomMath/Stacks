module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.AffineStageCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.StageRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.ChartLimitsInSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentLimitFacts.AffineBase

/-!
# FinitePresentationDescentLimitFacts

The generalizations made by this development of declarations of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent`. That module keeps its
statements as they are; each declaration here restating one of them carries its name with the
suffix `_of_limitFacts` (or `OfLimitFacts` for a definition), and the declarations that depend on
those restatements follow them.

* `AlgebraicGeometry.Space.exists_model_of_finitePresentation_of_affineChartLimitsInSchemes`,
  `AlgebraicGeometry.Space.exists_morphism_after_baseChange_of_affineChartLimitsInSchemes`,
  `AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq_of_affineChartLimitsInSchemes`: Stacks
  07SK for an inverse system of algebraic spaces with no cardinality hypothesis on the index
  category, given that its affine chart systems have their limits computed in schemes
  (`AlgebraicGeometry.Space.AffineChartLimitsInSchemes`).
-/
