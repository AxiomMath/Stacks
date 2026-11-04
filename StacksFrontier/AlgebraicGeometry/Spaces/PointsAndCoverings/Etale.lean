module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Étale morphisms of algebraic spaces (Stacks 03EC, 03FT)

The two closure properties of étaleness that do not refer to the algebraic-space axioms —
that an étale morphism of the big fppf site composed into an étale representable morphism
towards a presheaf again has étale composite, and that a composite of étale morphisms of
algebraic spaces is étale — are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts` and
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms`, where the étale calculus of charts
and the remaining permanence properties of Tag 03FS–03FV live. This module re-exports them.

## Main results

* `AlgebraicGeometry.Space.etale_comp_of_scheme`: **Stacks 03EC**, in
  `StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts`.
* `AlgebraicGeometry.Space.isEtale_comp`: **Stacks 03FT**, in
  `StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms`.

## References

* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 03FT](https://stacks.math.columbia.edu/tag/03FT)
-/
