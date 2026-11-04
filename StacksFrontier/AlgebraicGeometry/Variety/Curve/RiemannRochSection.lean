module

public import StacksFrontier.AlgebraicGeometry.CurveIntersectionNumber.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochChern
import StacksCore.Tactic.StacksAttribute

/-!
# The opening of the section on Riemann-Roch

Let `k` be a field and let `X` be a proper scheme of dimension at most one over `k`. The text of
the section on Riemann-Roch that precedes its first lemma consists of five displayed equations,
each of which is formalized and registered under its own tag:

* equation 0BRX, the degree `deg(ℰ) = χ(X, ℰ) - rank(ℰ) χ(X, 𝒪_X)` of a finite locally free
  module of constant rank, is the definition `AlgebraicGeometry.curveDegree`;
* equation 0BRY, `deg(ℰ) = deg(c₁(ℰ) ∩ [X]_1)`, is
  `AlgebraicGeometry.curveDegree_eq_chowDegree_firstChernCapOnCycles_fundamental`;
* equation 0BRZ, the first version of the Riemann-Roch formula
  `χ(X, ℰ) = deg(c₁(ℰ) ∩ [X]_1) + rank(ℰ) χ(X, 𝒪_X)`, is
  `AlgebraicGeometry.eulerCharacteristic_eq_chowDegree_firstChernCapOnCycles_add`;
* equation 0BS0, `(𝓛 · X) = deg(𝓛)` for an invertible module `𝓛`, is
  `AlgebraicGeometry.eq_invertibleCurveDegree_of_isSelfIntersectionNumber`;
* equation 0BS1, `deg_𝓛(X) = (𝓛 · X)`, is
  `AlgebraicGeometry.isSelfIntersectionNumber_one_iff_of_topologicalKrullDim_eq_one`.

The remaining sentences of that text announce the approach of the section and assert nothing.
This file registers the section's tag on the five declarations, which together cover it.

## References

* [Stacks Project, Section "Riemann-Roch", Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
-/

add_to_stacks 0B5B "equation (0BRX): deg(E) = χ(X, E) - rank(E) χ(X, O_X)"
  AlgebraicGeometry.curveDegree

add_to_stacks 0B5B "equation (0BRY): deg(E) = deg(c_1(E) ∩ [X]_1)"
  AlgebraicGeometry.curveDegree_eq_chowDegree_firstChernCapOnCycles_fundamental

add_to_stacks 0B5B "equation (0BRZ): the first version of Riemann-Roch"
  AlgebraicGeometry.eulerCharacteristic_eq_chowDegree_firstChernCapOnCycles_add

add_to_stacks 0B5B "equation (0BS0): (L · X) = deg(L)"
  AlgebraicGeometry.eq_invertibleCurveDegree_of_isSelfIntersectionNumber

add_to_stacks 0B5B "equation (0BS1): deg_L(X) = (L · X)"
  AlgebraicGeometry.isSelfIntersectionNumber_one_iff_of_topologicalKrullDim_eq_one
