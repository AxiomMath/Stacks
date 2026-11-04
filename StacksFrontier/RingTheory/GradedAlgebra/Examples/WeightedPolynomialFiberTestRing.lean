module

public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomial
public import StacksFrontier.RingTheory.Polynomial.QuotientXPow

/-!
# The test ring for the vertex fibres of the weighted twists

For the weighted polynomial situation `S = k[x, y, z]`, graded by the weights `1`, `2`, `3`, this
file defines the product `k[X]/(X³) × k[X]/(X³)` of two copies of the truncated polynomial ring.

## Main definitions

* `Stacks.WeightedPolynomialSituation.FiberTestRing`: the ring `k[X]/(X³) × k[X]/(X³)`.

## References

* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
-/

@[expose] public noncomputable section

namespace Stacks

namespace WeightedPolynomialSituation

/-- The product `k[X]/(X³) × k[X]/(X³)` of two copies of the truncated polynomial ring. -/
public abbrev FiberTestRing (E : WeightedPolynomialSituation) :=
  Polynomial.QuotientXPow E.k 3 × Polynomial.QuotientXPow E.k 3

end WeightedPolynomialSituation

end Stacks

end
