module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.BoundaryControl
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.DiameterBound
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.EdgeSums
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.MinusTwoComponents

/-!
# A uniform bound on the intersection matrix of a minimal numerical type

For a minimal numerical type of genus at least two, every entry of the
intersection matrix, multiplied by the multiplicity of its row, is bounded in
absolute value by `768` times the genus. This is the bound that makes the
prime torsion of the Picard group computable: for a prime larger than it, the
intersection matrix stays invertible modulo that prime.

The proof is a chain of three reductions. A component that is not a minus-two
index has its diagonal entry bounded by `6 * g` outright. A minus-two index
adjacent to a bounded component has its own diagonal entry bounded by twice
that bound, so a minus-two index joined to a non-minus-two component by a chain
of `k` minus-two indices is bounded by `6 * g * 2 ^ k`. Finally, every
connected component of minus-two indices is a proper subgraph, hence one of the
Dynkin configurations, and every Dynkin diagram either has diameter at most
seven — which bounds `k` — or has all its multiplicities within a factor of two
of a multiplicity on its boundary, which is bounded directly.

## Main results

* `AlgebraicGeometry.NumericalType.multiplicity_mul_abs_intersection_le`: the
  uniform bound, in `UniformBound/DiameterBound.lean`.

The proof is split into four parts:

* `UniformBound/MinusTwoComponents.lean`: the diagonal bounds along boundary
  chains, and the connected components of minus-two indices together with their
  classification;
* `UniformBound/EdgeSums.lean`: sums over the edges of the Dynkin diagrams of
  types `A`, `B` and `C`;
* `UniformBound/BoundaryControl.lean`: multiplicities of a Dynkin configuration
  within a factor of two of a multiplicity on its boundary;
* `UniformBound/DiameterBound.lean`: short boundary chains inside a component,
  and the uniform bound.

## Implementation notes

The genus is recorded as an integer `g`, and the two component indices are
arbitrary, including the diagonal case. Connected components of minus-two
indices are the `Relation.ReflTransGen` classes of the relation `MinusTwoEdge`,
realized as a `Finset` so that the classification applies to them; distances
inside a component are measured by paths in the induced `SimpleGraph`.

## References

* [Stacks Project, Tag 0C9W](https://stacks.math.columbia.edu/tag/0C9W)
-/
