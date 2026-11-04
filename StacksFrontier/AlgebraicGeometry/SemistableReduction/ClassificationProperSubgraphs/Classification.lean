module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.IncidenceGraph
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.TreeShape
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.ChainDiagrams
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.BranchedDiagrams

/-!
# Classification of connected proper subgraphs of minus-two indices

Every connected proper set of at least two minus-two indices in a numerical
type is, after reordering, one of the finite Dynkin configurations: types `A`,
`B`, `C`, `D` on any admissible number of vertices, and the exceptional types
`E₆`, `E₇`, `E₈`, `F₄`, `G₂`.

The proof runs in two halves. First the incidence graph of the subset is shown
to be a tree of maximum degree three with at most one trivalent vertex: cycles
of every length are excluded by exhibiting a positive vector supported on the
cycle in the zero locus of the intersection form, a fourth neighbour is
excluded by the four-vertex classification, and two trivalent vertices are
excluded because they would produce the affine diagram `D̃`. Then that shape is
matched against the diagram families, one case per vertex count and branch
position, using the two-, three-, four- and five-vertex classifications, the
`D₅`, `E₆`, `E₇` and `E₈` classifications, and the nonexistence of the affine
diagrams `Ẽ₆`, `Ẽ₇` and `Ẽ₈`.

## Main results

* `AlgebraicGeometry.NumericalType.classify_connected_proper_minusTwo_subgraph`
  (in `Classification/BranchedDiagrams`): the classification.

The proof is split into four parts:

* `Classification/IncidenceGraph`: the incidence graph `minusTwoGraph` is
  connected, acyclic, and of maximum degree three.
* `Classification/TreeShape`: it is a tree with at most one trivalent vertex,
  and a chain when every degree is at most two.
* `Classification/ChainDiagrams`: the Dynkin types of chains and of the `D₄`
  and `D₅` orderings.
* `Classification/BranchedDiagrams`: the branched shapes and the
  classification theorem.

## Implementation notes

An ordering of the subset is an injective map from `Fin I.card` with range
exactly `I`. The genus is not fixed, since its value plays no part in the
classification.

## References

* [Stacks Project, Tag 0C8Q](https://stacks.math.columbia.edu/tag/0C8Q)
-/
