module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothFromLocality.SchemeNeighborhoods
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothFromLocality.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothFromLocality.EtalePostcomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothFromLocality.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothFromLocality.SchemeSquareDescent

/-!
# Étale-smooth locality on the source and target from locality hypotheses (Stacks 0CG2)

Let `S` be a scheme contained in a big fppf site `B` and let `P` be a property of morphisms of
algebraic spaces over `S` which is étale local on the source, smooth local on the target and
stable under postcomposition with open immersions. Then `P` is étale-smooth local on the
source-and-target.

## Main results

* `AlgebraicGeometry.Space.isEtaleSmoothLocalOnSourceAndTarget_of_local`: **Stacks 0CG2**.

## Implementation notes

The three hypotheses are `CategoryTheory.MorphismProperty.IsLocalAtSource` for the étale
precoverage of **Stacks 03YH**, `CategoryTheory.MorphismProperty.IsLocalAtTarget` for the smooth
one, and `CategoryTheory.MorphismProperty.RespectsRight` for the open immersions of
**Stacks 02YU**. The first two clauses of the conclusion and the forward implication of the third
are `AlgebraicGeometry.Space.comp_isEtale`, `AlgebraicGeometry.Space.pullbackSnd_of_isSmooth` and
`AlgebraicGeometry.Space.exists_etale_smooth_neighborhood_of_prop`; what this file adds is the
descent half of the third clause.

That half is proved as in the source: the given neighbourhoods are combined into one square whose
left vertical arrow is surjective, the two locality hypotheses reduce the question to a morphism
of *schemes* of the site, and the resulting statement about schemes is **Stacks 0CF1**. The
pointwise equivalence of Stacks 0CF1 is reproved here for the property of morphisms of schemes
over `S` induced by `P` (`relativeProperty` below) rather than imported from
`AlgebraicGeometry.mem_largestOpen_iff_of_smoothAt_etaleAt`: the induced property is defined only
on the schemes of size below the cutoff of the site, and only relative to a structure morphism to
`S`, so it is not a `CategoryTheory.MorphismProperty` of all schemes and cannot instantiate that
result. What the relative setting needs beyond Stacks 0CF1 is the stability of `relativeProperty`
under postcomposition with an arbitrary étale morphism over `S`, which the absolute statement
gets for free from locality at the source; here it is obtained by induction on a bound for the
fibre degrees of the étale morphism (**Stacks 03J4**, **Stacks 03WU**), peeling off the
complement of the diagonal at each step.

## References

* [Stacks Project, Tag 0CG2](https://stacks.math.columbia.edu/tag/0CG2)
-/
