module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleCover.FiniteOpenUnion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleCover.EtaleDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.EtaleCover.SurjectiveChart

/-!
# An étale scheme chart of the finite part of a morphism

Let `f : X ⟶ Y` be a separated and locally quasi-finite morphism of algebraic spaces over a
scheme `S`. Then the finite part `(X/Y)_fin` of `f` admits a surjective étale morphism from a
scheme of the big fppf site which is itself étale over `Y`.

## Main results

* `AlgebraicGeometry.Space.exists_surjective_etale_chart_finiteOpenSubspacePresheaf` — Stacks
  04QG.

## Implementation notes

Both reductions of the source are carried out. First one replaces `Y` by a scheme étale
surjective over it: the finite part of the base change is the base change of the finite part,
Stacks 04QF, so its chart maps onto the original one, and the base change of `f` is a morphism
of schemes by Stacks 03XX because it stays separated and locally quasi-finite. Then, for a
separated locally quasi-finite morphism of schemes, the charts are the opens produced by the
étale localization of Stacks 04HJ: over an étale neighbourhood `U` of a point of `Y` the base
change decomposes into a part avoiding a prescribed finite set of the fibre and finitely many
pieces finite over `U`, and any union of those pieces is an open subspace finite over `U`,
hence a section of `(X/Y)_fin` over `U` and so a morphism `U ⟶ (X/Y)_fin`, étale by Stacks
04QE.

The chart is the coproduct of all those `U`, taken inside the site by cutting the index set
down to the site's cardinal bound; the sections glue to a section over the coproduct because
the finite part is an fppf sheaf, Stacks 04PE. Surjectivity is checked on points with values
in algebraically closed fields, where an open subspace finite over the field is a finite set
of points and therefore is exactly a union of the pieces above.

## References

* [Stacks Project, Tag 04QG](https://stacks.math.columbia.edu/tag/04QG)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04QE](https://stacks.math.columbia.edu/tag/04QE)
* [Stacks Project, Tag 04QF](https://stacks.math.columbia.edu/tag/04QF)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)

The proof is split into `EtaleCover.FiniteOpenUnion`, `EtaleCover.EtaleDecomposition` and
`EtaleCover.SurjectiveChart`.
-/
