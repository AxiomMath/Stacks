module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import Mathlib.CategoryTheory.Sites.Sieves.Functoriality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings

/-!
# The kernel pair of an étale atlas of an algebraic space (Stacks 0262)

The kernel pair of a surjective étale map from a scheme to an algebraic space is an étale
equivalence relation, and its quotient in fppf sheaves is the algebraic space.

## Main results

* `AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback` gives the equivalence relation.
* `CategoryTheory.MorphismProperty.relative.property` gives both étale projections.
* `AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale` gives the coequalizer property.

All three are re-exported from `StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation`.

* `AlgebraicGeometry.Space.singleton_mem_bigFppf_topology`, which says that a single
  surjective étale morphism of the bounded category of schemes generates a covering sieve, is
  re-exported too: it is proved in `StacksFrontier.AlgebraicGeometry.Spaces.Presentation`, which
  is imported publicly above.

## Implementation notes

The three parts of Stacks 0262 were proved here as well as in
`StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation`, under the same fully-qualified
names and with the same part keys — `@[stacks 0262 "part (1)"]`, the `add_to_stacks` of part
(2) and `@[stacks 0262 "part (3)"]` all stood on both sites. The two statements are the same
statement: elaborated separately and dumped with `pp.universes`, `pp.explicit`, `pp.proofs`
and `pp.deepTerms`, the two types agree byte for byte, as do their raw expression trees down
to binder names, binder info, `let` non-dependency flags and universe-level arguments, and
both carry the single universe parameter `u`. Only the proofs differed: the copy here spelled
out a universe-polymorphic form of the descent argument for sheaves of `Type u` on a category
in `Type (u + 1)`, where the surviving proof obtains the same conclusion from
`CategoryTheory.Sheaf.nonempty_isColimitCoforkOfKernelPair` directly. That machinery was
`private`, so no module could reach it, and the duplicated public theorems made the library
umbrella fail at import resolution. The `public import` above re-exports the surviving
declarations, so every name this module used to provide is still available through it.

The same held of `AlgebraicGeometry.Space.singleton_mem_bigFppf_topology`, which stood here
and in `StacksFrontier.AlgebraicGeometry.Spaces.Presentation` with the same signature; the copy
there survives and reaches consumers of this module through the import chain above.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
-/
