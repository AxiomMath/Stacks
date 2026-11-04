module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation

/-!
# Presentations of algebraic spaces (Stacks 0263)

A presentation of an algebraic space over `S` consists of a scheme `U` over `S`, an étale
equivalence relation `R` on `U`, and a surjective étale map from `U` to the space which
identifies `R` with the fibre product of `U` over the space.

## Main definitions

* `AlgebraicGeometry.Space.Presentation`, re-exported from
  `StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation`.

## Main results

The fields of `AlgebraicGeometry.Space.Presentation` give the étale equivalence relation, the
surjective étale atlas, and its kernel-pair property.

## Implementation notes

The structure itself lives in `StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation`, which
this module re-exports. It was declared here as well, under the same fully-qualified name and
with the same `@[stacks 0263]` tag; the two declarations elaborated to byte-identical types for
the structure and for all nine of its projections, so the copy carried no mathematics of its
own, while a structure is data and a duplicated datum cannot be co-imported — the two modules
together made the library umbrella fail at import resolution. The `public import` above
re-exports the surviving declaration, so every name this module used to provide is still
available through it.

## References

* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
-/
