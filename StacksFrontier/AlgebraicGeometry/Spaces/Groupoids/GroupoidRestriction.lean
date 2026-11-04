module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction.Arrows
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction.Restrict

/-!
# Restriction of a groupoid in algebraic spaces (Stacks 044B)

Let `G` be a groupoid in algebraic spaces over an algebraic space `B` over a scheme `S` of a big
fppf site, in the sense of Stacks 043W, and let `g : U' ⟶ G.objects` be any morphism of algebraic
spaces to its space of objects. The *restriction* of `G` along `g` is the groupoid in algebraic
spaces whose objects are `U'` and whose arrows are the iterated fibre product parametrizing an
arrow of `G` together with a lift of each of its two endpoints along `g`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrows`: the space of arrows of the
  restriction, with `restrictionSource`, `restrictionTarget` and `restrictionArrowsToArrows` its
  three projections.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Restriction`: the specification of the
  restriction — the restricted groupoid, the identifications of its object and arrow spaces and
  of its structure maps, its canonical morphism to `G`, and pointwise full faithfulness of that
  morphism.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrict`: the restriction itself, satisfying
  that specification.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrict_isRestriction`: **Stacks 044B** — the
  restriction is a groupoid in algebraic spaces over `B` with objects `U'`, arrows the fibre
  product `U' ×_{g, U, t} R ×_{s, U, g} U'`, source and target the two outer projections and
  composition computed by `c` on the underlying arrows; `g` and the projection to `R` form a
  morphism of groupoids to `G`, and on `T`-points, and on `T`-points over any point of `B(T)`,
  this morphism is the restriction of the groupoid of points of `G` along `U'(T) ⟶ U(T)`.

## DELIBERATE OWNERSHIP EXCEPTION — this is a Chapter 78 tag

Stacks 044B is `spaces-groupoids`, **Chapter 78**. It is stated here, as Stacks 044Q is in the
sibling file `QuotientStack.lean` and Stacks 043W in `GroupoidInSpaces.lean`, because the
Chapter 93–101 results that need the restriction of a groupoid in algebraic spaces cannot be
stated without it.

## Implementation notes

Every declaration of this file lives in `AlgebraicGeometry.GroupoidInAlgebraicSpaces` rather than
in `AlgebraicGeometry`. This is forced: `AlgebraicGeometry.restrictionArrows`,
`restrictionSource`, `restrictionTarget` and `restrictionArrowsToArrows` **already exist**, for
the groupoid *schemes* of Stacks 02VB, in
`StacksFrontier/AlgebraicGeometry/Groupoids/Stabilizer/Restriction.lean`. Those are a different
notion — fibre products in `Over S` rather than in the category of algebraic spaces over a big
fppf site — and since all four are `def`s producing data, declaring these at
`AlgebraicGeometry.*` would be a duplicate-constant error rather than a shadow.

`fiberProductFst`, `fiberProductSnd` and `fiberProduct_condition` are the two projections of
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` and their defining compatibility, and are
spelled after it.

`eq_id_of_idempotent_isIso` is stated for an arbitrary endomorphism that is an isomorphism, which
is strictly more general than the groupoid form it is used at; the groupoid form is recovered by
bare application.

## References

* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)

This file only re-exports its parts: `GroupoidRestriction/Arrows.lean`,
`GroupoidRestriction/Composition.lean` and `GroupoidRestriction/Restrict.lean`.
-/
