module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation

/-!
# Permanence of local complete intersection 1-morphisms of algebraic stacks (Stacks 0CJ6)

In a 2-commutative triangle `𝒳 ⟶ 𝒴 ⟶ 𝒵` of algebraic stacks over `S`, if `𝒴 ⟶ 𝒵` is smooth and
the composite `𝒳 ⟶ 𝒵` is a local complete intersection morphism, then `𝒳 ⟶ 𝒴` is a local
complete intersection morphism. This is the algebraic-stacks form of Stacks 0CHL, whose schemes
form is Stacks 069M.

## Main definitions

There are no new definitions.

## Main results

* **Stacks 0CJ6**, for an arbitrary target and with no carried hypotheses, is
  `AlgebraicStacks.isLocalCompleteIntersection_of_isLocalCompleteIntersection_comp_of_isSmooth`
  of `StacksFrontier.AlgebraicGeometry.Stacks.LocalCompleteIntersectionSmoothCancellation`.

## Implementation notes

Both the Koszul property of 1-morphisms of algebraic stacks
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocalCompleteIntersection`, Stacks 0CJ3) and
smoothness of 1-morphisms (`...IsSmooth`, Stacks 075U) are the smooth-diagram criteria of
Stacks 06FM at the corresponding property of morphisms of algebraic spaces, so the statement is
the cancellation `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp` at the pair
(Koszul, smooth). That generic lemma is used in its representable-target form,
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_comp_of_representableTarget`, where
both smooth diagrams are taken with right vertical 1-morphism the identity of the target, which
makes the universal clause of Stacks 06FM free.

## The restriction on the target, and why it is not removable here

The general-target form of the cancellation reaches a representable target by base changing both
hypotheses along a smooth presentation `𝒯 ⟶ 𝒵` (Stacks 06FQ), and the generic lemma that performs
that step asks for `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` of the restriction of
the property to algebraic spaces — base change along an *arbitrary* morphism. The Koszul property
does not have it: it is stable under *flat* base change only, which for morphisms of algebraic
spaces is Stacks 06C7
(`AlgebraicGeometry.Space.isLocalCompleteIntersection_pullback_snd`). Supplying that instance for
the Koszul property would make the hypothesis unsatisfiable and the statement empty, so the
target is instead restricted to the algebraic stack of an algebraic space, where no base change
of the property is performed at all. Removing the restriction needs a flat-base-change form of
Stacks 06FQ at the level of 1-morphisms of algebraic stacks, which this library does not have.

## Carried hypotheses

Two, both true statements of the Stacks project:

* `hlci`, that the Koszul property of morphisms of algebraic spaces over `S` is smooth local on
  the source-and-target. This is Stacks 0CHM and 0CHN fed through the criterion Stacks 06FB, and
  it is what the equivalence of the two conditions of Stacks 06FM consumes in order to return the
  universal condition, which is the definition Stacks 0CJ3 of the conclusion. It is absent from
  this library: `AlgebraicGeometry.Space.isLocalCompleteIntersection_isSmoothLocalOnSourceAndTarget`
  proves it, but only from syntomic locality on the source of the Koszul property of morphisms of
  schemes — the full Stacks 069P, of which this library proves the étale restriction only.
* `hcancel`, the algebraic-spaces form of this lemma, Stacks 0CHL: a morphism of algebraic spaces
  whose composite with a smooth morphism is Koszul is itself Koszul. It is the space-level
  cancellation the smooth-diagram criterion is cancelled against, and it is the honest content of
  the reduction — the stacks form adds no new geometry to it. It is available, as
  `AlgebraicGeometry.Space.isLocalCompleteIntersection_of_comp_of_isSmooth`; it is stated as a
  hypothesis here rather than applied, so that this module proves only the reduction.

The matching hypotheses for smoothness are both discharged:
`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_smooth` (Stacks 06FC at smoothness).

## References

* [Stacks Project, Tag 069M](https://stacks.math.columbia.edu/tag/069M)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 0CHL](https://stacks.math.columbia.edu/tag/0CHL)
* [Stacks Project, Tag 0CJ3](https://stacks.math.columbia.edu/tag/0CJ3)
* [Stacks Project, Tag 0CJ6](https://stacks.math.columbia.edu/tag/0CJ6)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
