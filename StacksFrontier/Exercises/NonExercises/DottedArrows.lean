module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DottedArrows.Composition
public import StacksFrontier.CategoryTheory.DottedArrows.Defs

/-!
# Dotted arrows in a valuative diagram, and dotted arrows for a composite

For a 2-commutative square whose left edge comes from the inclusion of a valuation ring's
fraction field and whose right edge is a morphism of algebraic stacks, a *dotted arrow* is a
diagonal 1-morphism with two compatible 2-morphisms, and a morphism of dotted arrows is a
compatible 2-morphism between the diagonals. For a composite morphism, the category of dotted
arrows is equivalent to an intermediate category fibred in groupoids over the dotted arrows of
the lower square, whose fibres are the categories of dotted arrows of the upper squares.

Both groups of statements already exist for an arbitrary square in a bicategory, respectively
an arbitrary locally groupoidal bicategory, which covers the squares of represented schemes
and algebraic stacks of the source. `CategoryTheory.DottedArrow` records a dotted arrow with
its pasting equation and `CategoryTheory.DottedArrow.Hom` a morphism of dotted arrows with both
compatibility equations; the category instance on them is what later valuative-criterion
statements use. The intermediate category is
`CategoryTheory.DottedArrow.WithFactorization`, with projection
`CategoryTheory.DottedArrow.compose`; the fibre identification is a strict isomorphism of
categories, which in particular gives the equivalence asserted by the source.

The groupoid assertion of Stacks 0CLC is likewise already available in that generality: in a
locally groupoidal bicategory every morphism of dotted arrows is invertible, which is
`CategoryTheory.instGroupoidDottedArrow`. Its setoid assertion is a condition on the relative
diagonal of a morphism of algebraic stacks and is stated where that notion lives.

Composition is diagrammatic throughout, so `j ≫ y` is the source's `y ∘ j`.

## References

* [Stacks Project, Tag 0CLA](https://stacks.math.columbia.edu/tag/0CLA)
* [Stacks Project, Tag 0CLC](https://stacks.math.columbia.edu/tag/0CLC)
* [Stacks Project, Tag 0CLF](https://stacks.math.columbia.edu/tag/0CLF)
-/

add_to_stacks 0CLA "dotted arrows" CategoryTheory.DottedArrow
add_to_stacks 0CLA "morphisms of dotted arrows" CategoryTheory.DottedArrow.Hom
add_to_stacks 0CLC "groupoid" CategoryTheory.instGroupoidDottedArrow
add_to_stacks 0CLF "equivalence with the intermediate category"
  CategoryTheory.DottedArrow.toWithFactorization_isEquivalence
add_to_stacks 0CLF "fibration over the lower dotted-arrow category"
  CategoryTheory.DottedArrow.compose_isFiberedInGroupoids
add_to_stacks 0CLF "fibre categories are upper dotted-arrow categories"
  CategoryTheory.DottedArrow.fiber_categoryIso
