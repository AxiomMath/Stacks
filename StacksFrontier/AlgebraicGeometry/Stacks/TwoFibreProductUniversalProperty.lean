module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory

/-!
# The 2-fibre product of algebraic stacks (Stacks 04T2)

**Stacks 04T2** says two things about a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of algebraic stacks over
a scheme `S` contained in a big fppf site: that the 2-fibre product `𝒵 ×_𝒴 𝒳` is again an
algebraic stack, and that it is *also* the 2-fibre product in the 2-category of algebraic stacks
over `(Sch/S)_fppf` — not merely in the ambient 2-category of categories fibred in groupoids.

The first assertion is Stacks 04TF, `AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct`,
which is already in the library in the greater generality the source states it in: it needs only
that `𝒴` be a stack with diagonal representable by algebraic spaces. This file supplies the
second.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProduct`: the canonical 2-fibre product of a
  cospan of algebraic stacks, as an object of the 2-category of algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids`: a
  2-commutative square of algebraic stacks whose underlying square of categories fibred in
  groupoids is a 2-fibre product is a 2-fibre product of algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFinalTwoCommSq_twoFibreProductSquare`:
  **Stacks 04T2**, the 2-categorical universal property — the canonical square
  `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare` is a 2-fibre product in the
  sense of Stacks 003Q in the 2-category of algebraic stacks; its 1-truncated form is
  `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFinalTwoCommSq_of_isTwoFibreProduct`: for algebraic
  stacks the 1-truncated notion already implies the one of Stacks 003Q.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids`: the
  converse of the first — for a cospan of algebraic stacks the implication also runs upwards,
  because the cospan has a 2-fibre product whose apex is again an algebraic stack.

## Implementation notes

The 2-category of algebraic stacks is a *full* sub-2-category of the 2-category of categories
fibred in groupoids, i.e. a `CategoryTheory.Bicategory.InducedBicategory`. Being a 2-fibre product
there is therefore a weaker condition than being one upstairs, since the universal property of
Stacks 003Q is tested against fewer 2-commutative squares — only those whose apex is an algebraic
stack. So the implication runs from the ambient 2-category down, and that is exactly
`CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying`: nothing about algebraic
stacks is used beyond fullness, and the whole content is that the inclusion of a full
sub-2-category is bijective on 1-morphisms and on 2-morphisms.

Both results here are therefore one application of that transfer. The apex of the canonical square
is an algebraic stack by
`AlgebraicGeometry.Stack.AlgebraicStacks.isAlgebraicStack_twoFibreProductSquare_pt`,
which is how `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare` is built, and the
square underlying it is `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` on the nose —
each field of the forgetful image is the field the canonical square was built from — so the
universal property proved for the latter applies with no comparison to insert. The universes are
the ones the 2-category of algebraic stacks is instantiated at, `{u, u, u + 1, u + 1}`, which is
an admissible instantiation of the ambient construction.

They are data, not propositions, since `CategoryTheory.Bicategory.IsTwoFibreProduct` is a terminal
object structure.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

add_to_stacks 04T2 "the 2-fibre product is an algebraic stack"
  AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct

namespace AlgebraicStacks

variable {𝒵 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- The canonical 2-fibre product `𝒵 ×_𝒴 𝒳` of a cospan of algebraic stacks over `S`, as an
object of the 2-category of algebraic stacks: the apex of
`AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare`, which is an algebraic stack by
Stacks 04TF.

This is an abbreviation, so a consumer may use it and `(twoFibreProductSquare B S hS g f).pt`
interchangeably. -/
abbrev twoFibreProduct (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) : Stack.AlgebraicStacks.{u, w} B S hS :=
  (twoFibreProductSquare B S hS g f).pt

/-- **A 2-commutative square of algebraic stacks whose underlying square of categories fibred in
groupoids is a 2-fibre product is a 2-fibre product of algebraic stacks.**

The 2-category of algebraic stacks is a full sub-2-category of the 2-category of categories fibred
in groupoids, and `AlgebraicGeometry.Stack.AlgebraicStacks.toCatFiberedInGroupoids` is the
inclusion on 2-commutative squares; the transfer is
`CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying`. -/
noncomputable def isTwoFibreProduct_of_toCatFiberedInGroupoids {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct (toCatFiberedInGroupoids B S hS P)) :
    Bicategory.IsTwoFibreProduct P :=
  Bicategory.isTwoFibreProduct_of_underlying hP

/-- **Stacks 04T2, the 2-categorical universal property, 1-truncated.** The canonical 2-fibre
product square `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare` of a cospan of
algebraic stacks over `S` is terminal in the quotient category of 2-commutative squares *in the
2-category of algebraic stacks over* `(Sch/S)_fppf`, not merely in the ambient 2-category of
categories fibred in groupoids. The form with the 2-fibre product of Stacks 003Q is
`AlgebraicGeometry.Stack.AlgebraicStacks.isFinalTwoCommSq_twoFibreProductSquare`.

That its apex is an algebraic stack is Stacks 04TF; see
`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct`. -/
noncomputable def isTwoFibreProduct_twoFibreProductSquare (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) :
    Bicategory.IsTwoFibreProduct (twoFibreProductSquare B S hS g f) :=
  isTwoFibreProduct_of_toCatFiberedInGroupoids B S hS _
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom f.hom)

/-- **A 2-fibre product of algebraic stacks is also a 2-fibre product of categories fibred in
groupoids.** This is the converse of
`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids`, and it
is false for a general full sub-2-category; what makes it true here is that the cospan has a
2-fibre product in the ambient 2-category whose apex happens to be an algebraic stack again
(Stacks 04TF). Any 2-fibre product of algebraic stacks is then isomorphic to that one already in
the 2-category of algebraic stacks, and the isomorphism is carried down by
`CategoryTheory.Bicategory.TwoCommSq.underlyingFunctor`. -/
noncomputable def isTwoFibreProduct_toCatFiberedInGroupoids {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P) :
    Bicategory.IsTwoFibreProduct (toCatFiberedInGroupoids B S hS P) :=
  Bicategory.isTwoFibreProduct_underlying
    (twoFibreProductSquare B S hS g f) hP
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom f.hom)

/-- **In the 2-category of algebraic stacks the two notions of 2-fibre product agree.** A terminal
object of the quotient category of 2-commutative squares over a cospan of algebraic stacks is a
2-fibre product in the sense of Stacks 003Q: its underlying square of categories fibred in groupoids
is a 2-fibre product there, whose legs detect 2-cells, and the 2-cells of the full sub-2-category
of algebraic stacks are those of categories fibred in groupoids. -/
noncomputable def isFinalTwoCommSq_of_isTwoFibreProduct {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P) :
    Bicategory.IsFinalTwoCommSq P :=
  Bicategory.isFinalTwoCommSq_of_legsDetect hP
    (Bicategory.legsDetectTwoCells_of_underlying
      (CatFiberedInGroupoids.legsDetectTwoCells_of_isTwoFibreProduct.{u, u, u + 1, u + 1}
        (isTwoFibreProduct_toCatFiberedInGroupoids B S hS P hP)))

/-- **Stacks 04T2, the 2-categorical universal property.** The canonical 2-fibre product square
`AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare` of a cospan of algebraic stacks
over `S` is a 2-fibre product in the sense of Stacks 003Q *in the 2-category of algebraic stacks
over* `(Sch/S)_fppf`, not merely in the ambient 2-category of categories fibred in groupoids: a
final object of the 2-category of 2-commutative diagrams over the cospan, any two 1-morphisms into
it being isomorphic by a unique 2-morphism.

That its apex is an algebraic stack is Stacks 04TF; see
`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct`. -/
@[stacks 04T2 "the 2-categorical universal property"]
noncomputable def isFinalTwoCommSq_twoFibreProductSquare (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) :
    Bicategory.IsFinalTwoCommSq (twoFibreProductSquare B S hS g f) :=
  Bicategory.isFinalTwoCommSq_of_underlying
    (CatFiberedInGroupoids.isFinalTwoCommSq_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom f.hom)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
