module

public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# The square underlying a 2-fibre product of algebraic stacks

`CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying` says that a full sub-2-category
inherits the 2-fibre products of the ambient one: a 2-commutative square of an induced
bicategory whose underlying square is a 2-fibre product is itself one. This file proves the
**opposite direction** for the 2-category of algebraic stacks (Stacks 03YP): a 2-fibre product
*there* has a 2-fibre product of categories fibred in groupoids underneath it.

That direction is **not** formal, and it is false for a general full sub-2-category: a square of
the sub-2-category can be terminal among the squares whose apex lies in the sub-2-category and
fail to be terminal among all squares of the ambient 2-category. What makes it true here is that
the sub-2-category is **closed under the construction** — the apex of the canonical 2-fibre
product of a cospan of algebraic stacks is an algebraic stack, which is Stacks 04TF, proved as
`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProductSquare` — so the ambient 2-fibre product
is already available upstairs and terminality upstairs pins the given square to it.

## Main results

* `CategoryTheory.Bicategory.isTwoFibreProduct_underlying`: the general statement, with the
  closure property as an explicit hypothesis — one square of the induced bicategory whose
  underlying square is a 2-fibre product.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_underlying_algebraicStacks`: the statement for the
  2-category of algebraic stacks, where Stacks 04T2 supplies that hypothesis.

## Implementation notes

The general lemma lives here rather than beside `isTwoFibreProduct_of_underlying` for two
reasons: its hypothesis is exactly what Stacks 04TF supplies and nothing else in the library
supplies, so stating it next to its only application keeps that dependency visible; and proving
it needs `CategoryTheory.Bicategory.isTwoFibreProduct_of_section`, which would enlarge the import
cone of the induced-bicategory file.

The 2-category of categories fibred in groupoids is a 2-category *over* the base site: its
2-morphisms are vertical, so the filler of a 2-commutative square is a `BasedNatIso` and the
squares here are the **relative** 2-fibre products throughout. The absolute notion, whose
comparison isomorphism on an object is arbitrary, is a different and inequivalent one and does
not appear; there is no choice to make, because the ambient 2-category is already relative.

The proof is the one terminality argument that the two universal properties share. Terminality of
the given square `P` upstairs and of the closure witness `R` upstairs — the latter from
`isTwoFibreProduct_of_underlying` — give pre-morphisms both ways, and the composite `P ⟶ R ⟶ P`
agrees with the identity in the quotient category of Stacks 003O, so the mediating 2-cell of that
agreement is a section of the comparison downstairs. `isTwoFibreProduct_of_section` then transfers
terminality from `R.underlying` to `P.underlying`. Both pre-morphisms and the 2-cell are choices,
so the conclusion — which is data — is read off its non-emptiness.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits


namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The square of categories fibred in groupoids underlying a 2-fibre product of algebraic
stacks is a 2-fibre product.** If a 2-commutative square `P` over a cospan of algebraic stacks
over `S` is a 2-fibre product in the 2-category of algebraic stacks (Stacks 03YP), then the
square underlying it is a 2-fibre product in the ambient 2-category of categories fibred in
groupoids over the big fppf site of `S`.

The implication runs this way and not the other: it takes the hypothesis at the level of
algebraic stacks and concludes at the level of categories fibred in groupoids, which is the
strictly stronger conclusion. The reverse implication is the formal
`CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying`, and it has no general converse; what
makes this one available is `CategoryTheory.Bicategory.isTwoFibreProduct_underlying` together with
Stacks 04T2, whose canonical square of the same cospan is a 2-fibre product of algebraic stacks
whose underlying square is the canonical square of categories fibred in groupoids, a 2-fibre
product unconditionally. That the canonical apex is again an algebraic stack is Stacks 04TF. -/
noncomputable def isTwoFibreProduct_underlying_algebraicStacks
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵}
    (P : Bicategory.TwoCommSq f g) (hP : Bicategory.IsTwoFibreProduct P) :
    Bicategory.IsTwoFibreProduct P.underlying :=
  Bicategory.isTwoFibreProduct_underlying (twoFibreProductSquareAlgebraicStacks B S hS f g) hP
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom g.hom)

end AlgebraicGeometry.Stack

end
