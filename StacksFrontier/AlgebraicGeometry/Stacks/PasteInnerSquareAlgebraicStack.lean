module

public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Cancelling the inner square of a pasted rectangle of algebraic stacks

Let `P` be a 2-fibre product of a cospan `g : 𝒞 ⟶ ℬ`, `f : 𝒜 ⟶ ℬ` of algebraic stacks over `S`,
let `k : 𝒟 ⟶ 𝒞` be a further 1-morphism, and let `Sq` be a 2-fibre product of the composed
cospan `(k ≫ g, f)`. Reassociating `Sq` gives a square over `(g, f)`, and the pre-morphism `p`
from it to `P` supplied by terminality cuts out the *inner* square
`CategoryTheory.Bicategory.pasteInnerSq P p` over the cospan `(k, P.fst)`:

```text
Sq.pt ---Sq.fst---> 𝒟
  |                 |
 p.hom              k
  v                 v
P.pt ----P.fst----> 𝒞
```

This module proves that inner square is a 2-fibre product. It is
`AlgebraicGeometry.Stack.isTwoFibreProduct_pasteInnerSq` read one 2-category up, in the
2-category of algebraic stacks over `S` rather than in the ambient 2-category of categories
fibred in groupoids. The distinction matters to a consumer: the point-set lemmas about a
2-cartesian square of algebraic stacks, such as
`AlgebraicGeometry.Stack.AlgebraicStacks.image_preimage_eq_preimage_image_of_isTwoFibreProduct`,
ask for terminality in the 2-category of algebraic stacks, and terminality there does *not*
follow from terminality downstairs unless some square over the cospan is known to have a 2-fibre
product underneath it.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_pasteInnerSqAlgebraicStacks`: the inner square cut
  out by `p` is a 2-fibre product of `(k, P.fst)` in the 2-category of algebraic stacks.

## Implementation notes

No 2-cell compatibility square is written by hand. The filler of the inner square is the first
comparison 2-cell `p.isoFst` of the terminality pre-morphism, by the definition of
`CategoryTheory.Bicategory.pasteInnerSq`, and the only other pre-morphism used is the one
terminality of the canonical square supplies.

The argument is the one of `AlgebraicGeometry.Stack.isTwoFibreProduct_pasteInnerSq`, with the
canonical 2-fibre product taken in the 2-category of algebraic stacks
(`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`): the canonical square `Q₀` of
`(k, P.fst)` receives a pre-morphism `q` from the inner square, pasting `Q₀` onto `P` recovers a
pre-morphism `Sq ⟶ P.pasteFst Q₀` whose underlying 1-morphism is that of `q`, and both squares
are 2-fibre products of the composed cospan, so that 1-morphism is an equivalence by
`AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks`. The transport of
terminality is then run on the squares of categories fibred in groupoids underlying these ones —
the square underlying `Q₀` is the canonical one there on the nose — and
`CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying` brings the conclusion back up, the
2-category of algebraic stacks being a full sub-2-category.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒜 ℬ 𝒞 𝒟 : AlgebraicStacks.{u, w} B S hS} {g : 𝒞 ⟶ ℬ} {f : 𝒜 ⟶ ℬ}

/-- **Cancelling the inner square of a pasted rectangle of algebraic stacks.** Let `P` be a
2-fibre product of a cospan `(g, f)` of algebraic stacks over `S`, let `k` be a 1-morphism into
the source of `g`, and let `Sq` be a 2-fibre product of the composed cospan `(k ≫ g, f)`
together with a pre-morphism `p` from the rectangle it defines over `(g, f)` to `P`. Then the
inner square cut out by `p` — the apex of `Sq` over `(k, P.fst)` — is a 2-fibre product in the
2-category of algebraic stacks.

This is the converse of `CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`, and it is
`AlgebraicGeometry.Stack.isTwoFibreProduct_pasteInnerSq` with the canonical 2-fibre product taken
among algebraic stacks. -/
noncomputable def isTwoFibreProduct_pasteInnerSqAlgebraicStacks
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    {k : 𝒟 ⟶ 𝒞} {Sq : Bicategory.TwoCommSq (k ≫ g) f}
    (hSq : Bicategory.IsTwoFibreProduct Sq)
    (p : Bicategory.TwoCommSq.PreHom (Bicategory.pasteOuterSq k Sq) P) :
    Bicategory.IsTwoFibreProduct (Bicategory.pasteInnerSq P p) := by
  classical
  set Q₀ := twoFibreProductSquareAlgebraicStacks B S hS k P.fst with hQ₀def
  have hQ₀ : Bicategory.IsTwoFibreProduct Q₀ :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS k P.fst
  set q := Bicategory.twoFibreProductPreHom hQ₀ (Bicategory.pasteInnerSq P p) with hqdef
  have hequiv :
      (Bicategory.pasteFstPreHom P Q₀ p q).hom.hom.hom.toFunctor.IsEquivalence :=
    isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hSq
      (Bicategory.isTwoFibreProduct_pasteFst P hP Q₀ hQ₀)
      (Bicategory.pasteFstPreHom P Q₀ p q)
  exact Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        k.hom P.fst.hom)
      q.underlying hequiv)

end AlgebraicGeometry.Stack

end
