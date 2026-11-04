module

public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.AbstractCancelSnd

/-!
# Cancelling a factor of an iterated 2-fibre product of algebraic stacks (Stacks 02XD)

Let `p : 𝒜 ⟶ 𝒳` and `q : ℬ ⟶ 𝒳` be 1-morphisms of algebraic stacks over the big fppf site of
`S`, let `c : 𝒰 ⟶ ℬ`, and let `G : 𝒰 ⟶ 𝒳` be identified with `c ≫ q` by an invertible 2-cell.
The canonical 2-fibre products of Stacks 04T2 give the iterated apex `(𝒜 ×_𝒳 ℬ) ×_ℬ 𝒰`, and this
file exhibits that apex as a 2-fibre product of the outer cospan `(p, G)` **in the 2-category of
algebraic stacks**:

```text
(𝒜 ×_𝒳 ℬ) ×_ℬ 𝒰  ≃  𝒜 ×_𝒳 𝒰
```

This is **Stacks 02XD** read as a statement about 2-fibre products rather than about apexes, at
the level at which a consumer about algebraic stacks can use it. The 1-morphism statement
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare` is about categories
fibred in groupoids; a statement whose hypothesis is "this square of *algebraic stacks* is a
2-fibre product" — as `AlgebraicGeometry.Stack.isQuasiCompactStack_of_isTwoFibreProduct` is, and
as Stacks 050V and 050W need — cannot be applied to it.

Also recorded here, because every consumer needs it: the comparison of an arbitrary 2-commutative
square of algebraic stacks with the canonical 2-fibre product square has composites with the two
projections equal to the legs of the given square *on the nose*.

## Main definitions

* `AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks`: the strict comparison of a
  2-commutative square of algebraic stacks with the canonical 2-fibre product square.
* `AlgebraicGeometry.Stack.cancelSndSquareAlgebraicStacks`: the iterated 2-fibre product, read as
  a 2-commutative square of algebraic stacks over the outer cospan.
* `AlgebraicGeometry.Stack.cancelSndEquivSquareAlgebraicStacks`: the same, with the inner apex
  replaced by any algebraic stack comparable to it.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_cancelSndSquareAlgebraicStacks`: that square is a
  2-fibre product of algebraic stacks.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_cancelSndEquivSquareAlgebraicStacks`: the same at a
  recognised inner 2-fibre product.

## Implementation notes

Nothing is re-proved. The 2-category of algebraic stacks is the induced bicategory of Stacks 03YP,
whose 1-morphisms and 2-morphisms are those of the ambient 2-category of categories fibred in
groupoids, and the legs and filler of
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` are those of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` wrapped by
`CategoryTheory.Bicategory.InducedBicategory.mkHom` and `.isoMk`. So each square written here has
the corresponding square of categories fibred in groupoids as its
`CategoryTheory.Bicategory.TwoCommSq.underlying` *on the nose*, and
`CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying` — the formal remark that a full
sub-2-category inherits the 2-fibre products of the ambient one, Stacks 003Q — transports
terminality with no further argument. The same holds for the strict comparison, which is
`CategoryTheory.Bicategory.TwoCommSq.PreHom.ofUnderlying` applied to
`CategoryTheory.CatFiberedInGroupoids.canonicalPreHom`, so both of its nose-compatibilities are
inherited.

`AlgebraicGeometry.Stack.cancelSndEquivSquareAlgebraicStacks` at the identity comparison has the
same apex as `AlgebraicGeometry.Stack.cancelSndSquareAlgebraicStacks`, so the latter is formally
redundant; it is kept because it is the hypothesis-free form of Stacks 02XD at this level, and it
is the form a consumer working with the canonical square reaches for.

No `@[stacks 02XD]` attribute: that tag stays on
`CategoryTheory.Limits.CategoricalPullback.assocComp` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Cancellation`, as the records of
`StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct` and
`StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstTwoFibreProduct` already rule.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒜 ℬ 𝒳 𝒲 𝒰 : AlgebraicStacks.{u, w} B S hS} (p : 𝒜 ⟶ 𝒳) (q : ℬ ⟶ 𝒳)

/-- **The strict comparison of a 2-commutative square of algebraic stacks with the canonical
2-fibre product square.** Its composites with the two projections of the canonical square are the
two legs of the given square on the nose, so both comparison 2-cells are identities; it is
`CategoryTheory.CatFiberedInGroupoids.canonicalPreHom` read in the 2-category of algebraic
stacks. -/
def canonicalPreHomAlgebraicStacks (T : Bicategory.TwoCommSq p q) :
    Bicategory.TwoCommSq.PreHom T (twoFibreProductSquareAlgebraicStacks B S hS p q) :=
  Bicategory.TwoCommSq.PreHom.ofUnderlying
    (CatFiberedInGroupoids.canonicalPreHom.{u, u, u + 1, u + 1} p.hom q.hom T.underlying)

/-- The strict comparison composed with the first projection of the canonical square is the first
leg of the given square. -/
theorem canonicalPreHomAlgebraicStacks_hom_comp_fst (T : Bicategory.TwoCommSq p q) :
    (canonicalPreHomAlgebraicStacks B S hS p q T).hom ≫
      (twoFibreProductSquareAlgebraicStacks B S hS p q).fst = T.fst := rfl

/-- The strict comparison composed with the second projection of the canonical square is the
second leg of the given square. -/
theorem canonicalPreHomAlgebraicStacks_hom_comp_snd (T : Bicategory.TwoCommSq p q) :
    (canonicalPreHomAlgebraicStacks B S hS p q T).hom ≫
      (twoFibreProductSquareAlgebraicStacks B S hS p q).snd = T.snd := rfl

variable (cmp : 𝒲 ⟶ (twoFibreProductSquareAlgebraicStacks B S hS p q).pt)

variable (c : 𝒰 ⟶ ℬ) (G : 𝒰 ⟶ 𝒳) (θ : c ≫ q ≅ G)

/-- The outer cospan `(p, G)` read on the iterated 2-fibre product `(𝒜 ×_𝒳 ℬ) ×_ℬ 𝒰` of
algebraic stacks: the projection to `𝒜` is the composite of the two projections and the
projection to `𝒰` is the outer one.

The filler is that of `CategoryTheory.CatFiberedInGroupoids.cancelSndSquare` read upstairs, so
the square underlying this one is that one on the nose. -/
noncomputable def cancelSndSquareAlgebraicStacks : Bicategory.TwoCommSq p G where
  pt := twoFibreProductAlgebraicStack B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS p q).snd c
  fst := (twoFibreProductSquareAlgebraicStacks B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS p q).snd c).fst ≫
    (twoFibreProductSquareAlgebraicStacks B S hS p q).fst
  snd := (twoFibreProductSquareAlgebraicStacks B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS p q).snd c).snd
  iso := Bicategory.InducedBicategory.isoMk
    (CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} p.hom q.hom c.hom G.hom
      (Bicategory.InducedBicategory.isoHom θ)).iso

/-- **Stacks 02XD in the 2-category of algebraic stacks.** The iterated 2-fibre product
`(𝒜 ×_𝒳 ℬ) ×_ℬ 𝒰`, with the composite of its two projections to `𝒜` and its own projection to
`𝒰`, is a 2-fibre product of the outer cospan `p : 𝒜 ⟶ 𝒳`, `G : 𝒰 ⟶ 𝒳` of algebraic stacks. -/
noncomputable def isTwoFibreProduct_cancelSndSquareAlgebraicStacks :
    Bicategory.IsTwoFibreProduct (cancelSndSquareAlgebraicStacks B S hS p q c G θ) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1}
      p.hom q.hom c.hom G.hom (Bicategory.InducedBicategory.isoHom θ))


/-- The outer cospan `(p, G)` read on the outer product `𝒲 ×_ℬ 𝒰`, where `𝒲` is an algebraic
stack comparable to the canonical inner apex `𝒜 ×_𝒳 ℬ` by `cmp`: the projection to `𝒜` is the
composite of the outer projection with `cmp` followed by the first inner projection, and the
projection to `𝒰` is the outer one. -/
noncomputable def cancelSndEquivSquareAlgebraicStacks : Bicategory.TwoCommSq p G where
  pt := twoFibreProductAlgebraicStack B S hS
    (cmp ≫ (twoFibreProductSquareAlgebraicStacks B S hS p q).snd) c
  fst := (twoFibreProductSquareAlgebraicStacks B S hS
      (cmp ≫ (twoFibreProductSquareAlgebraicStacks B S hS p q).snd) c).fst ≫
    (cmp ≫ (twoFibreProductSquareAlgebraicStacks B S hS p q).fst)
  snd := (twoFibreProductSquareAlgebraicStacks B S hS
    (cmp ≫ (twoFibreProductSquareAlgebraicStacks B S hS p q).snd) c).snd
  iso := Bicategory.InducedBicategory.isoMk
    (CatFiberedInGroupoids.cancelSndEquivSquare.{u, u, u + 1, u + 1} p.hom q.hom cmp.hom
      c.hom G.hom (Bicategory.InducedBicategory.isoHom θ)).iso

/-- **Stacks 02XD at a recognised inner 2-fibre product, in the 2-category of algebraic stacks.**
If the underlying functor of `cmp` is an equivalence of categories — which it is as soon as `𝒲`
carries a 2-fibre product square of the inner cospan, by
`AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks` — then the outer
product `𝒲 ×_ℬ 𝒰` is a 2-fibre product of the cospan `p : 𝒜 ⟶ 𝒳`, `G : 𝒰 ⟶ 𝒳`. -/
noncomputable def isTwoFibreProduct_cancelSndEquivSquareAlgebraicStacks
    (hcmp : cmp.hom.hom.toFunctor.IsEquivalence) :
    Bicategory.IsTwoFibreProduct (cancelSndEquivSquareAlgebraicStacks B S hS p q cmp c G θ) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (CatFiberedInGroupoids.isTwoFibreProduct_cancelSndEquivSquare.{u, u, u + 1, u + 1}
      p.hom q.hom cmp.hom c.hom G.hom (Bicategory.InducedBicategory.isoHom θ) hcmp)

end AlgebraicGeometry.Stack

end
