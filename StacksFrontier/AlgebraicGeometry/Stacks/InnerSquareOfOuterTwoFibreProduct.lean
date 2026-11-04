module

public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# Recognising the inner factor of an iterated 2-fibre product (Stacks 02XD, backwards)

Let `p : 𝒜 ⟶ 𝒳` and `q : ℬ ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S`, let `c : 𝒰 ⟶ ℬ`
and let `G : 𝒰 ⟶ 𝒳` be identified with `c ≫ q` by an invertible 2-cell. Stacks 02XD, in the form
`AlgebraicGeometry.Stack.isTwoFibreProduct_cancelSndEquivSquareAlgebraicStacks`, runs *forwards*:
it builds the iterated apex `(𝒜 ×_𝒳 ℬ) ×_ℬ 𝒰` and recognises it as a 2-fibre product of the outer
cospan `(p, G)`.

This module runs it *backwards*. Given a 2-fibre product `P` of the inner cospan `(p, q)` and a
2-fibre product `N` of the outer cospan `(p, G)` — two squares with no relation imposed between
them — it exhibits the apex of `N` as a 2-fibre product of the cospan `(P.snd, c)`:

```text
N.pt ------------> 𝒰
  |                |
  |                c
  v                v
P.pt --P.snd-----> ℬ
```

That is the step a descent argument needs when the outer product is handed to it from elsewhere.
In the stack case of Stacks 0H29 the outer product is the fibre product of *schemes* `W ×_Y Z'`,
recognised as a 2-fibre product of represented stacks by
`AlgebraicGeometry.Stack.isTwoFibreProduct_schemeStackSquare`, while `P` is the base change
`𝒳 ×_Y Z'` of the stack; the conclusion is that `W ×_Y Z'` is the base change of the affine smooth
atlas `𝒰 = W ⟶ 𝒳 = ℬ` along the projection `𝒳 ×_Y Z' ⟶ 𝒳`, which is what makes that projection
surjective and open on points.

## Main definitions

* `AlgebraicGeometry.Stack.outerSquareOfInner`: the outer square that Stacks 02XD builds on the
  canonical inner 2-fibre product, with the comparison of `P` with the canonical square as its
  recognition datum.
* `AlgebraicGeometry.Stack.innerComparison`: the 1-morphism from `N.pt` to the canonical apex
  `P.pt ×_ℬ 𝒰`, supplied by terminality of that outer square.
* `AlgebraicGeometry.Stack.innerSquareOfOuter`: the square displayed above, with legs the
  composites of `innerComparison` with the two canonical projections.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_innerSquareOfOuter`: it is a 2-fibre product.
* `AlgebraicGeometry.Stack.innerSquareOfOuter_snd_iso` and
  `AlgebraicGeometry.Stack.innerSquareOfOuter_fst_comp_iso`: its second leg is the second leg of
  `N`, and its first leg followed by `P.fst` is the first leg of `N`, both up to an invertible
  2-cell. These are what identify the legs of the recognised square with the ones a consumer
  started from — on points the two agree, since `AlgebraicGeometry.Stack.pointsMap` does not see
  a 2-morphism.

## Implementation notes

No 2-cell compatibility square is proved by hand, and that is the point of routing the argument
the way it is routed here. The only pre-morphism written down is
`AlgebraicGeometry.Stack.innerPreHomOfOuter`, from `innerSquareOfOuter` to the *canonical* inner
square; its two comparison 2-cells are identities, because the legs of `innerSquareOfOuter` are
*defined* as the composites of `innerComparison` with the canonical projections, so its
compatibility square is the filler of `innerSquareOfOuter` unwound and closes by `simp`.

Everything else is terminality. `innerComparison` is an equivalence because `N` and
`outerSquareOfInner` are both 2-fibre products of `(p, G)`
(`AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks`), and
`CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to` then transports terminality of
the canonical inner square onto `innerSquareOfOuter`. The transport is run on the squares of
categories fibred in groupoids underlying these ones, which are the canonical ones there on the
nose, and `CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying` brings the conclusion back
up; the 2-category of algebraic stacks is a full sub-2-category, so nothing is lost.

The two leg identifications are the comparison 2-cells of the terminality pre-morphism, read
through the two equalities `cmp ≫ canonical.fst = P.fst` and `cmp ≫ canonical.snd = P.snd` of
`AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks`, which hold on the nose.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
-/

@[expose] public section

open CategoryTheory Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒜 ℬ 𝒳 𝒰 : AlgebraicStacks.{u, w} B S hS} {p : 𝒜 ⟶ 𝒳} {q : ℬ ⟶ 𝒳}
  {c : 𝒰 ⟶ ℬ} {G : 𝒰 ⟶ 𝒳}

/-- The outer square that Stacks 02XD builds on the canonical 2-fibre product of the inner cospan
`(P.snd, c)`, recognising `P` as the inner factor through
`AlgebraicGeometry.Stack.canonicalPreHomAlgebraicStacks`. -/
noncomputable abbrev outerSquareOfInner (P : Bicategory.TwoCommSq p q) (θ : c ≫ q ≅ G) :
    Bicategory.TwoCommSq p G :=
  cancelSndEquivSquareAlgebraicStacks B S hS p q
    (canonicalPreHomAlgebraicStacks B S hS p q P).hom c G θ

/-- **Stacks 02XD at the recognised inner product.** The outer square is a 2-fibre product of
`(p, G)`: the recognition datum is an equivalence because `P` and the canonical square are both
2-fibre products of `(p, q)`. -/
noncomputable def isTwoFibreProduct_outerSquareOfInner (P : Bicategory.TwoCommSq p q)
    (hP : Bicategory.IsTwoFibreProduct P) (θ : c ≫ q ≅ G) :
    Bicategory.IsTwoFibreProduct (outerSquareOfInner B S hS P θ) :=
  isTwoFibreProduct_cancelSndEquivSquareAlgebraicStacks B S hS p q
    (canonicalPreHomAlgebraicStacks B S hS p q P).hom c G θ
    (isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hP
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS p q)
      (canonicalPreHomAlgebraicStacks B S hS p q P))

/-- The pre-morphism from `N` to the outer square of Stacks 02XD, supplied by terminality of the
latter. -/
noncomputable abbrev innerPreHomToOuter (P : Bicategory.TwoCommSq p q)
    (hP : Bicategory.IsTwoFibreProduct P) (θ : c ≫ q ≅ G) (N : Bicategory.TwoCommSq p G) :
    Bicategory.TwoCommSq.PreHom N (outerSquareOfInner B S hS P θ) :=
  Bicategory.twoFibreProductPreHom (isTwoFibreProduct_outerSquareOfInner B S hS P hP θ) N

/-- The 1-morphism from the apex of `N` to the canonical apex `P.pt ×_ℬ 𝒰`. -/
noncomputable abbrev innerComparison (P : Bicategory.TwoCommSq p q)
    (hP : Bicategory.IsTwoFibreProduct P) (θ : c ≫ q ≅ G) (N : Bicategory.TwoCommSq p G) :
    N.pt ⟶ (twoFibreProductSquareAlgebraicStacks B S hS P.snd c).pt :=
  (innerPreHomToOuter B S hS P hP θ N).hom

/-- `AlgebraicGeometry.Stack.innerComparison` is an equivalence of the underlying categories:
both `N` and the outer square of Stacks 02XD are 2-fibre products of the cospan `(p, G)`. -/
theorem isEquivalence_innerComparison (P : Bicategory.TwoCommSq p q)
    (hP : Bicategory.IsTwoFibreProduct P) (θ : c ≫ q ≅ G) (N : Bicategory.TwoCommSq p G)
    (hN : Bicategory.IsTwoFibreProduct N) :
    (innerComparison B S hS P hP θ N).hom.hom.toFunctor.IsEquivalence :=
  isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hN
    (isTwoFibreProduct_outerSquareOfInner B S hS P hP θ)
    (innerPreHomToOuter B S hS P hP θ N)

/-- The apex of `N`, as a 2-commutative square over the inner cospan `(P.snd, c)`: its two legs
are the composites of `AlgebraicGeometry.Stack.innerComparison` with the two projections of the
canonical inner 2-fibre product. -/
noncomputable def innerSquareOfOuter (P : Bicategory.TwoCommSq p q)
    (hP : Bicategory.IsTwoFibreProduct P) (θ : c ≫ q ≅ G) (N : Bicategory.TwoCommSq p G) :
    Bicategory.TwoCommSq P.snd c where
  pt := N.pt
  fst := innerComparison B S hS P hP θ N ≫
    (twoFibreProductSquareAlgebraicStacks B S hS P.snd c).fst
  snd := innerComparison B S hS P hP θ N ≫
    (twoFibreProductSquareAlgebraicStacks B S hS P.snd c).snd
  iso := α_ _ _ _ ≪≫
    whiskerLeftIso (innerComparison B S hS P hP θ N)
      (twoFibreProductSquareAlgebraicStacks B S hS P.snd c).iso ≪≫ (α_ _ _ _).symm

/-- The pre-morphism from `AlgebraicGeometry.Stack.innerSquareOfOuter` to the canonical inner
2-fibre product: its 1-morphism is the comparison and both of its comparison 2-cells are
identities. -/
noncomputable def innerPreHomOfOuter (P : Bicategory.TwoCommSq p q)
    (hP : Bicategory.IsTwoFibreProduct P) (θ : c ≫ q ≅ G) (N : Bicategory.TwoCommSq p G) :
    Bicategory.TwoCommSq.PreHom (innerSquareOfOuter B S hS P hP θ N)
      (twoFibreProductSquareAlgebraicStacks B S hS P.snd c) where
  hom := innerComparison B S hS P hP θ N
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    dsimp only [innerSquareOfOuter]
    simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom]
    bicategory

/-- **The inner factor of an iterated 2-fibre product, recognised on the apex of the outer
one.** If `P` is a 2-fibre product of `(p, q)` and `N` is a 2-fibre product of `(p, G)`, where
`G` is identified with `c ≫ q`, then the apex of `N` carries a 2-fibre product of the cospan
`(P.snd, c)`. -/
noncomputable def isTwoFibreProduct_innerSquareOfOuter (P : Bicategory.TwoCommSq p q)
    (hP : Bicategory.IsTwoFibreProduct P) (θ : c ≫ q ≅ G) (N : Bicategory.TwoCommSq p G)
    (hN : Bicategory.IsTwoFibreProduct N) :
    Bicategory.IsTwoFibreProduct (innerSquareOfOuter B S hS P hP θ N) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        P.snd.hom c.hom)
      (innerPreHomOfOuter B S hS P hP θ N).underlying
      (isEquivalence_innerComparison B S hS P hP θ N hN))

/-- The second leg of the recognised square is the second leg of `N`, up to an invertible
2-cell. -/
noncomputable def innerSquareOfOuter_snd_iso (P : Bicategory.TwoCommSq p q)
    (hP : Bicategory.IsTwoFibreProduct P) (θ : c ≫ q ≅ G) (N : Bicategory.TwoCommSq p G) :
    N.snd ≅ (innerSquareOfOuter B S hS P hP θ N).snd :=
  (innerPreHomToOuter B S hS P hP θ N).isoSnd

/-- The first leg of the recognised square followed by the first projection of `P` is the first
leg of `N`, up to an invertible 2-cell. -/
noncomputable def innerSquareOfOuter_fst_comp_iso (P : Bicategory.TwoCommSq p q)
    (hP : Bicategory.IsTwoFibreProduct P) (θ : c ≫ q ≅ G) (N : Bicategory.TwoCommSq p G) :
    N.fst ≅ (innerSquareOfOuter B S hS P hP θ N).fst ≫ P.fst :=
  (innerPreHomToOuter B S hS P hP θ N).isoFst ≪≫ (α_ _ _ _).symm

end AlgebraicGeometry.Stack

end
