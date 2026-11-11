module

public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSlicePullback

/-!
# The fibre product of objects of the site represents the 2-fibre product of the stacks

Let `a : U ⟶ W` and `b : V ⟶ W` be morphisms of the big fppf category of `S` and let
`p : Q ⟶ U`, `q : Q ⟶ V` be a fibre product of that cospan in the site. The objects `U`, `V`,
`W` and `Q` represent algebraic stacks over `S` (`AlgebraicGeometry.Stack.schemeStack`) and the
morphisms represent 1-morphisms between them
(`AlgebraicGeometry.Stack.schemeStackMap`). This module proves that the resulting square of
algebraic stacks is a **2-fibre product** in the sense of Stacks 003Q:

```text
Q ----q---> V          schemeStack Q ----> schemeStack V
|           |                |                  |
p           b      ↦         |                  |
|           |                v                  v
U ----a---> W          schemeStack U ----> schemeStack W
```

This is the identification which turns a closed subset of a fibre product of *schemes* into a
closed subset of a 2-fibre product of the *stacks* they represent, and conversely; it is the
input the stack case of Stacks 0H29 needs in order to consume the scheme case.

## Main definitions

* `AlgebraicGeometry.Stack.overMapSquareIso`: the natural isomorphism filling the square of
  slices, with the identity of the underlying object of the site in every component.
* `AlgebraicGeometry.Stack.schemeFibredCategorySquare`: the 2-commutative square of represented
  categories fibred in groupoids attached to a commuting square of the site.
* `AlgebraicGeometry.Stack.schemeStackSquare`: the same square, read in the 2-category of
  algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_schemeFibredCategorySquare`: the square of
  represented categories fibred in groupoids attached to a fibre product square of the site is a
  2-fibre product.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_schemeStackSquare`: the same, in the 2-category of
  algebraic stacks.
* `AlgebraicGeometry.Stack.isFinalTwoCommSq_schemeFibredCategorySquare` and
  `AlgebraicGeometry.Stack.isFinalTwoCommSq_schemeStackSquare`: the two squares are 2-fibre
  products in the full sense of Stacks 003Q, with the uniqueness of the 2-isomorphism of
  Stacks 003P (2); the two results above are their 1-truncated forms.

## Implementation notes

The category fibred in groupoids represented by an object of the site is the slice of the site
over it (`AlgebraicGeometry.Stack.schemeFibredCategory`), and the 1-morphism represented by a
morphism is postcomposition (`AlgebraicGeometry.Stack.overMapBased`). So the content of the
statement is purely about slices and is
`CategoryTheory.TwoFibreProductOver.instIsEquivalenceSlicePullback`: the slice over `Q` is the
2-fibre product over `𝒞` of the slices over `U` and over `V` above the slice over `W`.

What makes the transfer free is that the comparison functor
`CategoryTheory.TwoFibreProductOver.slicePullback` is *literally* the mediating 1-morphism
`CategoryTheory.CatFiberedInGroupoids.liftTwoFibreProductSquare` into the canonical 2-fibre
product, once the filler of the square is taken to be `overMapSquareIso` — both send an object
`c : T ⟶ Q` of the slice to the quadruple consisting of `T`, the two components of `c` and the
identity of `T`. So the equivalence of
`CategoryTheory.TwoFibreProductOver.instIsEquivalenceSlicePullback` is the hypothesis of
`CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to` with no transport at all, and
the passage to the 2-category of algebraic stacks is
`CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying`, that 2-category being a full
sub-2-category.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Q U V W : BigFppfOver B S hS} {p : Q ⟶ U} {q : Q ⟶ V} {a : U ⟶ W} {b : V ⟶ W}

/-- The natural isomorphism filling the square of slices attached to a commuting square of the
site: an object `c : T ⟶ Q` of the slice over `Q` is sent by the two routes to the two objects
`T ⟶ W` obtained from `c` by composing, and these agree, so the identity of `T` is an
isomorphism between them in the slice over `W`. -/
def overMapSquareIso (hcomm : p ≫ a = q ≫ b) :
    Over.map p ⋙ Over.map a ≅ Over.map q ⋙ Over.map b :=
  NatIso.ofComponents
    (fun c => Over.isoMk (Iso.refl c.left) (by simp [Category.assoc, hcomm]))
    (fun f => by apply Over.OverMorphism.ext; simp)

/-- Every component of `AlgebraicGeometry.Stack.overMapSquareIso` is vertical: it lies over the
identity of the underlying object of the site. -/
theorem overMapSquareIso_hom_app_isHomLift (hcomm : p ≫ a = q ≫ b) (c : Over Q) :
    (Over.forget W).IsHomLift (𝟙 ((Over.forget Q).obj c))
      ((overMapSquareIso B S hS hcomm).hom.app c) :=
  IsHomLift.of_fac' (Over.forget W) (𝟙 c.left) _ rfl rfl (by simp [overMapSquareIso])

/-- The 2-commutative square of represented categories fibred in groupoids attached to a
commuting square of the big fppf category of `S`. -/
def schemeFibredCategorySquare (hcomm : p ≫ a = q ≫ b) :
    Bicategory.TwoCommSq (schemeFibredCategoryMap B S hS a) (schemeFibredCategoryMap B S hS b)
    where
  pt := schemeFibredCategory B S hS Q
  fst := schemeFibredCategoryMap B S hS p
  snd := schemeFibredCategoryMap B S hS q
  iso := Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (overMapSquareIso B S hS hcomm)
      (overMapSquareIso_hom_app_isHomLift B S hS hcomm))

/-- **A fibre product square of the site gives a 2-fibre product square of the represented
categories fibred in groupoids.** -/
noncomputable def isTwoFibreProduct_schemeFibredCategorySquare (h : IsPullback p q a b) :
    Bicategory.IsTwoFibreProduct (schemeFibredCategorySquare B S hS h.w) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeFibredCategoryMap B S hS a) (schemeFibredCategoryMap B S hS b))
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeFibredCategoryMap B S hS a) (schemeFibredCategoryMap B S hS b)
      (schemeFibredCategorySquare B S hS h.w))
    (by
      change (TwoFibreProductOver.slicePullback h).IsEquivalence
      infer_instance)

/-- The 2-commutative square of algebraic stacks attached to a commuting square of the big fppf
category of `S`. -/
def schemeStackSquare (hcomm : p ≫ a = q ≫ b) :
    Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS a) (schemeStackMap.{u, w} B S hS b) where
  pt := schemeStack.{u, w} B S hS Q
  fst := schemeStackMap.{u, w} B S hS p
  snd := schemeStackMap.{u, w} B S hS q
  iso := Bicategory.InducedBicategory.isoMk
    (schemeFibredCategorySquare B S hS hcomm).iso

/-- **A fibre product square of the site gives a 2-fibre product square of the represented
algebraic stacks.** -/
noncomputable def isTwoFibreProduct_schemeStackSquare (h : IsPullback p q a b) :
    Bicategory.IsTwoFibreProduct (schemeStackSquare.{u, w} B S hS h.w) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (isTwoFibreProduct_schemeFibredCategorySquare B S hS h)

/-- **A fibre product square of the site gives a 2-fibre product square of the represented
categories fibred in groupoids, in the sense of Stacks 003Q**: a final object of the 2-category of
2-commutative diagrams, with the uniqueness of the 2-isomorphism of Stacks 003P (2). -/
noncomputable def isFinalTwoCommSq_schemeFibredCategorySquare (h : IsPullback p q a b) :
    Bicategory.IsFinalTwoCommSq (schemeFibredCategorySquare B S hS h.w) :=
  CatFiberedInGroupoids.isFinalTwoCommSq_of_isTwoFibreProduct.{u, u, u + 1, u + 1}
    (isTwoFibreProduct_schemeFibredCategorySquare B S hS h)

/-- **A fibre product square of the site gives a 2-fibre product square of the represented
algebraic stacks, in the sense of Stacks 003Q.** -/
noncomputable def isFinalTwoCommSq_schemeStackSquare (h : IsPullback p q a b) :
    Bicategory.IsFinalTwoCommSq (schemeStackSquare.{u, w} B S hS h.w) :=
  Bicategory.isFinalTwoCommSq_of_underlying
    (isFinalTwoCommSq_schemeFibredCategorySquare B S hS h)

end AlgebraicGeometry.Stack

end
