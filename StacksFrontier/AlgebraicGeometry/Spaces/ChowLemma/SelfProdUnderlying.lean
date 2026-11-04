module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplement

/-!
# The algebraic space underlying a finite self-product of the spaces-étale site

The `n`-fold self-product `U^n` of an object `U` of the spaces-étale site of an algebraic space
`X` is `∏ᶜ (fun _ : Fin n => U)`, a product taken *in the site*. Nothing can be said about the
algebraic space it carries until that product is identified with an iterated fibre product of
the underlying algebraic spaces over `X`, which is what this file does.

Two inputs are needed. The first is that the inclusion of the site into the slice `Over X`
preserves finite products: by Stacks 0DF3 it preserves the final object and fibre products, and
the site has both, so it preserves all finite limits. The second is the shape of a finite
product in a slice category: a binary product in `Over X` is a fibre product over `X`
(`Stacks.OverProducts.prodLeftIso`, from Mathlib's
`CategoryTheory.Limits.IsLimit.pullbackConeEquivBinaryFanFunctor`), and a `Fin (n + 1)`-indexed
product peels off one factor as a binary product
(`Stacks.OverProducts.prodFinSuccIso`, from Mathlib's
`CategoryTheory.Limits.extendFanIsLimit`).

## Main definitions

* `Stacks.OverProducts.prodLeftIso`: the object underlying a binary product in a slice category
  is the fibre product.
* `Stacks.OverProducts.prodFinSuccIso`: a `Fin (n + 1)`-fold self-product in any category with
  the relevant products is the binary product of the object with the `Fin n`-fold
  self-product.
* `AlgebraicGeometry.Space.SpacesEtale.inclusionSelfProdSuccIso` and
  `AlgebraicGeometry.Space.SpacesEtale.underlyingSelfProdSuccIso`: the two forms of the
  identification, in `Over X` and in the category of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.inclusion_preservesFiniteProducts`: the inclusion of the
  spaces-étale site of `X` into `Over X` preserves `Fin n`-indexed products.
* `AlgebraicGeometry.Space.pullbackFiberProductIso`: the presheaf underlying a fibre product of
  algebraic spaces over `S` is the presheaf fibre product. This is Stacks 02X2 read as an
  isomorphism of presheaves rather than as a universal property.

## What is and is not proved

Nothing here carries a Stacks attribute. Tag 0DF3 already sits on the three instances
`AlgebraicGeometry.Space.SpacesEtale.hasPullbacks`,
`AlgebraicGeometry.Space.SpacesEtale.hasTerminal`,
`AlgebraicGeometry.Space.SpacesEtale.inclusion_preservesTerminalShape` and
`AlgebraicGeometry.Space.SpacesEtale.inclusion_preservesPullbacks`, and Tag 02X2 on
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`; what is added here is the passage
from those to finite products and to an isomorphism of underlying objects.

The identification is stated in the "peel off one factor" form, which is the form an induction
on `n` consumes; the closed form for a general `n` as a wide fibre product is not stated,
because nothing needs it.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 0DF3](https://stacks.math.columbia.edu/tag/0DF3)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.OverProducts

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {X : C}

attribute [local instance] Over.ConstructProducts.over_binaryProduct_of_pullback
  Over.over_hasTerminal hasFiniteProducts_of_has_binary_and_terminal

/-- **The object underlying a binary product in a slice category is the fibre product.** -/
def prodLeftIso (A A' : Over X) : (A ⨯ A' : Over X).left ≅ pullback A.hom A'.hom :=
  (Over.forget X).mapIso
    ((prodIsProd A A').conePointUniqueUpToIso
      (IsLimit.pullbackConeEquivBinaryFanFunctor (pullbackIsPullback A.hom A'.hom)))

/-- **A finite self-product in a slice category peels off one factor.** -/
def prodFinSuccIso (A : Over X) (n : ℕ) :
    (∏ᶜ fun _ : Fin (n + 1) => A) ≅ A ⨯ (∏ᶜ fun _ : Fin n => A) :=
  (productIsProduct fun _ : Fin (n + 1) => A).conePointUniqueUpToIso
    (extendFanIsLimit (fun _ : Fin (n + 1) => A) (productIsProduct fun _ : Fin n => A)
      (prodIsProd A (∏ᶜ fun _ : Fin n => A)))

end Stacks.OverProducts

namespace AlgebraicGeometry.Space

open Stacks.OverProducts

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The presheaf underlying a fibre product of algebraic spaces over `S` is the presheaf
fibre product.** Both squares are cartesian over the same cospan, so Stacks 02X2 in the form
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct` identifies them. -/
def pullbackFiberProductIso {F G H : AlgebraicSpaces B S hS} (f : F ⟶ H) (g : G ⟶ H) :
    (pullback f g).1 ≅ pullback f.hom g.hom :=
  (ObjectProperty.ι (algebraicSpaceProperty B S hS)).mapIso
    ((IsPullback.of_hasPullback f g).isoIsPullback _ _
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.SpacesEtale

open Stacks.OverProducts

attribute [local instance] CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  CategoryTheory.Over.over_hasTerminal hasFiniteProducts_of_has_binary_and_terminal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **The inclusion of the spaces-étale site of `X` into the slice over `X` preserves finite
products.** It preserves the final object and fibre products by Stacks 0DF3, and the site has
a final object and fibre products, so it preserves all finite limits. -/
instance inclusion_preservesFiniteProducts (n : ℕ) :
    PreservesLimitsOfShape (Discrete (Fin n)) (inclusion B S hS X) :=
  have _ : HasFiniteLimits (SpacesEtale B S hS X) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have _ : PreservesFiniteLimits (inclusion B S hS X) :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  inferInstance

/-- **One factor peeled off a finite self-product of the spaces-étale site, in the slice over
`X`.** The inclusion into the slice preserves finite products, so the `(n + 1)`-fold
self-product of `U` in the site becomes the binary product in `Over X` of `U` with the
`n`-fold self-product. -/
def inclusionSelfProdSuccIso (U : SpacesEtale B S hS X) (n : ℕ) :
    (inclusion B S hS X).obj (selfProd B S hS X U (n + 1)) ≅
      ((inclusion B S hS X).obj U ⨯ (inclusion B S hS X).obj (selfProd B S hS X U n)) :=
  PreservesProduct.iso (inclusion B S hS X) (fun _ : Fin (n + 1) => U) ≪≫
    prodFinSuccIso ((inclusion B S hS X).obj U) n ≪≫
    prod.mapIso (Iso.refl _)
      (PreservesProduct.iso (inclusion B S hS X) (fun _ : Fin n => U)).symm

/-- **The algebraic space underlying a finite self-product of the spaces-étale site of `X` is
an iterated fibre product over `X`.** The `(n + 1)`-fold self-product of `U` in the
spaces-étale site of `X` has underlying algebraic space the fibre product over `X` of the
algebraic space underlying `U` with the algebraic space underlying the `n`-fold
self-product.

Iterating this identifies `AlgebraicGeometry.Space.SpacesEtale.selfProd` with the `n`-fold
fibre power of `U` over `X`, which is what lets properties of the underlying space of
`U ×_X ⋯ ×_X U` be checked one fibre product at a time. -/
def underlyingSelfProdSuccIso (U : SpacesEtale B S hS X) (n : ℕ) :
    underlying B S hS X (selfProd B S hS X U (n + 1)) ≅
      pullback ((inclusion B S hS X).obj U).hom
        ((inclusion B S hS X).obj (selfProd B S hS X U n)).hom :=
  (Over.forget X).mapIso (inclusionSelfProdSuccIso B S hS X U n) ≪≫
    prodLeftIso ((inclusion B S hS X).obj U)
      ((inclusion B S hS X).obj (selfProd B S hS X U n))

end AlgebraicGeometry.Space.SpacesEtale

end
