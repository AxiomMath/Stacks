module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence

/-!
# The diagonal and the second diagonal of a category fibred in groupoids

Fix a base category `𝒞`. The 2-category of categories fibred in groupoids over `𝒞` has
2-fibre products (Stacks 0041), hence products: the product `𝒳₁ × 𝒳₂` is the 2-fibre product
over the final object `𝟭 𝒞` of that 2-category. The *diagonal* of `𝒳` is the 1-morphism
`Δ : 𝒳 ⟶ 𝒳 × 𝒳` sending `x` to `(x, x, id)`, and the *relative diagonal* of a 1-morphism
`f : 𝒳 ⟶ 𝒴` is `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`. The composite of these two constructions, the
*second diagonal*

`Δ_Δ : 𝒳 ⟶ 𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳`,

is the identity section of the inertia of `𝒳` (Categories, Section 4.34); it is the subject of
Stacks 07WG.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.product`: the product of two categories fibred in
  groupoids over `𝒞`, i.e. their 2-fibre product over `𝟭 𝒞`.
* `AlgebraicGeometry.Stack.diagonalBasedFunctor`,
  `AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor`: the diagonal and the relative diagonal
  as 1-morphisms of categories over the big fppf site of `S`, allowing independent universes for
  their source and target.
* `AlgebraicGeometry.Stack.diagonal`, `AlgebraicGeometry.Stack.relativeDiagonal`: the same two
  1-morphisms, bundled as 1-morphisms of the 2-category of categories fibred in groupoids over
  the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff`: condition (1) of Stacks 045G is
  representability by algebraic spaces of `diagonalBasedFunctor`.
* `AlgebraicGeometry.Stack.secondDiagonal_comp_toRelativeInertia`: the second diagonal of `𝒳` is
  the identity section of the inertia of `𝒳`, which is the identification the proof of Stacks
  07WG opens with. The target of the second diagonal is identified with that inertia by
  `CategoryTheory.TwoFibreProductOver.isEquivalenceOver_toRelativeInertia`, an equivalence over
  the site.

## Implementation notes

The underlying functors are the ones of `CategoryTheory.TwoFibreProductOver.diagonal`, which is
the diagonal of a functor strictly over `𝒞`; for the absolute diagonal that functor is the
structure functor `𝒳 ⥤ 𝒞` itself, viewed as a 1-morphism into `𝟭 𝒞`. The target of the relative
diagonal is `AlgebraicGeometry.Stack.twoFibreProduct`, the 2-fibre product with independent
universes for all three total categories.

The product is stated over an arbitrary base category rather than over the big fppf site,
because nothing in its construction uses the site; it is the construction that Stacks 0303 forms
products of 1-morphisms along.

The based-functor forms and the bundled forms of the two diagonals are definitionally the same
1-morphism: the bundled form is the based functor under
`CategoryTheory.Bicategory.InducedBicategory.mkHom`, which is how a 1-morphism of a full
sub-2-category is presented. Both are provided because a consumer stating a representability
property of the diagonal needs the based functor (whose source and target may have independent
universes), while a consumer composing the diagonal with other 1-morphisms needs the bundled
form.

## References

* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.CatFiberedInGroupoids

universe u v w

variable {𝒞 : Type (u + 1)} [Category.{u} 𝒞]

/-- The product of two categories fibred in groupoids over `𝒞`: their 2-fibre product over the
final object `𝟭 𝒞` of the 2-category of categories fibred in groupoids over `𝒞`. Its objects are
the triples `(x₁, x₂, φ)` with `x₁`, `x₂` lying over a common object of `𝒞` and `φ` the induced
identification of their images, and its morphisms are the pairs of morphisms lying over one
common morphism of `𝒞`. -/
def product (𝒳₁ 𝒳₂ : CatFiberedInGroupoids.{u, v, u + 1, w} 𝒞) :
    CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) w} 𝒞 :=
  mk
    (BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor 𝒳₁.val.p 𝒳₂.val.p (𝟭 𝒞) 𝒳₁.val.p 𝒳₂.val.p))
    (TwoFibreProductOver.isFiberedInGroupoids 𝒳₁.val.p 𝒳₂.val.p (𝟭 𝒞) 𝒳₁.val.p 𝒳₂.val.p
      𝒳₁.isFiberedInGroupoids 𝒳₂.isFiberedInGroupoids Functor.isFiberedInGroupoids_id
      (Functor.comp_id _) (Functor.comp_id _))

end CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` of a category fibred in groupoids over the big fppf site of
`S`, as a 1-morphism of categories over that site: it sends an object `x` to `(x, x)` together
with the identity identification of the two images, and a morphism `f` to the pair `(f, f)`. -/
def diagonalBasedFunctor (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    𝒳.val ⥤ᵇ (CatFiberedInGroupoids.product 𝒳 𝒳).val where
  toFunctor := TwoFibreProductOver.diagonal (Functor.comp_id 𝒳.val.p)
  w := by rfl

/-- The relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` of a 1-morphism `f` of categories over
the big fppf site of `S`, as a 1-morphism of categories over that site. -/
def relativeDiagonalBasedFunctor
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (𝒴 : CatFiberedInGroupoids.{u, v', u + 1, w'} (BigFppfOver B S hS))
    (f : 𝒳.val ⥤ᵇ 𝒴.val) :
    𝒳.val ⥤ᵇ (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f f).val where
  toFunctor := TwoFibreProductOver.diagonal f.w
  w := by rfl

/-- The diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳`, as a 1-morphism of the 2-category of categories fibred in
groupoids over the big fppf site of `S`. -/
def diagonal
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS)) :
    𝒳 ⟶ CatFiberedInGroupoids.product 𝒳 𝒳 :=
  Bicategory.InducedBicategory.mkHom (diagonalBasedFunctor B S hS 𝒳)

/-- The relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` of a 1-morphism `f`, as a 1-morphism of
the 2-category of categories fibred in groupoids over the big fppf site of `S`. -/
def relativeDiagonal
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) : 𝒳 ⟶ twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom :=
  Bicategory.InducedBicategory.mkHom (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom)

/-- Condition (1) of Stacks 045G is representability by algebraic spaces of the diagonal 1-morphism
`AlgebraicGeometry.Stack.diagonalBasedFunctor`: the product category that
`AlgebraicGeometry.Stack.HasRepresentableDiagonal` is stated with is the one underlying
`CategoryTheory.CatFiberedInGroupoids.product`. -/
lemma hasRepresentableDiagonal_iff
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    HasRepresentableDiagonal B S hS 𝒳 ↔
      IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳) :=
  Iff.rfl

/-- **The second diagonal of `𝒳` is the identity section of its inertia.** Composing the second
diagonal `Δ_Δ : 𝒳 ⟶ 𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` with the comparison functor to the inertia of `𝒳`
(an equivalence over the site, by
`CategoryTheory.TwoFibreProductOver.isEquivalenceOver_toRelativeInertia`) gives the neutral
section `x ↦ (x, 𝟙 x)`. This is the first step of the proof of Stacks 07WG. -/
lemma secondDiagonal_comp_toRelativeInertia
    (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) :
    (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
          (diagonalBasedFunctor B S hS 𝒳)).toFunctor ⋙
        TwoFibreProductOver.toRelativeInertia (Functor.comp_id 𝒳.val.p) =
      RelativeInertia.neutralSection 𝒳.val.p :=
  TwoFibreProductOver.diagonal_comp_toRelativeInertia (Functor.comp_id 𝒳.val.p)

end AlgebraicGeometry.Stack

end
