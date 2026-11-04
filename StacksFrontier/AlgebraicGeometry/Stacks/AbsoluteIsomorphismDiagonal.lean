module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.DiagonalFullSubcategory

/-!
# The sheaf of isomorphisms between two points of an algebraic stack

Let `𝒳` be an algebraic stack over `S`, let `Z` be an algebraic space over `S`, and let
`x₁, x₂ : Z ⟶ 𝒳` be two 1-morphisms out of `Z` viewed as an algebraic stack. The 2-fibre
product `Z ×_{x₁, 𝒳, x₂} Z` has as objects the triples `(z₁, z₂, φ)` with `φ : x₁(z₁) ≅ x₂(z₂)`
vertical; the isomorphisms *between the two points* are the ones with `z₁ = z₂`, that is, the
objects of the full subcategory cut out by the diagonal condition.

This file shows that this full subcategory is a category fibred in groupoids over the big fppf
site, which is what makes `Isom(x₁, x₂)` an object of the 2-category in the first place and so
is the step every representability statement of Stacks 06PP is stated about. The content is the
general fact `CategoryTheory.isFiberedInGroupoids_restrict_diag`; here it is instantiated with
`Z` as the source, `𝒳` as the target, and `x₁`, `x₂` as the two 1-morphisms.

Stacks 06PP goes on to assert that this category is represented by an algebraic space over `Z`,
and that in the automorphism case `x₁ = x₂` the representative carries a group law. Neither is
proved here.

## Main definitions

* `AlgebraicGeometry.Stack.absoluteIsomorphismCategory`, the 2-fibre product
  `Z ×_{x₁, 𝒯, x₂} Z`;
* `AlgebraicGeometry.Stack.absoluteIsomorphismDiagonalSubcategory` and
  `AlgebraicGeometry.Stack.absoluteIsomorphismDiagonalProjection`, the diagonal full
  subcategory and its projection to the site.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInGroupoids_absoluteIsomorphismDiagonal`: the
  isomorphisms over one point of `Z` form a category fibred in groupoids.

## References

* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- The 2-fibre product `Z ×_{x₁, 𝒯, x₂} Z` of two algebraic-space-valued points of `𝒯`. Its
objects are the triples `(z₁, z₂, φ)` with `φ : x₁(z₁) ≅ x₂(z₂)` a vertical isomorphism of
`𝒯`; imposing `z₁ = z₂` cuts out the isomorphisms between the two points. -/
def absoluteIsomorphismCategory (𝒯 : AlgebraicStacks.{u, w} B S hS)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒯) :
    CatFiberedInGroupoids (BigFppfOver B S hS) :=
  twoFibreProduct B S hS 𝒯.val
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    x₁.hom.hom x₂.hom.hom

/-- The diagonal part of the 2-fibre product: its two points of `Z` are equal, so its objects
are the isomorphisms `x₁(z) ≅ x₂(z)` over a single point `z`. -/
abbrev absoluteIsomorphismDiagonalSubcategory
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :=
  ObjectProperty.FullSubcategory
    (fun A : (absoluteIsomorphismCategory B S hS Z hZ 𝒳 x₁ x₂).val.obj => A.x = A.y)

/-- Projection of the diagonal isomorphism category to the big fppf site. -/
abbrev absoluteIsomorphismDiagonalProjection
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    absoluteIsomorphismDiagonalSubcategory B S hS Z hZ x₁ x₂ ⥤ BigFppfOver B S hS :=
  ObjectProperty.ι _ ⋙ (absoluteIsomorphismCategory B S hS Z hZ 𝒳 x₁ x₂).val.p

/-- **Isomorphisms over one point of `Z` form a category fibred in groupoids.** This is the
step of Stacks 06PP that makes `Isom(x₁, x₂)` an object of the 2-category of categories fibred
in groupoids over the big fppf site; it is
`CategoryTheory.isFiberedInGroupoids_restrict_diag` instantiated at the two points, and needs
nothing of `𝒳` beyond its being fibred in groupoids. -/
theorem isFiberedInGroupoids_absoluteIsomorphismDiagonal
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (absoluteIsomorphismDiagonalProjection B S hS Z hZ x₁ x₂).IsFiberedInGroupoids :=
  isFiberedInGroupoids_restrict_diag
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p 𝒳.val.val.p
    x₁.hom.hom.toFunctor x₂.hom.hom.toFunctor
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids x₁.hom.hom.w x₂.hom.hom.w

end AlgebraicGeometry.Stack

end
