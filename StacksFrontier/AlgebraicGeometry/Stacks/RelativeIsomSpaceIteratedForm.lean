module

public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteNotionsAgree
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeIsomorphismDiagram

/-!
# The relative sheaf of isomorphisms in the iterated form of Stacks 06PP, part (2)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `Z` be an algebraic space over
`S`, let `x₁, x₂ : Z ⟶ 𝒳` be two algebraic-space-valued points of `𝒳`, write `y_i = x_i ≫ f`,
and let `α : y₁ ⟶ y₂` be a 2-morphism of the target. **Stacks 06PP** part (2) defines

```text
Isom^α_{𝒳/𝒴}(x₁, x₂) = (Z ×_{x₁, 𝒳, x₂} Z) ×_{Z ×_{y₁, 𝒴, y₂} Z, Δ^α} Z
```

— the 2-fibre product of the map `H` on isomorphism categories induced by `f` along the twisted
diagonal `Δ^α` determined by `α` — and this file builds that object in exactly that iterated
shape, with its structure 1-morphism to `Z`, and proves both that it is represented by an
algebraic space over `S` and that the structure 1-morphism is representable by algebraic spaces.
`H` and `Δ^α` are the ones constructed in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeIsomorphismDiagram.lean`.

Three steps, each an application of a tag the library already has.

* `Z ×_{x₁, 𝒳, x₂} Z` and `Z ×_{y₁, 𝒴, y₂} Z` —
  `AlgebraicGeometry.Stack.absoluteIsomorphismCategory` for `𝒳` and for `𝒴` — are represented by
  algebraic spaces: a 1-morphism out of the stack of an
  algebraic space into an algebraic stack is representable by algebraic spaces (**Stacks 045G**,
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source`), and
  `Z` represents its own stack, so **Stacks 0300** applies to the cospan `(x₁, x₂)` and to the
  cospan `(y₁, y₂)`.
* Hence `H` and `Δ^α` are 1-morphisms between categories each represented by an algebraic space,
  so both are representable by algebraic spaces by **Stacks 02ZZ**.
* **Stacks 0300** then makes the 2-fibre product of `H` along `Δ^α` an algebraic space, and its
  structure 1-morphism to `Z` — the first projection to `Z ×_{x₁, 𝒳, x₂} Z` followed by that
  object's own first projection to `Z` — is representable by algebraic spaces, again by
  Stacks 02ZZ, both its source and `Z` being algebraic spaces.

This is the *source's own* presentation of part (2). The library's other presentation, the fibre
of the relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` along the twisted point `(x₁, x₂, α)`, is
`AlgebraicGeometry.Stack.relativeIsomorphismSpaceOverSpace`; the two are equivalent, and the
comparison between them is still not proved — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/AutomorphismSpaceOverAlgebraicSpace.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.relativeIsomorphismIteratedSpace`: the iterated 2-fibre product
  displayed above.
* `AlgebraicGeometry.Stack.relativeIsomorphismIteratedSpaceProj`: its structure 1-morphism to the
  stack of `Z`.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_absoluteIsomorphismCategory`: the
  2-fibre product `Z ×_{x₁, 𝒯, x₂} Z` of two algebraic-space-valued points of an algebraic stack
  is represented by an algebraic space.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_absoluteIsomorphismImageBasedFunctor`
  and
  `AlgebraicGeometry.Stack`'s
  `isRepresentableByAlgebraicSpaces_relativeIsomorphismTwistedDiagonalBasedFunctor`:
  `H` and `Δ^α` are representable by algebraic spaces.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_relativeIsomorphismIteratedSpace` and
  `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeIsomorphismIteratedSpaceProj`:
  **Stacks 06PP** part (2) in the source's shape — the iterated 2-fibre product is an algebraic
  space over `Z`.

## Implementation notes

Stacks 02ZZ is stated for a 1-morphism of the 2-category of categories fibred in groupoids,
whose 1-morphisms wrap a 1-morphism of categories over the site; the wrapping is
`CategoryTheory.Bicategory.InducedBicategory.mkHom`, and the conclusion is about the wrapped
1-morphism's underlying functor, which is the one wrapped. The universes of all the categories
occurring here are those of `AlgebraicGeometry.Stack.AlgebraicStacks`, since a 2-fibre product of
categories with objects in `Type (u + 1)` and morphisms in `Type u` has objects and morphisms in
the same two universes; that is what lets Stacks 02ZZ, which asks for the same universes on both
sides, apply to `H`, to `Δ^α` and to the structure 1-morphism.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **The 2-fibre product `Z ×_{x₁, 𝒯, x₂} Z` of two algebraic-space-valued points of an
algebraic stack is represented by an algebraic space.** The second leg `x₂` is representable by
algebraic spaces because its source is the stack of an algebraic space and its target is an
algebraic stack (Stacks 045G), and `Z` represents the first factor, so this is Stacks 0300. -/
theorem isRepresentableByAlgebraicSpace_absoluteIsomorphismCategory
    (𝒯 : AlgebraicStacks.{u, w} B S hS)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒯) :
    IsRepresentableByAlgebraicSpace B S hS
      (absoluteIsomorphismCategory B S hS Z hZ 𝒯 x₁ x₂) :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒯.val
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val x₁.hom.hom x₂.hom.hom
    (isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS 𝒯 Z hZ x₂)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)

/-- Stacks 02ZZ for a based functor between categories represented by algebraic spaces. -/
private theorem isRepresentableByAlgebraicSpaces_of_basedFunctor
    {𝒜 ℬ : CatFiberedInGroupoids.{u, u, u + 1, w} (BigFppfOver B S hS)} (F : 𝒜.val ⥤ᵇ ℬ.val)
    (h𝒜 : IsRepresentableByAlgebraicSpace B S hS 𝒜)
    (hℬ : IsRepresentableByAlgebraicSpace B S hS ℬ) :
    IsRepresentableByAlgebraicSpaces B S hS F :=
  isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
    (Bicategory.InducedBicategory.mkHom F) h𝒜 hℬ

/-- **The map `H` on absolute isomorphism categories induced by `f` is representable by algebraic
spaces.** Both its source and its target are represented by algebraic spaces, so this is
Stacks 02ZZ. -/
theorem isRepresentableByAlgebraicSpaces_absoluteIsomorphismImageBasedFunctor (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS
      (absoluteIsomorphismImageBasedFunctor B S hS Z hZ f x₁ x₂) :=
  isRepresentableByAlgebraicSpaces_of_basedFunctor B S hS
    (absoluteIsomorphismImageBasedFunctor B S hS Z hZ f x₁ x₂)
    (isRepresentableByAlgebraicSpace_absoluteIsomorphismCategory B S hS Z hZ 𝒳 x₁ x₂)
    (isRepresentableByAlgebraicSpace_absoluteIsomorphismCategory B S hS Z hZ 𝒴 (x₁ ≫ f)
      (x₂ ≫ f))

/-- **The twisted diagonal `Δ^α` is representable by algebraic spaces**, for the same reason:
its source is the stack of `Z` and its target is `Z ×_{y₁, 𝒴, y₂} Z`, and both are represented
by algebraic spaces, so this is Stacks 02ZZ. -/
theorem isRepresentableByAlgebraicSpaces_relativeIsomorphismTwistedDiagonalBasedFunctor
    (f : 𝒳 ⟶ 𝒴) (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeIsomorphismTwistedDiagonalBasedFunctor B S hS Z hZ f x₁ x₂ α) :=
  isRepresentableByAlgebraicSpaces_of_basedFunctor B S hS
    (relativeIsomorphismTwistedDiagonalBasedFunctor B S hS Z hZ f x₁ x₂ α)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)
    (isRepresentableByAlgebraicSpace_absoluteIsomorphismCategory B S hS Z hZ 𝒴 (x₁ ≫ f)
      (x₂ ≫ f))

/-- **Stacks 06PP, part (2): the relative sheaf of isomorphisms from `x₁` to `x₂` lifting `α`,
in the iterated form the source writes it in.** The 2-fibre product

```text
Isom^α_{𝒳/𝒴}(x₁, x₂) = (Z ×_{x₁, 𝒳, x₂} Z) ×_{Z ×_{y₁, 𝒴, y₂} Z, Δ^α} Z
```

of the map `H` on absolute isomorphism categories induced by `f` along the twisted diagonal
`Δ^α` determined by `α`. Its objects over a scheme `W` are the isomorphisms `x₁(z) ≅ x₂(z)` of
the fibre of `𝒳` over `W` whose image under `f` is the component of `α` at `z`. -/
@[stacks 06PP "part (2): Isom^α_{X/Y}(x₁, x₂) as the iterated fibre product of the source"]
noncomputable def relativeIsomorphismIteratedSpace (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    CatFiberedInGroupoids (BigFppfOver B S hS) :=
  twoFibreProduct B S hS
    (absoluteIsomorphismCategory B S hS Z hZ 𝒴 (x₁ ≫ f) (x₂ ≫ f))
    (absoluteIsomorphismCategory B S hS Z hZ 𝒳 x₁ x₂)
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    (absoluteIsomorphismImageBasedFunctor B S hS Z hZ f x₁ x₂)
    (relativeIsomorphismTwistedDiagonalBasedFunctor B S hS Z hZ f x₁ x₂ α)

/-- The structure 1-morphism `Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z` of the iterated form: the first
projection to `Z ×_{x₁, 𝒳, x₂} Z`, followed by that object's own first projection to the stack
of `Z`. -/
noncomputable def relativeIsomorphismIteratedSpaceProj (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    (relativeIsomorphismIteratedSpace B S hS Z hZ f x₁ x₂ α).val ⥤ᵇ
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val :=
  BasedFunctor.comp
    (twoFibreProductFst B S hS
      (absoluteIsomorphismCategory B S hS Z hZ 𝒴 (x₁ ≫ f) (x₂ ≫ f))
      (absoluteIsomorphismCategory B S hS Z hZ 𝒳 x₁ x₂)
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val
      (absoluteIsomorphismImageBasedFunctor B S hS Z hZ f x₁ x₂)
      (relativeIsomorphismTwistedDiagonalBasedFunctor B S hS Z hZ f x₁ x₂ α))
    (twoFibreProductFst B S hS 𝒳.val
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val x₁.hom.hom x₂.hom.hom)

/-- **Stacks 06PP, part (2): the iterated form of `Isom^α_{𝒳/𝒴}(x₁, x₂)` is an algebraic
space.** It is the base change of the twisted diagonal `Δ^α` along `H`; `Δ^α` is representable by
algebraic spaces and `Z ×_{x₁, 𝒳, x₂} Z` is represented by an algebraic space, so this is
Stacks 0300. -/
@[stacks 06PP "part (2): the iterated form of Isom^α_{X/Y}(x₁, x₂) is an algebraic space"]
theorem isRepresentableByAlgebraicSpace_relativeIsomorphismIteratedSpace (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    IsRepresentableByAlgebraicSpace B S hS
      (relativeIsomorphismIteratedSpace B S hS Z hZ f x₁ x₂ α) :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    (absoluteIsomorphismCategory B S hS Z hZ 𝒴 (x₁ ≫ f) (x₂ ≫ f))
    (absoluteIsomorphismCategory B S hS Z hZ 𝒳 x₁ x₂)
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    (absoluteIsomorphismImageBasedFunctor B S hS Z hZ f x₁ x₂)
    (relativeIsomorphismTwistedDiagonalBasedFunctor B S hS Z hZ f x₁ x₂ α)
    (isRepresentableByAlgebraicSpaces_relativeIsomorphismTwistedDiagonalBasedFunctor
      B S hS Z hZ f x₁ x₂ α)
    (isRepresentableByAlgebraicSpace_absoluteIsomorphismCategory B S hS Z hZ 𝒳 x₁ x₂)

/-- **Stacks 06PP, part (2): the iterated form of `Isom^α_{𝒳/𝒴}(x₁, x₂)` is an algebraic space
over `Z`.** Its structure 1-morphism to the stack of `Z` has an algebraic space as source and the
stack of `Z` as target, so it is representable by algebraic spaces by Stacks 02ZZ; together with
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_relativeIsomorphismIteratedSpace` it is
therefore a morphism of algebraic spaces with target `Z`. -/
@[stacks 06PP "part (2): the iterated form of Isom^α_{X/Y}(x₁, x₂) is an algebraic space over Z"]
theorem isRepresentableByAlgebraicSpaces_relativeIsomorphismIteratedSpaceProj (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeIsomorphismIteratedSpaceProj B S hS Z hZ f x₁ x₂ α) :=
  isRepresentableByAlgebraicSpaces_of_basedFunctor B S hS
    (relativeIsomorphismIteratedSpaceProj B S hS Z hZ f x₁ x₂ α)
    (isRepresentableByAlgebraicSpace_relativeIsomorphismIteratedSpace B S hS Z hZ f x₁ x₂ α)
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)

end AlgebraicGeometry.Stack

end
