module

public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceRenderingComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeAutomorphismTotalPresheaf

/-!
# The sheaves of isomorphisms of Stacks 06PP are algebraic spaces over `Z`

`StacksFrontier/AlgebraicGeometry/Stacks/IsomSpaceRenderingComparison.lean` identifies the two
2-fibre products Stacks 06PP writes `Isom_𝒳(x₁, x₂)` and `Isom^α_{𝒳/𝒴}(x₁, x₂)`, as categories
over `Z`, with the categories of elements of two presheaves on the *category of elements of `Z`*:
the presheaf of vertical morphisms `x₁(a) ⟶ x₂(a)` and its relative form, the vertical morphisms
whose image under `f` is the component `α_a`.
`StacksFrontier/AlgebraicGeometry/Stacks/AutomorphismSpaceOverAlgebraicSpace.lean` proves that each
2-fibre product is represented by an algebraic space, but only existentially.

This file puts the two together through the total-presheaf construction
`CategoryTheory.PresheafOfCategories.elementsTotalPresheaf`: the presheaf on the big fppf site of
`S` whose sections over `W` are the pairs of a point `z` of `Z` over `W` and an isomorphism over
`z` — the sheaf of isomorphisms as the source reads it — *is* an algebraic space, and it comes
with its structure morphism to `Z`.

## Main definitions

* `AlgebraicGeometry.Stack.isomorphismTotalPresheaf` and
  `AlgebraicGeometry.Stack.relativeIsomorphismTotalPresheaf`: the two sheaves of isomorphisms on
  the big fppf site, with `AlgebraicGeometry.Stack.isomorphismSpaceOver` and
  `AlgebraicGeometry.Stack.relativeIsomorphismSpaceOver` reading each as an object of
  `CategoryTheory.Over Z`.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicSpace_isomorphismTotalPresheaf` and
  `AlgebraicGeometry.Stack.isAlgebraicSpace_relativeIsomorphismTotalPresheaf`: each is an
  algebraic space over `S`, hence an algebraic space over `Z`.

## Implementation notes

Both proofs are `AlgebraicGeometry.Stack.isAlgebraicSpace_elementsTotalPresheaf` fed with the
equivalence over `Z` of `IsomSpaceRenderingComparison.lean`, read over the site through
`StacksRepresentableCFG.EquivalenceOver.compRight` and the `w` equation of the projection to the
stack of `Z`, and with the existential representability of the 2-fibre product. The category
instance of a 2-fibre product is found through `CategoryTheory.BasedCategory.ofFunctor`, which is
made reducible for instance search here as in
`StacksFrontier/AlgebraicGeometry/Stacks/IsomSpaceRenderingComparison.lean`.

These are the presheaves on the site that `Isom_𝒳(x₁, x₂)` and `Isom^α_{𝒳/𝒴}(x₁, x₂)` are; that
they agree with the hand-built presheaves `AlgebraicGeometry.Stack.isomSpaceOverSpace` and
`AlgebraicGeometry.Stack.relativeIsomSpaceOverSpace` of
`StacksFrontier/AlgebraicGeometry/Stacks/IsomSpaceOverAlgebraicSpace.lean`, whose sections are the
isomorphisms of the *fibre categories* rather than the vertical morphisms of the total category,
is a comparison of two descriptions of one set and is not proved here.

## References

* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04XT](https://stacks.math.columbia.edu/tag/04XT)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 06PP: the sheaf `Isom_𝒳(x₁, x₂)` on the big fppf site of `S`.** The total presheaf
of the presheaf of vertical morphisms from `x₁` to `x₂`: its sections over an object `W` of the
site are the pairs consisting of a point `z` of `Z` over `W` and a vertical morphism
`x₁(z) ⟶ x₂(z)` of `𝒳`, every one of which is an isomorphism because the fibres of an algebraic
stack are groupoids. -/
noncomputable abbrev isomorphismTotalPresheaf
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  PresheafOfCategories.elementsTotalPresheaf Z
    (TwoFibreProductOver.DiagonalFibre.vertHomPresheaf 𝒳.val.isFiberedInGroupoids
      (isomorphismPairPoint B S hS Z hZ x₁ x₂).hom.w)

/-- **Stacks 06PP: `Isom_𝒳(x₁, x₂)` as an object over `Z`.** -/
noncomputable abbrev isomorphismSpaceOver
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) : Over Z :=
  Over.mk (PresheafOfCategories.elementsTotalProj Z
    (TwoFibreProductOver.DiagonalFibre.vertHomPresheaf 𝒳.val.isFiberedInGroupoids
      (isomorphismPairPoint B S hS Z hZ x₁ x₂).hom.w))

/-- **Stacks 06PP: the sheaf `Isom_𝒳(x₁, x₂)` on the big fppf site is an algebraic space over
`Z`.** The presheaf whose sections over `W` are the pairs of a point `z` of `Z` over `W` and an
isomorphism `x₁(z) ≅ x₂(z)` is an algebraic space over `S`, so together with its structure
morphism to `Z` it is the algebraic space over `Z` that the last paragraph of Stacks 06PP
asserts. -/
@[stacks 06PP
  "Isom_X(x₁, x₂) as a presheaf over Z on the big fppf site is an algebraic space"]
theorem isAlgebraicSpace_isomorphismTotalPresheaf
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsAlgebraicSpace B S hS (isomorphismTotalPresheaf B S hS Z hZ x₁ x₂) :=
  isAlgebraicSpace_elementsTotalPresheaf B S hS Z _
    (((nonempty_equivalenceOver_isomorphismSpaceOverSpaceProj B S hS Z hZ x₁
        x₂).some.compRight (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p).ofEq
      (isomorphismSpaceOverSpaceProj B S hS Z hZ x₁ x₂).w).symm
    (isRepresentableByAlgebraicSpace_isomorphismSpaceOverSpace B S hS Z hZ x₁ x₂)

/-- **Stacks 06PP, part (2): the sheaf `Isom^α_{𝒳/𝒴}(x₁, x₂)` on the big fppf site of `S`.** The
total presheaf of the presheaf of vertical morphisms from `x₁` to `x₂` lifting `α`: its sections
over `W` are the pairs of a point `z` of `Z` over `W` and a vertical morphism
`x₁(z) ⟶ x₂(z)` whose image under `f` is the component `α_z`. -/
noncomputable abbrev relativeIsomorphismTotalPresheaf (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  PresheafOfCategories.elementsTotalPresheaf Z
    (TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
      𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w)

/-- **Stacks 06PP, part (2): `Isom^α_{𝒳/𝒴}(x₁, x₂)` as an object over `Z`.** -/
noncomputable abbrev relativeIsomorphismSpaceOver (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) : Over Z :=
  Over.mk (PresheafOfCategories.elementsTotalProj Z
    (TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
      𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w))

/-- **Stacks 06PP, part (2): the sheaf `Isom^α_{𝒳/𝒴}(x₁, x₂)` on the big fppf site is an
algebraic space over `Z`.** The presheaf whose sections over `W` are the pairs of a point `z` of
`Z` over `W` and an isomorphism `x₁(z) ≅ x₂(z)` lifting the component `α_z` is an algebraic space
over `S`, so together with its structure morphism to `Z` it is the algebraic space over `Z` that
part (2) asserts. -/
@[stacks 06PP
  "part (2): Isom^α_{X/Y}(x₁, x₂) as a presheaf over Z on the big fppf site is an algebraic space"]
theorem isAlgebraicSpace_relativeIsomorphismTotalPresheaf (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    IsAlgebraicSpace B S hS (relativeIsomorphismTotalPresheaf B S hS Z hZ f x₁ x₂ α) :=
  isAlgebraicSpace_elementsTotalPresheaf B S hS Z _
    (((nonempty_equivalenceOver_relativeIsomorphismSpaceOverSpaceProj B S hS Z hZ f x₁ x₂
        α).some.compRight (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p).ofEq
      (relativeIsomorphismSpaceOverSpaceProj B S hS Z hZ f x₁ x₂ α).w).symm
    (isRepresentableByAlgebraicSpace_relativeIsomorphismSpaceOverSpace B S hS Z hZ f x₁ x₂ α)

/-- The presheaf underlying the object `AlgebraicGeometry.Stack.isomorphismSpaceOver` of
`CategoryTheory.Over Z` is an algebraic space, so that object *is* an algebraic space over `Z`. -/
theorem isAlgebraicSpace_isomorphismSpaceOver_left
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    IsAlgebraicSpace B S hS (isomorphismSpaceOver B S hS Z hZ x₁ x₂).left :=
  isAlgebraicSpace_isomorphismTotalPresheaf B S hS Z hZ x₁ x₂

/-- The presheaf underlying the object
`AlgebraicGeometry.Stack.relativeIsomorphismSpaceOver` of `CategoryTheory.Over Z` is an algebraic
space, so that object *is* an algebraic space over `Z`. -/
theorem isAlgebraicSpace_relativeIsomorphismSpaceOver_left (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    IsAlgebraicSpace B S hS (relativeIsomorphismSpaceOver B S hS Z hZ f x₁ x₂ α).left :=
  isAlgebraicSpace_relativeIsomorphismTotalPresheaf B S hS Z hZ f x₁ x₂ α

end AlgebraicGeometry.Stack

end
