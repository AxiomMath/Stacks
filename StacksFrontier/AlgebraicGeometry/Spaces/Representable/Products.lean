module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.CategoryTheory.Limits.BinaryProductDiagonal

/-!
# Products of representable transformations

The product `a₁ × a₂ : F₁ × F₂ ⟶ G₁ × G₂` of two representable transformations of presheaves
on the big fppf site of a scheme is again representable.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_prod_map`: the product of two representable
  transformations of presheaves on the big fppf site over `S` is representable.

## Implementation notes

The whole content is formal and already available: `CategoryTheory.MorphismProperty.prod_map`
says that a property of morphisms stable under base change and under composition holds of the
product of two morphisms it holds of, by factoring the product as
`F₁ ⨯ F₂ ⟶ G₁ ⨯ F₂ ⟶ G₁ ⨯ G₂` and recognising each leg as a base change. Relative
representability along the Yoneda embedding is stable under base change and under composition,
so the statement for the big fppf site is an instance.

## References

* [Stacks Project, Tag 02WC](https://stacks.math.columbia.edu/tag/02WC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks Project, Tag 02WC.** The product of two representable transformations of
presheaves on the big fppf site over `S` is representable. -/
@[stacks 02WC]
public theorem relativelyRepresentable_prod_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F₁ G₁ F₂ G₂ : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂)
    (h₁ : yoneda.relativelyRepresentable a₁) (h₂ : yoneda.relativelyRepresentable a₂) :
    yoneda.relativelyRepresentable (prod.map a₁ a₂) :=
  MorphismProperty.prod_map _ a₁ a₂ h₁ h₂

end AlgebraicGeometry.Space

end
