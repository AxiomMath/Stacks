module

public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableProperty
public import StacksFrontier.CategoryTheory.Limits.BinaryProductDiagonal

/-!
# Products of representable morphisms of presheaves with a property

Let `a₁ : F₁ ⟶ G₁` and `a₂ : F₂ ⟶ G₂` be representable morphisms of presheaves on the big
fppf site of a scheme `S`, and let `P` be a property of morphisms of schemes, carried by a
representable morphism of presheaves in the sense of Stacks 025V. If `P` is stable under
composition and both `a₁` and `a₂` have `P`, then so does the product morphism
`a₁ × a₂ : F₁ × F₂ ⟶ G₁ × G₂`.

## Main results

* `AlgebraicGeometry.Space.hasSchemeProperty_prod_map`: **Stacks 02WM**.

## Implementation notes

The underlying categorical fact — that a morphism property stable under base change and under
composition is stable under binary products of morphisms — is already available as
`CategoryTheory.MorphismProperty.prod_map`, so all that is done here is to supply its two
hypotheses for the derived property `CategoryTheory.MorphismProperty.presheaf`.

Stacks 025V applies the definition only to properties which are also stable under base change
and fppf local on the base, and neither is needed here: the derived property
`CategoryTheory.MorphismProperty.presheaf` is stable under base change for *every* `P`, by
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`, since pasting a Cartesian
square onto a represented pullback square of `a` gives a represented pullback square of `a`.
So the only hypothesis on `P` is stability under composition, which is the hypothesis the
source states.

## References

* [Stacks Project, Tag 02WM](https://stacks.math.columbia.edu/tag/02WM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 02WM.** Let `P` be a property of morphisms of schemes which is stable under
composition. If two representable morphisms of presheaves `a₁ : F₁ ⟶ G₁` and `a₂ : F₂ ⟶ G₂`
on the big fppf site of `S` both have `P` in the sense of Stacks 025V, then so does their
product `a₁ × a₂ : F₁ × F₂ ⟶ G₁ × G₂`. -/
@[stacks 02WM]
theorem hasSchemeProperty_prod_map (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition] {F₁ F₂ G₁ G₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂)
    (h₁ : HasSchemeProperty B S hS P a₁) (h₂ : HasSchemeProperty B S hS P a₂) :
    HasSchemeProperty B S hS P (prod.map a₁ a₂) :=
  have : MorphismProperty.IsStableUnderBaseChange
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf :=
    MorphismProperty.relative_isStableUnderBaseChange _
  MorphismProperty.prod_map _ a₁ a₂ h₁ h₂

end AlgebraicGeometry.Space

end
