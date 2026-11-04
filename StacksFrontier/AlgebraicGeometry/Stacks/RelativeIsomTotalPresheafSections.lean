module

public import StacksFrontier.AlgebraicGeometry.Stacks.IsomTotalPresheafAlgebraic
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsTotalPresheafSections
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.RelativeDiagonalFibreGlobalSections

/-!
# Sections of the sheaf of isomorphisms lifting a 2-morphism

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks, `Z` an algebraic space, `x₁, x₂ : Z ⟶ 𝒳`
and `α : x₁ ≫ f ⟶ x₂ ≫ f`. A section of the structure morphism
`Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z` of the sheaf of Stacks 06PP
(`AlgebraicGeometry.Stack.relativeIsomorphismTotalPresheaf`) is the same thing as a natural
family of vertical morphisms `x₁(z) ⟶ x₂(z)`, indexed by the points `z` of `Z`, lying over the
components of `α`: that is, a 2-morphism `x₁ ⟶ x₂` whose image under `f` is `α`.

## Main results

* `AlgebraicGeometry.Stack.relativeIsomorphismSectionEquiv`: sections of
  `Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z` are natural families of vertical morphisms over `α`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry.Stack

universe u w

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Sections of `Isom^α_{𝒳/𝒴}(x₁, x₂) ⟶ Z` are natural families of vertical morphisms
`x₁(z) ⟶ x₂(z)` over the components of `α`.** A section of the total presheaf over the identity of
`Z` is a global section of the presheaf of vertical morphisms on the category of elements of `Z`
(`CategoryTheory.PresheafOfCategories.elementsTotalSectionEquiv`), and those are the natural
families
(`CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre.relVertHomGlobalSectionEquiv`). -/
noncomputable def relativeIsomorphismSectionEquiv (f : 𝒳 ⟶ 𝒴)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    {s : Z ⟶ relativeIsomorphismTotalPresheaf B S hS Z hZ f x₁ x₂ α //
      s ≫ PresheafOfCategories.elementsTotalProj Z
        (relVertHomPresheaf 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
          (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w) = 𝟙 Z} ≃
      RelVertFamily (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p
        (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).toFunctor :=
  (PresheafOfCategories.elementsTotalSectionEquiv Z _).trans
    (relVertHomGlobalSectionEquiv 𝒴.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      (relativeIsomorphismTwistedPoint B S hS Z hZ f x₁ x₂ α).w f.hom.hom.w)

end AlgebraicGeometry.Stack

end
