module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism

/-!
# An étale morphism of algebraic stacks is unramified

Étaleness and unramifiedness of a 1-morphism of algebraic stacks over `S` are both the
Deligne–Mumford condition together with the universal étale-smooth diagram test, taken at
étaleness and at unramifiedness of morphisms of algebraic spaces. An étale 1-morphism is
unramified.

## Main results

* `AlgebraicGeometry.Stack.isUnramified_of_isEtale`: an étale 1-morphism of algebraic stacks over
  `S` is unramified.

## References

* [Stacks Project, Tag 0CIW](https://stacks.math.columbia.edu/tag/0CIW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An étale 1-morphism of algebraic stacks over `S` is unramified. -/
@[stacks 0CIW]
theorem isUnramified_of_isEtale {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : IsEtale B S hS f) : IsUnramified B S hS f :=
  hasEtaleSmoothLocalProperty_mono B S hS
    (fun {_ _} _ hg => Space.isUnramified_of_isEtale B S hS hg) hf

end AlgebraicGeometry.Stack

end
