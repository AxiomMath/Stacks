module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphism
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Base change of a universal homeomorphism of algebraic stacks (Stacks 0CI8)

The base change of a universal homeomorphism of algebraic stacks over `S` by any 1-morphism of
algebraic stacks is a universal homeomorphism. Both hypothesis and conclusion are stated for an
arbitrary 2-fibre-product square; in a square over the cospan `(g, f)` the base change of `f` is
the projection `fst` to the source of `g`.

## Main results

* `AlgebraicGeometry.Stack.universalHomeomorphism_baseChange`: the base change of a universal
  homeomorphism of algebraic stacks is a universal homeomorphism.

## References

* [Stacks Project, Tag 0CI7](https://stacks.math.columbia.edu/tag/0CI7)
* [Stacks Project, Tag 0CI8](https://stacks.math.columbia.edu/tag/0CI8)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base change of a universal homeomorphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` along any
`g : 𝒵 ⟶ 𝒴` is a universal homeomorphism: in a 2-fibre-product square over `(g, f)`, the projection
to `𝒵` is a universal homeomorphism. -/
@[stacks 0CI8]
theorem universalHomeomorphism_baseChange {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (hf : UniversalHomeomorphism B S hS f)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P) :
    UniversalHomeomorphism B S hS P.fst := fun 𝒲 k Q hQ ↦
  hf 𝒲 (k ≫ g) (P.pasteFst Q) (Bicategory.isTwoFibreProduct_pasteFst P hP Q hQ)

end AlgebraicGeometry.Stack

end
