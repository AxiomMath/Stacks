module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjective
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Base change of a universally injective morphism of algebraic stacks (Stacks 0CI3)

The base change of a universally injective 1-morphism of algebraic stacks over `S` by any
1-morphism of algebraic stacks is universally injective. This is **Stacks 0CI3**.

## Main results

* `AlgebraicGeometry.Stack.universallyInjective_baseChange`: **Stacks 0CI3**.

## Implementation notes

Both hypothesis and conclusion are stated for an arbitrary 2-fibre-product square, so the result
applies to any model of the base change and needs no comparison of models; in a square over the
cospan `(g, f)` the base change of `f` is the projection `fst` to the source of `g`.

Unwinding the two statements, the content is exactly the pasting law: a test square `Q` over
`(k, P.fst)` for the base change `P.fst` pastes with `P` to a test square over `(k ≫ g, f)` for
`f`, with the *same* apex and the *same* first projection
(`CategoryTheory.Bicategory.TwoCommSq.pasteFst`), and the pasted square is again a 2-fibre
product by `CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`. So the injectivity asked of
`Q.fst` is literally an instance of the injectivity the hypothesis provides.

## References

* [Stacks Project, Tag 0CI3](https://stacks.math.columbia.edu/tag/0CI3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CI3.** The base change of a universally injective 1-morphism `f : 𝒳 ⟶ 𝒴` of
algebraic stacks over `S` along any `g : 𝒵 ⟶ 𝒴` is universally injective: in a 2-fibre-product
square over `(g, f)`, the projection to `𝒵` is universally injective. -/
@[stacks 0CI3, ega "IV 11.9.14" "base change stability"]
theorem universallyInjective_baseChange {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (hf : UniversallyInjective B S hS f)
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P) :
    UniversallyInjective B S hS P.fst := by
  intro 𝒲 k Q hQ
  exact hf 𝒲 (k ≫ g) (P.pasteFst Q) (Bicategory.isTwoFibreProduct_pasteFst P hP Q hQ)

end AlgebraicGeometry.Stack

end
