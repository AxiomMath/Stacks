module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# Universally injective morphisms of algebraic stacks (Stacks 0CI2)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is *universally injective* when for every
1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks the induced map `|𝒵 ×_𝒴 𝒳| → |𝒵|` on points is
injective.

## Main definitions

* `AlgebraicGeometry.Stack.UniversallyInjective`: **Stacks 0CI2**.

## Implementation notes

The base change is not a chosen model: the condition quantifies over every 2-commutative square
over the cospan `(g, f)` which is a 2-fibre product in the sense of **Stacks 003Q**
(`CategoryTheory.Bicategory.IsTwoFibreProduct`), and asks injectivity of the map on points
induced by its projection `fst` to `𝒵`, which is the base change of `f`. So the condition is
independent of the model, and a consumer may instantiate it at whichever model it already has —
in particular at the canonical
`AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare`. Dually, verifying the condition
means verifying it at every model, which is what makes it usable as a hypothesis in the
base-change and composition arguments without a transport step.

The points and the map between them are those of **Stacks 04XG**, in the form
`AlgebraicGeometry.Stack.AlgebraicStacks.pointsMap`, which reads the fibred-in-groupoids witness
each one needs off the algebraic-stack condition of Stacks 026O; which witness is chosen is
immaterial, since `CategoryTheory.Functor.IsFiberedInGroupoids` is a proposition.

This is an abbreviation, so the ordinary `Function.Injective` API applies to it directly.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 0CI2](https://stacks.math.columbia.edu/tag/0CI2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CI2.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is *universally
injective* if for every 1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks over `S` and every 2-fibre
product of `(g, f)` the map `|𝒵 ×_𝒴 𝒳| → |𝒵|` induced by the projection to `𝒵` is injective. -/
@[stacks 0CI2]
abbrev UniversallyInjective {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴) (P : Bicategory.TwoCommSq g f),
    Bicategory.IsTwoFibreProduct P →
      Function.Injective (AlgebraicStacks.pointsMap B S hS P.fst)

end AlgebraicGeometry.Stack

end
