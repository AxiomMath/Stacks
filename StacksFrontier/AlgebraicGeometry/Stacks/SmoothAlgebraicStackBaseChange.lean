module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange

/-!
# A base change of a smooth 1-morphism of algebraic stacks is smooth (Stacks 075W)

Stacks 075W says that a base change of a smooth 1-morphism of algebraic stacks over `S` is
smooth: if `f : 𝒳 ⟶ 𝒴` is smooth in the sense of
`AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth` (**Stacks 075U**) and `g : 𝒴' ⟶ 𝒴` is any
1-morphism of algebraic stacks, then the projection to `𝒴'` of every 2-fibre product of `f`
along `g` is smooth.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_baseChange`: **Stacks 075W**.

## Implementation notes

Smoothness of a 1-morphism of algebraic stacks is condition (2) of Stacks 06FM at smoothness of
morphisms of algebraic spaces, so this is `AlgebraicGeometry.Stack`
`.hasPropertyOnSomeSmoothDiagram_baseChange_of_isStableUnderBaseChange` at that property. Its
one hypothesis on the property is discharged by
`AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange` (**Stacks 03ZE**).

Stacks 06FQ is stated in the source for a property smooth local on the source-and-target, which
for smoothness is **Stacks 06FC**'s smooth case and is open in this library — it rests on Stacks
06F2, descent of smoothness along a smooth covering of the source, which
`StacksDraft.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.Smooth` records as missing.
That hypothesis is not used in the proof of Stacks 06FQ, so
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_baseChange` keeps it only to state the
tag as the source does, and the hypothesis-free
`hasPropertyOnSomeSmoothDiagram_baseChange_of_isStableUnderBaseChange` that proves it is what is
used here. Consequently the statement below is Stacks 075W itself, with no side condition.

The conclusion is stated for an arbitrary 2-fibre product square, so it does not depend on a
chosen model of the 2-fibre product.

## References

* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 075W.** A base change of a smooth 1-morphism of algebraic stacks over `S` is
smooth: for `f : 𝒳 ⟶ 𝒴` smooth and `g : 𝒴' ⟶ 𝒴` arbitrary, the projection to `𝒴'` of any
2-fibre product square over the cospan `(g, f)` is smooth. -/
@[stacks 075W]
theorem isSmooth_baseChange {𝒳 𝒴 𝒴' : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hf : IsSmooth B S hS f) :
    IsSmooth B S hS Q.fst :=
  have : (Stack.spaceProperty B S hS
      (fun _ _ h => Space.IsSmooth B S hS h)).IsStableUnderBaseChange :=
    Space.isSmooth_isStableUnderBaseChange B S hS
  Stack.hasPropertyOnSomeSmoothDiagram_baseChange_of_isStableUnderBaseChange B S hS
    (fun _ _ h => Space.IsSmooth B S hS h) f g Q hQ hf

end AlgebraicGeometry.Stack.AlgebraicStacks

end
