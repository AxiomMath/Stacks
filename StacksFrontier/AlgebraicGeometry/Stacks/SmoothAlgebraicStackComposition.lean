module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp

/-!
# Composition of smooth 1-morphisms of algebraic stacks (Stacks 075V)

**Stacks 075V** asserts that the composite of two smooth 1-morphisms of algebraic stacks over `S`
(**Stacks 075U**, `AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth`) is smooth. The source
proves it by combining the composition remark **Stacks 06FP** with the two facts that smoothness
of morphisms of algebraic spaces is smooth local on the source-and-target (**Stacks 06FC**, the
smooth case) and stable under composition (**Stacks 03ZD**), and nothing else.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_comp`: **Stacks 075V**.

## Implementation notes

Stacks 075U *is* condition (2) of Stacks 06FM at smoothness of morphisms of algebraic spaces —
`AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth` is an abbreviation for
`AlgebraicGeometry.Stack.HasPropertyOnSomeSmoothDiagram` at that property — so no passage between
the existential and the universal form of the criterion is needed here, and the result is Stacks
06FP applied directly. That is the one difference from the sister statements
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_comp` (Stacks 06FT) and
`...isLocallyOfFinitePresentation_comp` (Stacks 06Q3), which are defined over the universal form
and therefore have to make the round trip, and from `...isFlat_comp` (Stacks 06PX), whose notion
inlines the longhand quantifier and needs the recorded bridge.

The two hypotheses of Stacks 06FP are supplied at smoothness by
`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_smooth` and
`AlgebraicGeometry.Space.isSmooth_comp`, which are the source's own two ingredients.

The declaration has the same leaf name as the corresponding statement for morphisms of *algebraic
spaces*, `AlgebraicGeometry.Space.isSmooth_comp`. They are different notions about different
objects and are distinguished by namespace exactly as
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_comp` (Stacks 06PX) is distinguished from
`AlgebraicGeometry.Space.isFlat_comp` (Stacks 03MN); the space-level one is the composition
hypothesis this consumes.

## References

* [Stacks Project, Tag 03ZD](https://stacks.math.columbia.edu/tag/03ZD)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FP](https://stacks.math.columbia.edu/tag/06FP)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

/-- **Stacks 075V.** The composite of two smooth 1-morphisms of algebraic stacks over `S` is
smooth: the composition remark Stacks 06FP at smoothness of morphisms of algebraic spaces, which
is smooth local on the source-and-target by the smooth case of Stacks 06FC and stable under
composition by Stacks 03ZD. -/
@[stacks 075V]
theorem isSmooth_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsSmooth B S hS f) (hg : IsSmooth B S hS g) :
    IsSmooth B S hS (f ≫ g) :=
  Stack.hasPropertyOnSomeSmoothDiagram_comp.{u, w} B S hS
    (fun _ _ h => Space.IsSmooth B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (fun hU hV hW p q hp hq => Space.isSmooth_comp B S hS hU hV hW p q hp hq)
    𝒳.property 𝒴.property 𝒵.property f.hom g.hom hf hg

end AlgebraicGeometry.Stack.AlgebraicStacks

end
