module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Points

/-!
# Thickenings of algebraic stacks (Stacks 0BPP)

A *thickening* of algebraic stacks over `S` is a closed immersion which is surjective on the
underlying sets of points: the source is realised as a closed substack of the target whose
underlying space is all of it. A *morphism of thickenings* is a 2-commutative square whose two
vertical arrows are the specified thickenings, and both notions have a relative form over a
fixed algebraic stack.

## Main definitions

* `AlgebraicGeometry.Stack.IsThickening`: **Stacks 0BPP**, part (1).
* `AlgebraicGeometry.Stack.ThickeningMorphism`: **Stacks 0BPP**, part (2).
* `AlgebraicGeometry.Stack.ThickeningOver`: **Stacks 0BPP**, part (3), thickenings over a stack.
* `AlgebraicGeometry.Stack.ThickeningMorphismOver`: **Stacks 0BPP**, part (3), morphisms over a
  stack.

## Main results

There are no propositional results here.

## Implementation notes

Surjectivity on points is stated through `AlgebraicGeometry.Stack.pointsMap`, the map on
field-valued point classes, exactly as `AlgebraicGeometry.Stack.IsSurjective` (Stacks 04ZS) is.
The closed immersion is the §04XB relative property of Stacks 04YL part (2), i.e.
`AlgebraicGeometry.Stack.AlgebraicStacks.IsClosedImmersion`, so the specified inclusion stays
available to base change and composition rather than being replaced by a full subcategory.

The source's part (1) also records that the induced continuous map of underlying topological
spaces is a **homeomorphism**. That statement is deliberately **not** here: it has to be phrased
through the point topology of Stacks 04XL, and 04XL has no library site under either of its part
keys, so the homeomorphism clause is not yet statable. It is the only part key of 0BPP this file
does not carry, and the file is tagged accordingly — see the implementation note on each
declaration.

All four squares are 2-commutative, not strictly commutative: the comparison is an isomorphism of
1-morphisms in the 2-category of algebraic stacks, and for a morphism of thickenings it is
precisely the statement that the ambient morphism restricts to the inner one.

Three naming notes. `AlgebraicGeometry.Stack.IsThickening` is a condition on a 1-morphism of
algebraic **stacks**; it is a different notion from the scheme-level
`Stacks.Thickenings.IsThickening` (Stacks 04EX) and from
`AlgebraicGeometry.RingedSpaceThickening.IsThickening` (Stacks 08KZ), and inside this namespace
the bare name is the stack one. The three structures are named
`Thickening…` rather than carrying the source's bare `Morphism`, `Over` and `MorphismOver`,
because a root-level `Over` in this namespace would shadow `CategoryTheory.Over` for every file
that opens both — the shadowing hazard that a duplicate `DottedArrow` already produced in this
area.

## References

* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0BPP**, part (1). A 1-morphism of algebraic stacks over `S` *is a thickening* when it
is a closed immersion, in the sense of Stacks 04YL part (2), and is surjective on the underlying
sets of points.

The source's part (1) also asserts that the induced map of underlying topological spaces is a
homeomorphism; that clause needs the point topology of Stacks 04XL, which has no library site, so
it is not stated here. -/
@[stacks 0BPP "part (1): thickening"]
abbrev IsThickening {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (i : 𝒳 ⟶ 𝒴) : Prop :=
  AlgebraicStacks.IsClosedImmersion B S hS i ∧
    Function.Surjective
      (pointsMap B S hS 𝒳.val.val
        (Classical.choose 𝒳.property) (Classical.choose 𝒴.property) i.hom.hom)

/-- **Stacks 0BPP**, part (2). A *morphism of thickenings* from the thickening `i` to the
thickening `j` of algebraic stacks over `S`: a 1-morphism of the ambient stacks, a 1-morphism of
the closed substacks, and a 2-isomorphism saying that the former restricts to the latter. -/
@[stacks 0BPP "part (2): morphisms of thickenings"]
structure ThickeningMorphism {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (i : 𝒳 ⟶ 𝒳') (j : 𝒴 ⟶ 𝒴') (_hi : IsThickening i) (_hj : IsThickening j) where
  /-- The 1-morphism between the ambient algebraic stacks. -/
  outer : 𝒳' ⟶ 𝒴'
  /-- The restricted 1-morphism between the closed substacks. -/
  inner : 𝒳 ⟶ 𝒴
  /-- The restriction square 2-commutes, which is what it means for `outer` to restrict to
  `inner`. -/
  comm : inner ≫ j ≅ i ≫ outer

/-- **Stacks 0BPP**, part (3). A thickening of algebraic stacks over `S` together with a
1-morphism from its ambient stack to a fixed algebraic stack `𝒵`. -/
@[stacks 0BPP "part (3): thickenings over a stack"]
structure ThickeningOver (𝒵 : AlgebraicStacks.{u, w} B S hS) where
  /-- The closed substack. -/
  source : AlgebraicStacks.{u, w} B S hS
  /-- The ambient algebraic stack. -/
  ambient : AlgebraicStacks.{u, w} B S hS
  /-- The specified closed inclusion of the substack into the ambient stack. -/
  inclusion : source ⟶ ambient
  /-- The specified inclusion is a thickening. -/
  isThickening : IsThickening inclusion
  /-- The structure 1-morphism of the ambient stack to the base. -/
  toBase : ambient ⟶ 𝒵

/-- **Stacks 0BPP**, part (3). A morphism of thickenings of algebraic stacks over a fixed
algebraic stack `𝒵`: a morphism of the underlying thickenings whose ambient component lies over
the base up to 2-isomorphism. -/
@[stacks 0BPP "part (3): morphisms over a stack"]
structure ThickeningMorphismOver {𝒵 : AlgebraicStacks.{u, w} B S hS}
    (𝒳 𝒴 : ThickeningOver.{u, w} 𝒵) where
  /-- The morphism of the two specified thickenings. -/
  hom : ThickeningMorphism 𝒳.inclusion 𝒴.inclusion 𝒳.isThickening 𝒴.isThickening
  /-- The ambient 1-morphism is over the base, up to 2-isomorphism. -/
  over : hom.outer ≫ 𝒴.toBase ≅ 𝒳.toBase

end AlgebraicGeometry.Stack

end
