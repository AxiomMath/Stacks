module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphism

/-!
# Smooth 1-morphisms of algebraic stacks (Stacks 075U)

Following Stacks 075U, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is smooth* when it
passes the existential smooth-diagram test of Stacks 06FM at smoothness of morphisms of algebraic
spaces: there are algebraic spaces `U` and `V` over `S`, a 1-morphism `a` from the category fibred
in groupoids attached to `U` to `𝒳` which is smooth and surjective on objects, a 1-morphism `b`
from the one attached to `V` to `𝒴` which is smooth, and a morphism `h : U ⟶ V` of presheaves
whose associated 1-morphism makes the square 2-commute, such that `h` is a smooth morphism of
algebraic spaces.

Smoothness of morphisms of algebraic spaces is smooth local on the source and the target, so by
Stacks 06FM this one test is equivalent to the test on *every* smooth diagram and the notion is
well defined; the equivalence itself is Stacks 06FM and is not used here, since Stacks 075U *is*
the existential form.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth`: **Stacks 075U**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks`
  `.hasPropertyOnSomeSmoothDiagram_isLocallyOfFinitePresentation_of_isSmooth`: a smooth
  1-morphism of algebraic stacks passes the existential smooth-diagram test at local finite
  presentation of morphisms of algebraic spaces.

## Implementation notes

The test is condition (2) of Stacks 06FM, which is formalized as
`AlgebraicGeometry.Stack.HasPropertyOnSomeSmoothDiagram`, applied at smoothness of morphisms of
algebraic spaces, `AlgebraicGeometry.Space.IsSmooth` (**Stacks 03ZC**, part (1)). This is the same
proposition as the longhand quantifier that
`AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat` (**Stacks 06PW**) writes out, as
`isFlat_iff_hasPropertyOnSomeSmoothDiagram` records for flatness; here the named condition is used
directly rather than inlined, so that the two sister notions stay one notion and cannot drift.

Note that the property being tested is smoothness of the *horizontal* morphism `h` of algebraic
spaces, while the smoothness required of the two *vertical* 1-morphisms `a` and `b` is the
different notion `AlgebraicGeometry.Stack.IsRelativelySmooth` of Stacks 04XB — the relative
property of **Stacks 03YK** at `AlgebraicGeometry.Space.smoothMorphismProperty`. Both instance
hypotheses of that notion are discharged for smoothness, so this definition carries no hypothesis
on either property.

**Stacks 0DNP is formalized in `StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone`
(with `@[stacks 0DNP]`); the result below is the pointwise half of it, proved here untagged.**
Stacks 0DNP says a smooth 1-morphism of algebraic stacks is locally of finite presentation. Smoothness
(Stacks 075U) is the *existential* smooth-diagram test and local finite presentation
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFinitePresentation`, **Stacks 06Q2**,
part (1)) is the *universal* one, so 0DNP is the pointwise implication Stacks 04AJ followed by
the implication "condition (2) implies condition (1)" of Stacks 06FM. That second step is the
long half of Stacks 06FM — the source argues it through a diagram on
`U ×_𝒳 U'`, `U ×_𝒴 V'` and `V ×_𝒴 V'` and four applications of the smooth-locality package of
Stacks 06F8 — and it is not in this library: `StacksDraft.AlgebraicGeometry.Stacks`
`.SmoothLocalMorphismEvery` has only the easy converse
`hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram`, and
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_relative` needs `f` representable,
which Stacks 0DNP does not assume. So the pointwise half is proved here, untagged, and Stacks
0DNP is proved separately in `SmoothLocalMorphismMonotone` rather than derived from it here.

## References

* [Stacks Project, Tag 04AJ](https://stacks.math.columbia.edu/tag/04AJ)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0DNP](https://stacks.math.columbia.edu/tag/0DNP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 075U.** A 1-morphism of algebraic stacks over `S` is *smooth* when it passes the
existential smooth-diagram test of Stacks 06FM at smoothness of morphisms of algebraic spaces:
there are algebraic spaces `U`, `V` over `S`, a smooth 1-morphism `a` from the category fibred in
groupoids of `U` to the source which is surjective on objects, a smooth 1-morphism `b` from the
one of `V` to the target, and a morphism `h : U ⟶ V` making the square 2-commute, with `h` a
smooth morphism of algebraic spaces. -/
@[stacks 075U]
abbrev IsSmooth {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  Stack.HasPropertyOnSomeSmoothDiagram B S hS
    (fun _ _ h => Space.IsSmooth B S hS h) f.hom

/-- A smooth 1-morphism of algebraic stacks over `S` passes the existential smooth-diagram test
of Stacks 06FM at local finite presentation of morphisms of algebraic spaces: its own smooth
diagram has top horizontal morphism smooth, hence locally of finite presentation by
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isSmooth` (**Stacks 04AJ**).

This is the pointwise half of Stacks 0DNP; see the implementation notes for the half of Stacks
06FM that is still needed to upgrade the conclusion to
`AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyOfFinitePresentation`, which is the universal
test. -/
theorem hasPropertyOnSomeSmoothDiagram_isLocallyOfFinitePresentation_of_isSmooth
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} (hf : IsSmooth B S hS f) :
    Stack.HasPropertyOnSomeSmoothDiagram B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h) f.hom := by
  obtain ⟨U, V, hU, hV, a, b, h, hη, ha, hsurj, hb, hsm⟩ := hf
  exact ⟨U, V, hU, hV, a, b, h, hη, ha, hsurj, hb,
    Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
