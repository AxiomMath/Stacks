module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordFibreProductEtaleCover
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismSurjectiveDiagram

/-!
# The two étale-smooth diagram tests agree for a Deligne–Mumford morphism (Stacks 0CIF)

Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on
the source-and-target (**Stacks 0CFZ**) and let `f : 𝒳 ⟶ 𝒴` be a Deligne–Mumford 1-morphism of
algebraic stacks over `S`. This file proves the first assertion of **Stacks 0CIF**: `f` passes the
universal étale-smooth diagram test for `P` (condition (1): every diagram `U → V` over `f` with
`V → 𝒴` smooth and `U → 𝒳 ×_𝒴 V` étale has `P` on `U → V`) exactly when it passes the existential
one (condition (2): some such diagram with `U → 𝒳` surjective has `P` on `U → V`).

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_iff_some`: **Stacks 0CIF**, the
  equivalence of conditions (1) and (2) for a Deligne–Mumford 1-morphism.

## Implementation notes

The proof is the source's. (2) ⇒ (1) is
`Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram`, which needs
no hypothesis on `f`. (1) ⇒ (2) applies condition (1) to one diagram with surjective
left-hand vertical 1-morphism; that such a diagram exists for a Deligne–Mumford `f` is
**Stacks 0CIA**, part (2), in the form
`AlgebraicGeometry.Stack.hasSurjectiveEtaleSmoothDiagram_of_isDM_of_forward`, whose input, the
substantial direction of **Stacks 06N3**, is the proved theorem
`AlgebraicGeometry.Stack.existsEtalePresentationOfIsAbsolutelyDM`, read at the terminal scheme,
which every big fppf site contains (`AlgebraicGeometry.BigFppfSite.contains_terminal`). So the
statement has exactly the source's hypotheses.

The two further assertions of Stacks 0CIF, for representable source and target and for a
representable `f`, carry the same tag at
`AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_iff_represented` and
`AlgebraicGeometry.Stack.hasPropertyOnSomeEtaleSmoothDiagram_iff_relative`.

## References

* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CIF, the equivalence of conditions (1) and (2).** Let `P` be a property of
morphisms of algebraic spaces over `S` which is étale-smooth local on the source-and-target, and
let `f : 𝒳 ⟶ 𝒴` be a Deligne–Mumford 1-morphism of algebraic stacks over `S`. Then the following
are equivalent:

1. for every 2-commutative square of algebraic spaces `h : U → V` over `f` with `V → 𝒴` smooth
   and `U → 𝒳 ×_𝒴 V` étale, the morphism `h` has `P`;
2. for some such square with `U → 𝒳` surjective, the morphism `h` has `P`. -/
@[stacks 0CIF "equivalence of parts (1) and (2)"]
theorem hasPropertyOnEveryEtaleSmoothDiagram_iff_some
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsDM B S hS f) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f ↔
      HasPropertyOnSomeEtaleSmoothDiagram B S hS P f :=
  hasPropertyOnEveryEtaleSmoothDiagram_iff_some_of_hasSurjectiveEtaleSmoothDiagram B S hS P hP f
    (hasSurjectiveEtaleSmoothDiagram_of_isDM_of_forward B S hS
      (existsEtalePresentationOfIsAbsolutelyDM.{u, w} B S hS B.contains_terminal) f hf)

end AlgebraicGeometry.Stack

end
