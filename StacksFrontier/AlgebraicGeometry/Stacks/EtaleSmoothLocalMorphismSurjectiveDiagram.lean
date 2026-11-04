module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEveryConverse

/-!
# The universal étale-smooth diagram criterion implies the existential one (Stacks 0CIF)

Let `P` be a property of morphisms of algebraic spaces over `S` and let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S`. This file proves the implication **(1) ⇒ (2)** of the
first assertion of **Stacks 0CIF**, in the form in which that implication is actually available:
once *one* diagram of algebraic spaces over `f` with smooth right-hand vertical 1-morphism,
surjective left-hand vertical 1-morphism and étale comparison to the 2-fibre product exists at
all, condition (1) hands condition (2) that very diagram.

So (1) ⇒ (2) carries no content beyond the **existence** of such a diagram, and the existence is
isolated here as `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram`, a statement in which
`P` does not occur. Together with the converse implication
`hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram`, in this same
namespace, this reduces the equivalence of the two tests to that one existence statement.

## Main definitions

* `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram`: the diagram data of
  **Stacks 0CIF** condition (2) with the clause about `P` dropped — a smooth right-hand vertical
  1-morphism, a surjective left-hand vertical 1-morphism, and an étale comparison to every
  2-fibre product of the cospan.

## Main results

* `hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram`: condition (1)
  of Stacks 0CIF implies condition (2), given such a diagram.
* `hasPropertyOnEveryEtaleSmoothDiagram_iff_some_of_hasSurjectiveEtaleSmoothDiagram`: the two
  conditions are equivalent, given such a diagram and an étale-smooth local `P`.

## Implementation notes

No `@[stacks]` attribute. The key `"equivalence of parts (1) and (2)"` of Stacks 0CIF asserts the
equivalence for every Deligne–Mumford `f`, with no diagram supplied; the `iff` proved here instead
*assumes* a diagram, so it is a strictly weaker statement and is not a covering set for that key.
It is recorded because it is the whole of the implication that is not the existence statement.

Deriving `HasSurjectiveEtaleSmoothDiagram` from `AlgebraicGeometry.Stack.IsDM` is **Stacks 0CIA**,
which rests on the structure theorem **Stacks 06N3** that a DM algebraic stack admits a surjective
étale presentation by a scheme; neither is available, so the key stays open. What this file fixes
is that nothing else is missing: `P` and its étale-smooth locality play no role in (1) ⇒ (2).

## References

* [Stacks Project, Tag 0CFZ](https://stacks.math.columbia.edu/tag/0CFZ)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The diagram data of condition (2) of Stacks 0CIF, without the clause about `P`.** There is
a 2-commutative square of algebraic spaces over `f` whose right-hand vertical 1-morphism is
smooth, whose left-hand vertical 1-morphism is surjective, and whose every comparison 1-morphism
from the square's cone to a 2-fibre product of `(b, f)` is étale.

For a Deligne–Mumford `f` this is what **Stacks 0CIA** provides, and it is the only thing
condition (1) of Stacks 0CIF needs in order to give condition (2). -/
abbrev HasSurjectiveEtaleSmoothDiagram
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom),
      IsSurjective B S hS a ∧
      IsRelativelySmooth B S hS b.hom ∧
      (∀ (Q : Bicategory.TwoCommSq b.hom f.hom)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (k : Bicategory.TwoCommSq.PreHom
          (diagramCone B S hS f.hom a.hom b.hom h η) Q),
          IsRelativelyEtale B S hS k.hom)

/-- **Condition (1) of Stacks 0CIF implies condition (2).** If some diagram of algebraic spaces
over `f : 𝒳 ⟶ 𝒴` has smooth right-hand vertical 1-morphism, surjective left-hand vertical
1-morphism and étale comparison to every 2-fibre product of its cospan, then the universal
étale-smooth diagram test for `P` gives the existential one — on that same diagram, since the
universal test applies to it and its conclusion is the one remaining clause.

No hypothesis on `P` is used: the étale-smooth locality of Stacks 0CFZ is needed only for the
converse implication. -/
theorem hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hex : HasSurjectiveEtaleSmoothDiagram B S hS f)
    (hevery : HasPropertyOnEveryEtaleSmoothDiagram B S hS P f) :
    HasPropertyOnSomeEtaleSmoothDiagram B S hS P f := by
  obtain ⟨U, V, hU, hV, a, b, h, η, hasu, hbsm, hcompar⟩ := hex
  exact ⟨U, V, hU, hV, a, b, h, η, hasu, hbsm, hcompar,
    hevery U V hU hV a b h η hbsm hcompar⟩

/-- **The first assertion of Stacks 0CIF, given a diagram.** For a property `P` of morphisms of
algebraic spaces over `S` which is étale-smooth local on the source-and-target, and a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` admitting a diagram as in
`AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagram`, the universal and existential
étale-smooth diagram tests agree.

Stacks 0CIF asserts this for every Deligne–Mumford `f`, with the diagram produced by Stacks 0CIA
rather than assumed; this statement is therefore weaker and carries no `@[stacks]` attribute. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_iff_some_of_hasSurjectiveEtaleSmoothDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hex : HasSurjectiveEtaleSmoothDiagram B S hS f) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f ↔
      HasPropertyOnSomeEtaleSmoothDiagram B S hS P f :=
  ⟨hasPropertyOnSomeEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleSmoothDiagram B S hS P f hex,
    hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram B S hS P hP f⟩

end AlgebraicGeometry.Stack

end
