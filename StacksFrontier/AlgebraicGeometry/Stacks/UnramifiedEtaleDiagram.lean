module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism

/-!
# Unramifiedness tested on every étale diagram (Stacks 0CIY)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Condition (2) of **Stacks 0CIY**
asks that `f` be Deligne–Mumford and that for every algebraic space `V` with a 1-morphism
`V ⟶ 𝒴` — smooth or not — and every algebraic space `U` with an étale 1-morphism
`U ⟶ V ×_𝒴 𝒳`, the morphism `U ⟶ V` of algebraic spaces be unramified. This file introduces
that test and derives condition (1), unramifiedness in the sense of **Stacks 0CIT**.

## Main definitions

* `AlgebraicGeometry.Stack.HasPropertyOnEveryEtaleDiagram`: the diagram test of condition (2) of
  Stacks 0CIY at a property `P` of morphisms of algebraic spaces over `S`.
* `AlgebraicGeometry.Stack.IsUnramifiedOnEveryEtaleDiagram`: condition (2) of Stacks 0CIY.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleDiagram`:
  the étale diagram test implies the étale-smooth diagram test of Stacks 0CIF.
* `AlgebraicGeometry.Stack.isUnramified_of_isUnramifiedOnEveryEtaleDiagram`: **Stacks 0CIY**, the
  implication (2) ⇒ (1).

## Implementation notes

Condition (2) is rendered as the universal étale-smooth diagram test
`AlgebraicGeometry.Stack.HasPropertyOnEveryEtaleSmoothDiagram` with the smoothness clause on the
right-hand vertical 1-morphism deleted, and nothing else changed. The two readings agree: a
diagram over `f` with étale comparison to a 2-fibre product of `(b, f)` is the same datum as a
1-morphism `b : V ⟶ 𝒴` out of an algebraic space together with an étale 1-morphism from an
algebraic space `U` to `V ×_𝒴 𝒳`, the diagram's top horizontal morphism being the induced
`U ⟶ V`; and the comparison need only be checked at one 2-fibre product, by
`AlgebraicGeometry.Stack.isRelativelyEtale_preHom_of_one`. Read that way the implication (2) ⇒ (1)
is the deletion of a hypothesis, which is the whole of that implication: the source's own proof
of (1) ⇒ (2) is the step with content, since it has to produce the conclusion for a `b` that is
not smooth, and it does so from base change and composition of unramified 1-morphisms of
algebraic stacks (**Stacks 0CIV** and **Stacks 0CIU**), neither of which is available here.

The test is stated for an arbitrary property `P` of morphisms of algebraic spaces over `S`, as
Stacks 0CIF's tests are, so that the deletion lemma is available at properties other than
unramifiedness; no locality of `P` is used.

## References

* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIU](https://stacks.math.columbia.edu/tag/0CIU)
* [Stacks Project, Tag 0CIV](https://stacks.math.columbia.edu/tag/0CIV)
* [Stacks Project, Tag 0CIY](https://stacks.math.columbia.edu/tag/0CIY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The diagram test of condition (2) of Stacks 0CIY.** For every 2-commutative square of
algebraic spaces over `f` whose every comparison 1-morphism from the square's cone to a 2-fibre
product of `(b, f)` is étale, the top horizontal morphism of algebraic spaces has `P`.

This is `AlgebraicGeometry.Stack.HasPropertyOnEveryEtaleSmoothDiagram` with the smoothness clause
on the right-hand vertical 1-morphism deleted, so it tests `P` on more diagrams. -/
abbrev HasPropertyOnEveryEtaleDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (h : U ⟶ V)
    (η : (associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom),
      (∀ (Q : Bicategory.TwoCommSq b.hom f.hom)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (k : Bicategory.TwoCommSq.PreHom
          (diagramCone B S hS f.hom a.hom b.hom h η) Q),
          IsRelativelyEtale B S hS k.hom) →
      P (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩)

/-- **Condition (2) of Stacks 0CIY.** The 1-morphism `f` is Deligne–Mumford and every étale
diagram of algebraic spaces over it has unramified top horizontal morphism, in the sense of
`AlgebraicGeometry.Space.IsUnramified` (**Stacks 03ZH**, part (1)). -/
abbrev IsUnramifiedOnEveryEtaleDiagram
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsDM B S hS f ∧
    HasPropertyOnEveryEtaleDiagram B S hS
      (fun {_ _} (g : _ ⟶ _) => Space.IsUnramified B S hS g.hom :
        MorphismProperty (AlgebraicSpaces B S hS)) f

/-- **The étale diagram test implies the étale-smooth diagram test of Stacks 0CIF.** The latter
tests `P` on the diagrams whose right-hand vertical 1-morphism is in addition smooth, so the
implication is the discarding of that hypothesis. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleDiagram
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : HasPropertyOnEveryEtaleDiagram B S hS P f) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f :=
  fun U V hU hV a b h η _hbsm hk => hf U V hU hV a b h η hk

/-- **Stacks 0CIY, the implication (2) ⇒ (1).** A Deligne–Mumford 1-morphism of algebraic stacks
over `S` whose every étale diagram of algebraic spaces has unramified top horizontal morphism is
unramified in the sense of Stacks 0CIT. -/
@[stacks 0CIY "the implication (2) => (1)"]
theorem isUnramified_of_isUnramifiedOnEveryEtaleDiagram
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    (hf : IsUnramifiedOnEveryEtaleDiagram.{u, w} B S hS f) :
    IsUnramified B S hS f :=
  ⟨hf.1, hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnEveryEtaleDiagram B S hS _ hf.2⟩

end AlgebraicGeometry.Stack

end
