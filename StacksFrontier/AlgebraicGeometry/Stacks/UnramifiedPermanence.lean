module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSourceAndTarget.EtaleSmoothExamples
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationCancellation

/-!
# Permanence of unramifiedness in a tower of algebraic stacks (Stacks 0CIZ)

Let `𝒳 → 𝒴 → 𝒵` be 1-morphisms of algebraic stacks over `S`. **Stacks 0CIZ** says that if
`𝒳 → 𝒵` is unramified and `𝒴 → 𝒵` is Deligne–Mumford then `𝒳 → 𝒴` is unramified. This file
proves it from the nested presentations the source chooses, which are taken as a hypothesis.

## Main definitions

* `AlgebraicGeometry.Stack.HasSurjectiveEtaleSmoothDiagramOver`: a diagram of algebraic spaces
  over `f` of the shape **Stacks 0CIF** condition (2) asks for, whose top horizontal morphism
  continues into such a diagram over `f ≫ g`.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnEveryEtaleSmoothDiagram_of_comp`: the étale-smooth
  diagram test of Stacks 0CIF cancels the second factor of a composite, for a property of
  morphisms of algebraic spaces that is étale-smooth local on the source-and-target and cancels
  the second factor there.
* `AlgebraicGeometry.Stack.isUnramified_of_comp`: **Stacks 0CIZ**.

## Implementation notes

The source's proof chooses an algebraic space `W` with `W → 𝒵` surjective smooth, then `V` with
`V → 𝒴 ×_𝒵 W` surjective étale, then `U` with `U → 𝒳 ×_𝒴 V` surjective étale; the composite
`U → W` is then the top horizontal morphism of an étale-smooth diagram over `𝒳 → 𝒵`, hence
unramified, and `U → V` is unramified by **Stacks 06G6**. Only the second and third choices use
the Deligne–Mumford hypotheses, and both are **Stacks 0CIA**, which rests on the structure
theorem **Stacks 06N3** — a Deligne–Mumford algebraic stack admits a surjective étale
presentation by a scheme — and is not available in this library. The two nested presentations are
therefore carried as the hypothesis `HasSurjectiveEtaleSmoothDiagramOver`, which packages exactly
what they produce: one diagram over `𝒳 → 𝒴` whose top horizontal morphism extends to one over
`𝒳 → 𝒵`. Everything else in the argument is discharged.

Once those presentations are supplied the Deligne–Mumford hypothesis on `𝒴 → 𝒵` is not used
again, so it is not part of the statement below; what it is used for in the source is producing
the presentation of `𝒴 ×_𝒵 W`. The Deligne–Mumford conclusion on `𝒳 → 𝒴` is **Stacks 050M**
part (1), `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_of_comp`, which needs no hypothesis on
the second factor either.

Passing from the one diagram to the universal test of Stacks 0CIT is the implication (2) ⇒ (1) of
Stacks 0CIF, proved in this namespace as
`hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram`, and that is the
only place étale-smooth locality of unramifiedness — **Stacks 0CG3** at the unramified entry —
is used.

## References

* [Stacks Project, Tag 050M](https://stacks.math.columbia.edu/tag/050M)
* [Stacks Project, Tag 06G6](https://stacks.math.columbia.edu/tag/06G6)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 0CG3](https://stacks.math.columbia.edu/tag/0CG3)
* [Stacks Project, Tag 0CIA](https://stacks.math.columbia.edu/tag/0CIA)
* [Stacks Project, Tag 0CIF](https://stacks.math.columbia.edu/tag/0CIF)
* [Stacks Project, Tag 0CIT](https://stacks.math.columbia.edu/tag/0CIT)
* [Stacks Project, Tag 0CIZ](https://stacks.math.columbia.edu/tag/0CIZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A diagram of algebraic spaces over `f` that extends to one over `f ≫ g`.** There are
algebraic spaces `U`, `V`, `W` over `S` with 1-morphisms `a : U ⟶ 𝒳`, `b : V ⟶ 𝒴`, `c : W ⟶ 𝒵`
and morphisms `h : U ⟶ V`, `k : V ⟶ W` such that `(a, b, h)` is a diagram over `f` and
`(a, c, h ≫ k)` one over `f ≫ g`, both of the shape condition (2) of **Stacks 0CIF** asks for:
`a` surjective, the right-hand vertical 1-morphism smooth, and every comparison 1-morphism from
the diagram's cone to a 2-fibre product of its cospan étale.

This is what the two nested applications of **Stacks 0CIA** in the proof of Stacks 0CIZ produce:
a surjective smooth `W ⟶ 𝒵`, a surjective étale `V ⟶ 𝒴 ×_𝒵 W` and a surjective étale
`U ⟶ 𝒳 ×_𝒴 V`. -/
abbrev HasSurjectiveEtaleSmoothDiagramOver
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) : Prop :=
  ∃ (U V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V)
    (hW : IsAlgebraicSpace B S hS W)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (b : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴)
    (c : algebraicSpaceStack.{u, w} B S hS W hW ⟶ 𝒵)
    (h : U ⟶ V) (k : V ⟶ W)
    (η : (associatedMap B S hS h).1 ≫ b.hom ≅ a.hom ≫ f.hom)
    (θ : (associatedMap B S hS (h ≫ k)).1 ≫ c.hom ≅ a.hom ≫ (f ≫ g).hom),
      IsSurjective B S hS a ∧
      IsRelativelySmooth B S hS b.hom ∧
      IsRelativelySmooth B S hS c.hom ∧
      (∀ (Q : Bicategory.TwoCommSq b.hom f.hom)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (m : Bicategory.TwoCommSq.PreHom
          (diagramCone B S hS f.hom a.hom b.hom h η) Q),
          IsRelativelyEtale B S hS m.hom) ∧
      (∀ (Q : Bicategory.TwoCommSq c.hom (f ≫ g).hom)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (m : Bicategory.TwoCommSq.PreHom
          (diagramCone B S hS (f ≫ g).hom a.hom c.hom (h ≫ k) θ) Q),
          IsRelativelyEtale B S hS m.hom)

/-- **The étale-smooth diagram test of Stacks 0CIF cancels the second factor of a composite.**
Let `P` be a property of morphisms of algebraic spaces over `S` which is étale-smooth local on
the source-and-target (**Stacks 0CFZ**) and cancels first factors there. If the composite
`f ≫ g` passes the universal étale-smooth diagram test at `P`, and there is a diagram over `f`
extending to one over `f ≫ g`, then `f` passes that test.

The extended diagram's top horizontal morphism has `P` by the test for `f ≫ g`; cancelling `k`
leaves `P` on `h`, which exhibits the existential test for `f`; and the existential test gives
the universal one by the implication (2) ⇒ (1) of Stacks 0CIF. -/
theorem hasPropertyOnEveryEtaleSmoothDiagram_of_comp
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : Space.IsEtaleSmoothLocalOnSourceAndTarget B S hS P)
    (hcancel : ∀ {X Y Z : AlgebraicSpaces B S hS} (p : X ⟶ Y) (q : Y ⟶ Z), P (p ≫ q) → P p)
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : HasPropertyOnEveryEtaleSmoothDiagram B S hS P (f ≫ g))
    (hdata : HasSurjectiveEtaleSmoothDiagramOver.{u, w} B S hS f g) :
    HasPropertyOnEveryEtaleSmoothDiagram B S hS P f := by
  obtain ⟨U, V, W, hU, hV, hW, a, b, c, h, k, η, θ, hasu, hbsm, hcsm, hmet, hmet'⟩ := hdata
  have htop : P ((ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩) ≫
      (ObjectProperty.homMk k : (⟨V, hV⟩ : AlgebraicSpaces B S hS) ⟶ ⟨W, hW⟩)) :=
    hfg U W hU hW a c (h ≫ k) θ hcsm hmet'
  exact hasPropertyOnEveryEtaleSmoothDiagram_of_hasPropertyOnSomeEtaleSmoothDiagram
    B S hS P hP f ⟨U, V, hU, hV, a, b, h, η, hasu, hbsm, hmet, hcancel _ _ htop⟩

/-- **Stacks 0CIZ.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over
`S`. If `f ≫ g` is unramified, then `f` is unramified.

`f` is Deligne–Mumford by Stacks 050M part (1). For the étale-smooth diagram test, the nested
presentations supply a diagram over `f` extending to one over `f ≫ g`; the extended diagram's
top horizontal morphism is unramified, hence so is the one over `f` by **Stacks 06G6**. -/
@[stacks 0CIZ "carrying as a hypothesis the two nested surjective etale presentations that the \
source obtains from Stacks 0CIA, which this library does not have because Stacks 06N3 is not \
proved; once they are given, the Deligne-Mumford hypothesis on the second factor is not used"]
theorem isUnramified_of_comp {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsUnramified B S hS (f ≫ g))
    (hdata : HasSurjectiveEtaleSmoothDiagramOver.{u, w} B S hS f g) :
    IsUnramified B S hS f :=
  ⟨AlgebraicStacks.isDM_of_comp B S hS f g hfg.1,
    hasPropertyOnEveryEtaleSmoothDiagram_of_comp B S hS _
      (Space.isUnramified_isEtaleSmoothLocalOnSourceAndTarget B S hS)
      (fun {X Y Z} p q hpq => Space.isUnramified_of_comp B S hS X.property Y.property Z.property
        p.hom q.hom hpq) f g hfg.2 hdata⟩

end AlgebraicGeometry.Stack

end
