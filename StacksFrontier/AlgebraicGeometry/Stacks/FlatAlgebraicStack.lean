module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects

/-!
# Flat 1-morphisms of algebraic stacks (Stacks 06PW)

Following Stacks 06PW, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is flat* when it
passes the existential smooth-diagram test of Stacks 06FM at flatness of morphisms of algebraic
spaces: there are algebraic spaces `U` and `V` over `S`, a 1-morphism `a` from the category
fibred in groupoids attached to `U` to `𝒳` which is smooth and surjective on objects, a
1-morphism `b` from the one attached to `V` to `𝒴` which is smooth, and a morphism `h : U ⟶ V`
of presheaves whose associated 1-morphism makes the square 2-commute, such that `h` is a flat
morphism of algebraic spaces.

Flatness of morphisms of algebraic spaces is smooth local on the source and the target (Stacks
06FC), so by Stacks 06FM this one test is equivalent to the test on *every* smooth diagram and
the notion is well defined; the equivalence itself is Stacks 06FM and is not used here, since
Stacks 06PW *is* the existential form.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsFlat`: **Stacks 06PW**.

## Implementation notes

The test is the existential criterion of Stacks 06FM, written out longhand rather than through a
named predicate, in the same way and for the same reason as the predicates of
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack`: Stacks 06FM's criterion and the
smoothness notion it is phrased in are abbreviations, so the quantifier written out is *the same*
proposition, and writing it out keeps this file independent of the three theorems of Stacks 06FM,
which are what make the criterion well behaved but are not part of Stacks 06PW's statement.

Concretely, two abbreviations are inlined. Smoothness of the two legs `a` and `b` is the notion of
Stacks 04XB at `AlgebraicGeometry.Space.smoothMorphismProperty`, i.e. representability by
algebraic spaces together with the relative property of **Stacks 03YK** there; both instance
hypotheses of `AlgebraicGeometry.Stack.HasRelativeProperty` are discharged for smoothness, by
`AlgebraicGeometry.Space.instIsStableUnderBaseChangeSmoothMorphismProperty` (Stacks 03ZE) and
`AlgebraicGeometry.Space.smooth_isLocalAtTarget_fppf` (Stacks 0429 at the fppf precoverage), so
no hypothesis on the property is carried. And the property being tested, flatness of a morphism
of presheaves, is applied directly to `h` rather than through a
`CategoryTheory.MorphismProperty` on presheaves evaluated at `h`.

The index universe of the fppf precoverage inside the locality instance argument of
`AlgebraicGeometry.Stack.HasRelativeProperty` is a fourth universe parameter, independent of the
three of the categories fibred in groupoids; it is fixed at `u + 1` here, which is where Stacks
06FM's criterion asks for it, and `AlgebraicGeometry.Space.smooth_isLocalAtTarget_fppf` is
polymorphic in it.

A scheme-valued point and the passage from an algebraic space over it to one over `S` are as in
`AlgebraicGeometry.Stack.HasRelativeProperty`; the 1-morphism attached to a morphism of
presheaves is `AlgebraicGeometry.Stack.associatedMap` (**Stacks 0458**), whose value is recorded
by a subtype, so its underlying 1-morphism is its first component.

## References

* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06PW.** A 1-morphism of algebraic stacks over `S` is *flat* when it passes the
existential smooth-diagram test of Stacks 06FM at flatness of morphisms of algebraic spaces:
there are algebraic spaces `U`, `V` over `S`, a smooth 1-morphism `a` from the category fibred in
groupoids of `U` to the source which is surjective on objects, a smooth 1-morphism `b` from the
one of `V` to the target, and a morphism `h : U ⟶ V` making the square 2-commute, with `h` a flat
morphism of algebraic spaces. -/
@[stacks 06PW]
abbrev IsFlat {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hU : IsAlgebraicSpace B S hS U)
    (_hV : IsAlgebraicSpace B S hS V)
    (a : Stack.fibredCategory B S hS U ⟶ 𝒳.1)
    (b : Stack.fibredCategory B S hS V ⟶ 𝒴.1)
    (h : U ⟶ V),
      Nonempty ((Stack.associatedMap B S hS h).1 ≫ b ≅ a ≫ f.hom) ∧
      (∃ ha : Stack.IsRepresentableByAlgebraicSpaces B S hS a.hom,
        Stack.HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
          (Space.smoothMorphismProperty B S hS) a ha) ∧
      Stack.IsSurjectiveOnObjects B S hS
        (Stack.fibredCategory B S hS U).val.p 𝒳.1.val.p
        (CatFiberedInGroupoids.homFunctor a) ∧
      (∃ hb : Stack.IsRepresentableByAlgebraicSpaces B S hS b.hom,
        Stack.HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
          (Space.smoothMorphismProperty B S hS) b hb) ∧
      Space.IsFlat B S hS h

end AlgebraicGeometry.Stack.AlgebraicStacks

end
