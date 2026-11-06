module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackOfAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty

/-!
# The action groupoid of a smooth group action is smooth, and its quotient stack is algebraic

Let `B` be an algebraic space over a scheme `S` of a big fppf site, let `G` be a group algebraic
space over `B` acting on an algebraic space `X` over `B`, and suppose `G` is **smooth** over `B`.
The action groupoid `(X, G ×_B X, pr₂, a, m)` of **Stacks 0444** is then a smooth groupoid in
algebraic spaces in the sense of **Stacks 04TH**, so **Stacks 04TK** applies to it: the quotient
stack `[X/G]` of **Stacks 044Q** part (2) is an algebraic stack over `S`.

## Main results

* `AlgebraicGeometry.Space.isSmooth_groupoidOfAction`: the action groupoid of a smooth group
  action is a smooth groupoid in algebraic spaces.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStackOfAction`: the quotient stack of a
  smooth group action is an algebraic stack (Stacks 04TK).

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04TH](https://stacks.math.columbia.edu/tag/04TH)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u w

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- A morphism of presheaves heterogeneously equal to a smooth one, between presheaves equal to
its source and its target, is itself smooth. -/
theorem isSmooth_of_heq
    {F G F' G' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : F' ⟶ G')
    (hsource : F' = F) (htarget : G' = G) (h : HEq f g)
    (hg : IsSmooth C S hS g) :
    IsSmooth C S hS f := by
  subst hsource htarget
  rwa [eq_of_heq h]

/-- **The action groupoid of a smooth group action is a smooth groupoid** (Stacks 04TH). Let a
group algebraic space `G` over an algebraic space `B` over `S` act on an algebraic space `X` over
`B`. If `G` is smooth over `B`, then both structure maps of the action groupoid of Stacks 0444
are smooth morphisms of algebraic spaces over `S`. -/
theorem isSmooth_groupoidOfAction (B : AlgebraicSpaces C S hS) (G X : Over B.obj)
    [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left)
    (hGsm : IsSmooth C S hS G.hom) :
    GroupoidInAlgebraicSpaces.IsSmooth C S hS (groupoidOfAction B G X hG hX).groupoid := by
  have hprod : IsAlgebraicSpace C S hS (pullback G.hom X.hom) :=
    isAlgebraicSpace_pullback C S hS G.hom X.hom hG hX B.property
  have hsnd : IsSmooth C S hS (CartesianMonoidalCategory.snd G X).left :=
    (smoothMorphismProperty C S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct C S hS
        (ObjectProperty.homMk G.hom : (⟨G.left, hG⟩ : AlgebraicSpaces C S hS) ⟶ B)
        (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpaces C S hS) ⟶ B)) hGsm
  have hleft : ∀ {P Q : Over B.obj} {a b : P ⟶ Q}, a = b → a.left = b.left :=
    fun h => congrArg (·.left) h
  have hinviso : IsIso ((Stacks.Groupoids.ActionGroupoid.inverse G X).left) :=
    ⟨(Stacks.Groupoids.ActionGroupoid.inverse G X).left,
      hleft (Stacks.Groupoids.ActionGroupoid.inverse_comp_inverse G X),
      hleft (Stacks.Groupoids.ActionGroupoid.inverse_comp_inverse G X)⟩
  have htgt : IsSmooth C S hS (γ[G, X] : G ⊗ X ⟶ X).left := by
    rw [hleft (Stacks.Groupoids.ActionGroupoid.inverse_source G X).symm]
    exact isSmooth_comp C S hS hprod hprod hX _ _
      (isSmooth_of_isIso C S hS hprod hprod _) hsnd
  have hars := (congrArg (·.obj) (groupoidOfAction B G X hG hX).arrows_eq).symm
  have hobj := (congrArg (·.obj) (groupoidOfAction B G X hG hX).objects_eq).symm
  exact ⟨isSmooth_of_heq _ (CartesianMonoidalCategory.snd G X).left hars hobj
      (groupoidOfAction B G X hG hX).source_eq hsnd,
    isSmooth_of_heq _ (γ[G, X] : G ⊗ X ⟶ X).left hars hobj
      (groupoidOfAction B G X hG hX).target_eq htgt⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **The quotient stack of a smooth group action is an algebraic stack** — Stacks 04TK for the
action groupoid of Stacks 0444. Let a group algebraic space `G`, smooth over an algebraic space
`B` over `S`, act on an algebraic space `X` over `B`. Then `[X/G]` of Stacks 044Q part (2) is an
algebraic stack over `S`. -/
theorem isAlgebraicStack_quotientStackOfAction (B : AlgebraicSpaces C S hS) (G X : Over B.obj)
    [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left)
    (hGsm : Space.IsSmooth C S hS G.hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStackOfAction B G X hG hX) :=
  isAlgebraicStack_quotientStack_of_isSmooth (Space.isSmooth_groupoidOfAction B G X hG hX hGsm)

end AlgebraicGeometry.Stack

end
