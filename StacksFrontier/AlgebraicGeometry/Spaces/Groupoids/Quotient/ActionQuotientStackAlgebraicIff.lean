module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.GerbeGroupDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackAlgebraicIffRestriction

/-!
# Algebraicity of the quotient stack of a group action (Stacks 06PK)

Let a group algebraic space `G` over an algebraic space `B` over a scheme `S` of a big fppf site
act on an algebraic space `X` over `B`. **Stacks 06PK** states that the quotient stack `[X/G]` is
an algebraic stack exactly when there is a morphism `φ : X' ⟶ X` of algebraic spaces over `B` for
which `(g, x') ↦ g • φ x'` is a surjection of fppf sheaves `G ×_B X' ⟶ X` and both projections to
`X'` of the space of triples `{(x₁, g, x₂) : φ x₁ = g • φ x₂}` are flat and locally of finite
presentation.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_action_iff_exists_cover` and
  `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_groupoidOfAction_iff_exists_cover`:
  **Stacks 06PK**, for any action groupoid construction of Stacks 0444 and for the one the
  library builds.

## Implementation notes

The source deduces Stacks 06PK from Stacks 06PJ applied to the action groupoid of Stacks 0444;
the translation between the two criteria is
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_action_iff` of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.GerbeGroupDescent`, whose statement takes
the biconditional of Stacks 06PJ as an argument. That biconditional is
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_iff_restrictionAlong`, whose implication
towards algebraicity goes through Stacks 06FI
(`AlgebraicGeometry.Stack.forall_isAlgebraicStack_quotientStack_of_flat`). Supplying it gives the
statement with nothing carried.

## References

* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
* [Stacks Project, Tag 06PK](https://stacks.math.columbia.edu/tag/06PK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u w

namespace AlgebraicGeometry.Stack

/-- **Stacks 06PK.** Let a group algebraic space `G` over an algebraic space `B` act on an
algebraic space `X` over `B`. The quotient stack `[X/G]` of the action groupoid of
**Stacks 0444** is an algebraic stack exactly when there is a morphism `φ : X' ⟶ X` of algebraic
spaces over `B` for which

1. `G ×_B X' ⟶ X`, `(g, x') ↦ g • φ x'`, is a surjection of fppf sheaves, and
2. both projections to `X'` of the space of triples `{(x₁, g, x₂) : φ x₁ = g • φ x₂}`, the fibre
   product `X' ×_{φ, X, a} (G ×_B X')`, are flat and locally of finite presentation.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_action_iff` with the
biconditional of **Stacks 06PJ** it takes supplied by
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_iff_restrictionAlong`. -/
@[stacks 06PK "for any action groupoid construction of Stacks 0444"]
theorem isAlgebraicStack_quotientStack_action_iff_exists_cover
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left)
    (A : Space.ActionGroupoidConstruction B G X hG hX) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack A.groupoid) ↔
      ∃ (X' : Over B.obj) (_ : IsAlgebraicSpace C S hS X'.left) (φ : X' ⟶ X),
        let a : G ⊗ X' ⟶ X := (𝟙 G ⊗ₘ φ) ≫ γ[G, X]
        Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) a.left ∧
        Space.IsFlat C S hS (pullback.fst φ.left a.left) ∧
        Space.IsLocallyOfFinitePresentation C S hS (pullback.fst φ.left a.left) ∧
        Space.IsFlat C S hS (pullback.snd φ.left a.left ≫ (snd G X').left) ∧
        Space.IsLocallyOfFinitePresentation C S hS
          (pullback.snd φ.left a.left ≫ (snd G X').left) :=
  isAlgebraicStack_quotientStack_action_iff.{u, w} C S hS B G X hG hX A
    (fun H => isAlgebraicStack_quotientStack_iff_restrictionAlong.{u, w} H)

/-- **Stacks 06PK for the action groupoid of Stacks 0444 that the library builds.** The quotient
stack `[X/G]` is an algebraic stack exactly when there is a morphism `φ : X' ⟶ X` of algebraic
spaces over `B` for which `G ×_B X' ⟶ X`, `(g, x') ↦ g • φ x'`, is a surjection of fppf sheaves
and both projections to `X'` of the space of triples `{(x₁, g, x₂) : φ x₁ = g • φ x₂}` are flat
and locally of finite presentation.

This is `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_groupoidOfAction_iff` with the
biconditional of Stacks 06PJ it takes supplied as in
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_action_iff_exists_cover`. -/
@[stacks 06PK "for the action groupoid of Stacks 0444 that the library builds"]
theorem isAlgebraicStack_quotientStack_groupoidOfAction_iff_exists_cover
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (B : AlgebraicSpaces C S hS)
    (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left) :
    IsAlgebraicStack.{u, w} C S hS
        (quotientStack (Space.groupoidOfAction B G X hG hX).groupoid) ↔
      ∃ (X' : Over B.obj) (_ : IsAlgebraicSpace C S hS X'.left) (φ : X' ⟶ X),
        let a : G ⊗ X' ⟶ X := (𝟙 G ⊗ₘ φ) ≫ γ[G, X]
        Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) a.left ∧
        Space.IsFlat C S hS (pullback.fst φ.left a.left) ∧
        Space.IsLocallyOfFinitePresentation C S hS (pullback.fst φ.left a.left) ∧
        Space.IsFlat C S hS (pullback.snd φ.left a.left ≫ (snd G X').left) ∧
        Space.IsLocallyOfFinitePresentation C S hS
          (pullback.snd φ.left a.left ≫ (snd G X').left) :=
  isAlgebraicStack_quotientStack_groupoidOfAction_iff.{u, w} C S hS B G X hG hX
    (fun H => isAlgebraicStack_quotientStack_iff_restrictionAlong.{u, w} H)

end AlgebraicGeometry.Stack

end
