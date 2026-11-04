module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid

/-!
# The quotient stack of a group action (Stacks 044Q, part (2))

Let `B` be an algebraic space over a scheme `S` of a big fppf site, let `G` be a group algebraic
space over `B`, and let `G` act on an algebraic space `X` over `B` through
`a : G ×_B X ⟶ X`. By Stacks 0444 the data `(X, G ×_B X, pr₁, a, m)` is a groupoid in algebraic
spaces over `B`, the *action groupoid*. The *quotient stack* `[X/G]` is, by definition, the
quotient stack `[U/R]` of part (1) of Stacks 044Q applied to that groupoid.

## Main definitions

* `AlgebraicGeometry.Stack.quotientStackOfAction`: **Stacks 044Q**, part (2) — the quotient
  stack `[X/G]` of an action of a group algebraic space on an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.isStack_quotientStackOfAction`,
  `AlgebraicGeometry.Stack.isFiberedInGroupoids_quotientStackOfAction` and
  `AlgebraicGeometry.Stack.isStackInGroupoids_quotientStackOfAction`: `[X/G]` is a stack in
  groupoids over the big fppf site, so the structure functor really is the morphism
  `p : [X/G] ⟶ (Sch/S)_fppf` the source names.

## Placement — Stacks 044Q is a Chapter 78 tag

Stacks 044Q is `spaces-groupoids`, **Chapter 78**. Part (1) is formalized in the sibling file
`QuotientStack.lean`, for the reason recorded there; this file completes the same definition and
is placed beside it for the same reason, with the names a Chapter 78 development would use.

## Implementation notes

Nothing is rebuilt. The action groupoid is Stacks 0444,
`AlgebraicGeometry.Space.groupoidOfAction` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Stabilizer/ActionGroupoid.lean`, whose
`groupoid` field is exactly the `AlgebraicGeometry.GroupoidInAlgebraicSpaces` that part (1)
consumes; the quotient is `AlgebraicGeometry.Stack.quotientStack` of part (1). So the
definition below is the composite of the two, and the three facts about it are the corresponding
facts for part (1) at the action groupoid.

The group algebraic space and the acted-on space are given in the form Stacks 0444 takes: `G`
and `X` are objects of the slice of presheaves over `B`, whose cartesian monoidal structure has
`G ⊗ X = G ×_B X`, with `GrpObj G` the group law `m` and `ModObj G X` the action `a`, together
with the hypotheses that `G` and `X` are algebraic spaces. This is the generality of the source:
no condition is imposed on `B`, on `G`, on `X` or on the action.

`AlgebraicGeometry.Space.actionGroupoid` of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/ActionGroupoidModules.lean` and
`AlgebraicGeometry.Stack.actionGroupoid` of
`StacksFrontier/AlgebraicGeometry/Stacks/SmoothQuotientStack.lean` are two wrappers around the same
`groupoidOfAction`, for the group-algebraic-space bundle and for the slice form respectively.
The slice form is taken here because it is the one `groupoidOfAction` itself states, so no
repackaging intervenes between the source's data and the groupoid.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 02ZP](https://stacks.math.columbia.edu/tag/02ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **Stacks 044Q, part (2).** The quotient stack `[X/G]` of an action of a group algebraic
space `G` over `B` on an algebraic space `X` over `B`, as a category over the big fppf site: the
quotient stack of part (1) of the action groupoid `(X, G ×_B X, pr₁, a, m)` of Stacks 0444, that
is, the stackification of the pointwise groupoid fibration of that groupoid. -/
@[stacks 044Q "part (2): quotient stack of an action"]
noncomputable abbrev quotientStackOfAction
    (B : AlgebraicSpaces C S hS) (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left) :
    BasedCategory (BigFppfOver C S hS) :=
  quotientStack (Space.groupoidOfAction B G X hG hX).groupoid

/-- The quotient stack of an action satisfies descent for the fppf topology. -/
theorem isStack_quotientStackOfAction
    (B : AlgebraicSpaces C S hS) (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left) :
    (quotientStackOfAction B G X hG hX).p.IsStack (BigFppfOver.topology C S hS) :=
  isStack_quotientStack _

/-- The quotient stack of an action is fibred in groupoids. -/
theorem isFiberedInGroupoids_quotientStackOfAction
    (B : AlgebraicSpaces C S hS) (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left) :
    (quotientStackOfAction B G X hG hX).p.IsFiberedInGroupoids :=
  isFiberedInGroupoids_quotientStack _

/-- The quotient stack of an action is a stack in groupoids over the big fppf site, in the sense
of Stacks 02ZI: the two clauses above together. -/
theorem isStackInGroupoids_quotientStackOfAction
    (B : AlgebraicSpaces C S hS) (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left) :
    Functor.IsStackInGroupoids (quotientStackOfAction B G X hG hX).p
      (BigFppfOver.topology C S hS) :=
  isStackInGroupoids_quotientStack _

end AlgebraicGeometry.Stack

end
