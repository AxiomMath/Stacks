module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenRelationEtaleQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatChartAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatPresentationRepresentableDiagonal

/-!
# The packaged forms of Stacks 04S6 compared

Clauses of [Stacks, Tag 04S6] appear as hypotheses in four shapes:

* `AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection` — condition (3), the
  shape the bootstrap layer consumes;
* `AlgebraicGeometry.Stack.Bootstrap04S6Spaces` — condition (3) again, with the two relative
  properties written out as anonymous morphism properties instead of through the packaged
  `AlgebraicGeometry.Space.flatProperty` and
  `AlgebraicGeometry.Space.locallyOfFinitePresentationProperty`;
* `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf` — condition (1), for a pre-relation;
* `AlgebraicGeometry.Space.Theorem04S6Quotient` — condition (1) again, for the pre-relation of a
  groupoid in algebraic spaces.

This module identifies the two shapes of condition (3) with each other, and derives the
groupoid shape of condition (1), and condition (3), from the pre-relation shape of condition (1).

## Main results

* `AlgebraicGeometry.Stack.bootstrap04S6Spaces_iff_isBootstrapAlgebraicSpaceAlongFlatSurjection`:
  the two shapes of condition (3) are the same statement.
* `AlgebraicGeometry.Space.theorem04S6Quotient_of_quotientSheaf`: condition (1) for a
  pre-relation implies condition (1) for a groupoid in algebraic spaces.
* `AlgebraicGeometry.Stack.bootstrap04S6Spaces_of_quotientSheaf`: condition (1) implies
  condition (3) in its second shape.

## References

* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-- The target map of the pre-relation of a groupoid in algebraic spaces is the groupoid's own
target map. -/
theorem groupoidPreRelation_target_left (H : GroupoidInAlgebraicSpaces C S hS A) :
    (groupoidPreRelation H).target.left = H.target.hom := by
  rw [PreRelation.target, prod.lift_fst]
  rfl

/-- The source map of the pre-relation of a groupoid in algebraic spaces is the groupoid's own
source map. -/
theorem groupoidPreRelation_source_left (H : GroupoidInAlgebraicSpaces C S hS A) :
    (groupoidPreRelation H).source.left = H.source.hom := by
  rw [PreRelation.source, prod.lift_snd]
  rfl

variable (C) (S) (hS) in
/-- Condition (1) of [Stacks, Tag 04S6] for pre-relations implies condition (1) for groupoids in
algebraic spaces. -/
theorem theorem04S6Quotient_of_quotientSheaf
    [HasSheafify (BigFppfOver.topology C S hS) (Type u)]
    (h04S6 : Bootstrap04S6QuotientSheaf C S hS) :
    Theorem04S6Quotient C S hS := by
  intro Bs H hequiv hsflat htflat hslfp htlfp
  refine h04S6 (groupoidPreRelation H) H.arrows.property H.objects.property hequiv ?_ ?_ ?_ ?_ <;>
    simpa only [groupoidPreRelation_target_left, groupoidPreRelation_source_left]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The two shapes of condition (3) of [Stacks, Tag 04S6] are equivalent:
`AlgebraicGeometry.Stack.Bootstrap04S6Spaces` holds if and only if
`AlgebraicGeometry.Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection` does. -/
theorem bootstrap04S6Spaces_iff_isBootstrapAlgebraicSpaceAlongFlatSurjection :
    Bootstrap04S6Spaces B S hS ↔
      Space.IsBootstrapAlgebraicSpaceAlongFlatSurjection B S hS :=
  ⟨fun h => h, fun h => h⟩

/-- Condition (1) of [Stacks, Tag 04S6] for pre-relations implies condition (3) in the shape
`AlgebraicGeometry.Stack.Bootstrap04S6Spaces`. -/
theorem bootstrap04S6Spaces_of_quotientSheaf
    (h04S6 : Space.Bootstrap04S6QuotientSheaf B S hS) :
    Bootstrap04S6Spaces B S hS :=
  (bootstrap04S6Spaces_iff_isBootstrapAlgebraicSpaceAlongFlatSurjection B S hS).mpr
    (Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf B S hS h04S6)

end AlgebraicGeometry.Stack

end
