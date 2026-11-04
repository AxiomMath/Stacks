module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureQuotientChart
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeExistenceUniversallyClosed

/-!
# The point of a represented algebraic stack named by a point of the algebraic space

`AlgebraicGeometry.Stack.EtaleLocalStructure.pointsMap_chart_point` produces the point of the
quotient stack `[U/R]` over a given point of `|U|` by inverting the bijection of **Stacks 04XL**
between the points of the algebraic space `U` represents and the points of the category fibred in
groupoids it represents. A consumer whose point of `|U|` is fixed in advance by something else —
as the residue field point of the fibre step of **Stacks 0DU5** is — needs to know which point of
`|U|` that inversion returns.

This module records the two identifications that answer it: the point of `|U|` the inversion
returns is the one the representing equivalence attaches to the given point of the algebraic
space, and that point is the class of the residue field point at the underlying scheme point.

## Main results

* `AlgebraicGeometry.Stack.EtaleLocalStructure.spacePointMap_id_eq_pointsMap_representing`: the
  tautological chart point map of an algebraic space is the chart point map of a representing
  equivalence followed by the equivalence's inverse.
* `AlgebraicGeometry.Stack.EtaleLocalStructure.pointClass_closedPointFieldValuedPoint_eq`: the
  point of the algebraic stack of `U` that `z` names is the class of the residue field point at
  the scheme point underlying `z`.

## Implementation notes

The first result is `AlgebraicGeometry.Stack.spacePointMap_comp` at the tautological chart,
together with the fact that the two based functors of an equivalence over the site induce mutually
inverse maps on points. It is what identifies the hypothesis the choice of chart point in the
proof of `AlgebraicGeometry.Stack.EtaleLocalStructure.pointsMap_chart_point` satisfies: the based
functor the presentation of the self-intersection carries as its source presentation is the
inverse of the representing equivalence.

The second result is read off the identification of the points of a represented algebraic stack
with the points of its scheme: both sides have the same underlying scheme point, by
`AlgebraicGeometry.Stack.pointsHomeomorphScheme_representedChartPointMap` on the one side and by
`AlgebraicGeometry.Stack.schemePoint_closedPointFieldValuedPoint` on the other, and that
identification is injective.

## References

* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0DU3](https://stacks.math.columbia.edu/tag/0DU3)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The tautological chart point map factors through the chart point map of a representing
equivalence.** Composing the latter with the inverse based functor of the representing equivalence
returns the former. -/
theorem spacePointMap_id_eq_pointsMap_representing
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (e : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (z : Space.points B S hS F) :
    spacePointMap B S hS F (fibredCategory B S hS F)
        (BasedFunctor.id (fibredCategory B S hS F).val) z =
      pointsMap B S hS 𝒳.val 𝒳.property (fibredCategory B S hS F).property
        (representingEquivalence B S hS F 𝒳 e).inverse
        (spacePointMap B S hS F 𝒳 (representingEquivalence B S hS F 𝒳 e).functor z) := by
  have key : spacePointMap B S hS F 𝒳 (representingEquivalence B S hS F 𝒳 e).functor z =
      pointsMap B S hS (fibredCategory B S hS F).val
        (fibredCategory B S hS F).property 𝒳.property
        (representingEquivalence B S hS F 𝒳 e).functor
        (spacePointMap B S hS F (fibredCategory B S hS F)
          (BasedFunctor.id (fibredCategory B S hS F).val) z) := by
    have h := spacePointMap_comp B S hS F (fibredCategory B S hS F) 𝒳
      (BasedFunctor.id (fibredCategory B S hS F).val)
      (representingEquivalence B S hS F 𝒳 e).functor
    rw [BasedFunctor.id_comp] at h
    exact congrFun h z
  rw [key]
  exact ((pointsEquivOfBasedEquivalence B S hS (fibredCategory B S hS F).property 𝒳.property
    (representingEquivalence B S hS F 𝒳 e)).left_inv _).symm

/-- **The point of the algebraic stack of `U` named by a point of the algebraic space `U`
represents is the class of the residue field point at the scheme point underlying it.** -/
theorem pointClass_closedPointFieldValuedPoint_eq (U : BigFppfOver B S hS)
    (z : Space.points B S hS (yoneda.obj U))
    (hz : B.Contains (Spec (.of (((BigFppfOver.toScheme B S hS).obj U).residueField
      (Space.pointsToScheme B S hS U z))))) :
    pointClass B S hS (schemeFibredCategory B S hS U).val
        (schemeFibredCategory B S hS U).property
        (closedPointFieldValuedPoint B S hS U (Space.pointsToScheme B S hS U z) hz) =
      representedChartPointMap B S hS U z := by
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  refine (pointsHomeomorphScheme B S hS U).injective ?_
  rw [pointsHomeomorphScheme_representedChartPointMap,
    pointsHomeomorphScheme_eq_schemePoint, schemePoint_closedPointFieldValuedPoint]

end AlgebraicGeometry.Stack.EtaleLocalStructure

end
