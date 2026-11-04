module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackFactorization

/-!
# The reduced closed substack on a closed set of points (Stacks 0509)

**Stacks 0509** asserts that a closed subset `T` of the points of an algebraic stack `𝒳` over `S`
carries exactly one reduced closed substack structure: there is a unique closed substack of `𝒳`
which is reduced and whose set of points is `T`.

This file proves the uniqueness assertion. Two reduced closed substacks of `𝒳` with the same set
of points contain one another: each is a closed substack of `𝒳` whose points contain the image of
the point map of the other's inclusion, so **Stacks 050B** factors that inclusion through it
because the source is reduced, and a factorization of the inclusion is exactly a containment of
object properties.

## Main results

* `AlgebraicGeometry.Stack.le_of_isReducedStack_of_range_pointsMap_subset`: a reduced closed
  substack is contained in every closed substack whose points contain its own.
* `AlgebraicGeometry.Stack.eq_of_isReducedStack_of_range_pointsMap_eq`: the uniqueness assertion
  of **Stacks 0509**.

## Existence, and the full statement

This file proves uniqueness only. Existence, and **Stacks 0509** itself as an existence and
uniqueness statement, are in `StacksFrontier/AlgebraicGeometry/Stacks/ReducedClosedSubstackExistence.lean`
(`AlgebraicGeometry.Stack.exists_isClosedSubstack_isReducedStack_range_pointsMap_eq` and
`AlgebraicGeometry.Stack.existsUnique_reducedClosedSubstack`), which needs the descent of closed
subspaces of a smooth chart and so cannot sit below this file.

## Implementation notes

A closed substack is a property of the objects of `𝒳` satisfying
`AlgebraicGeometry.Stack.IsClosedSubstack`, so uniqueness is an equality of object properties and
containment is the order on them. Reducedness of the substack is
`AlgebraicGeometry.Stack.IsReducedStack` of its full subcategory, i.e. the existential scheme
atlas criterion of **Stacks 04YF** at reducedness, and its set of points is the range of the map
on points induced by its canonical inclusion.

Both statements are given for arbitrary proofs that the full subcategories are algebraic stacks,
rather than for the ones the closed-substack conditions choose, so that no choice enters them.

## References

* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
* [Stacks Project, Tag 050B](https://stacks.math.columbia.edu/tag/050B)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A reduced closed substack is contained in every closed substack carrying its points.** Let
`P` and `Q` cut out closed substacks of an algebraic stack `𝒳` over `S`, with the one cut out by
`P` reduced. If every point of the substack cut out by `P` is a point of the one cut out by `Q`,
then `P ≤ Q`.

By **Stacks 050B** the inclusion of the first substack factors through the second, and a
factorization of that inclusion holds the containment objectwise. -/
theorem le_of_isReducedStack_of_range_pointsMap_subset {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P Q : ObjectProperty 𝒳.val.val.obj}
    (hAP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hQ : IsClosedSubstack 𝒳 Q)
    (hAQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q))
    (hPred : IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hAP))
    (hsub : Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hAP)) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hAQ))) :
    P ≤ Q := by
  have hisoQ : Q.IsClosedUnderIsomorphisms := hQ.1
  have hfac := (factorsThroughSubstack_iff_range_pointsMap_subset B S hS
    (fullSubcategoryInclusion 𝒳 P hAP) hQ hAQ hPred).2 hsub
  rw [factorsThroughSubstack_iff_forall] at hfac
  exact fun x hx => hfac ⟨x, hx⟩

/-- **The uniqueness assertion of Stacks 0509.** Two reduced closed substacks of an algebraic stack `𝒳` over `S`
with the same set of points are equal: each is contained in the other by
`AlgebraicGeometry.Stack.le_of_isReducedStack_of_range_pointsMap_subset`. -/
@[stacks 0509 "uniqueness"]
theorem eq_of_isReducedStack_of_range_pointsMap_eq {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {P Q : ObjectProperty 𝒳.val.val.obj}
    (hP : IsClosedSubstack 𝒳 P) (hQ : IsClosedSubstack 𝒳 Q)
    (hAP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hAQ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 Q))
    (hPred : IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hAP))
    (hQred : IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 Q hAQ))
    (hpoints :
      Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hAP)) =
        Set.range (AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 Q hAQ))) :
    P = Q :=
  le_antisymm
    (le_of_isReducedStack_of_range_pointsMap_subset B S hS hAP hQ hAQ hPred hpoints.subset)
    (le_of_isReducedStack_of_range_pointsMap_subset B S hS hAQ hP hAP hQred hpoints.symm.subset)

end AlgebraicGeometry.Stack

end
