module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces

/-!
# The groupoid of points of a groupoid in algebraic spaces (Stacks 044P)

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site. Stacks 044P writes down the contravariant functor on the big fppf
site sending a test object `T` to the groupoid with objects `U(T)` and arrows `R(T)`, with the
source, target and composition of `G`, and sending a morphism of test objects to the pullback of
points. This file records that functor.

## Main results

The functor of Stacks 044P is the composite of two constructions this library already has: the
object-and-arrow data of `G` as a groupoid in presheaves,
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.toGroupoidInFunctors`, followed by the evaluation
functor of a groupoid in presheaves, `Deformation.evaluationFunctor`. That each of its values is
a groupoid and not merely a category is `Deformation.evaluationFunctor_groupoid`.

## Implementation notes

No new declaration is introduced. `Deformation.evaluationFunctor` takes values in categories and
each value carries the groupoid structure, so the composite *is* the groupoid-valued functor the
source displays; writing a second copy of it as a `Grpd`-valued functor would name no new
mathematics. The groupoid-valued repackaging that the quotient stack construction needs is
`AlgebraicGeometry.Stack.evaluationGroupoidFunctor`.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044P](https://stacks.math.columbia.edu/tag/044P)
* [Stacks Project, Tag 06KB](https://stacks.math.columbia.edu/tag/06KB)
-/

@[expose] public section

add_to_stacks 044P "the groupoid data on the fppf site"
  AlgebraicGeometry.GroupoidInAlgebraicSpaces.toGroupoidInFunctors
add_to_stacks 044P "the functor of pointwise groupoids" Deformation.evaluationFunctor
add_to_stacks 044P "each pointwise value is a groupoid" Deformation.evaluationFunctor_groupoid

end
