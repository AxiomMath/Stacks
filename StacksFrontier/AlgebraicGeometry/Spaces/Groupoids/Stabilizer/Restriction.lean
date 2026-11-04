module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.RestrictionArrows

/-!
# Restricting a groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`,
and let `g : U' ⟶ U` be an arbitrary morphism of algebraic spaces. Then `U'` and the space
`U' ×_{g, U, t} R ×_{s, U, g} U'` of arrows of `G` with a lift of each endpoint form again a
groupoid in algebraic spaces over `B`, the *restriction* of `G` to `U'`, and the projections to
`U` and `R` are a morphism of groupoids which is fully faithful after evaluation at every test
object. That is Stacks 044B, and it is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrict`, together with
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Restriction`, which packages the restricted
groupoid with the identification of its object space, its arrow space and its four structure
morphisms, its canonical morphism to `G`, and the pointwise full faithfulness of that morphism.
This module re-exports them.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
-/
