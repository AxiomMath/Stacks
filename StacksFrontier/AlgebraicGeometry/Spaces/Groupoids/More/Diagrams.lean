module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.PointwiseComposition

/-!
# The composition diagram of a groupoid in algebraic spaces

For a groupoid in algebraic spaces the space of composable pairs of arrows sits in a diagram
with the arrow space and the object space in which three squares are cartesian: the defining
fibre-product square of the source and the target, the square formed by composition and the
second projection over two copies of the source, and the square formed by composition and the
first projection over two copies of the target. This file registers **Stacks 04P9** on the
three results which prove them.

## Main results

No result is proved here. The three cartesian squares of the diagram are

* `AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`, the lower-left square, which
  holds for arbitrary algebraic spaces with no groupoid in sight;
* `AlgebraicGeometry.Space.isPullback_comp_source`, the lower-right square, which is
  **Stacks 043Z**, the square formed by composition and the second projection over two copies
  of the source;
* `AlgebraicGeometry.Space.isPullback_fst_comp`, the upper square, which is the triangle on
  top of **Stacks 043Z**: the first projection out of the space of composable pairs of arrows
  and the composition of a groupoid in algebraic spaces form a cartesian square with two
  copies of the target morphism, a composable pair being determined by its first arrow
  together with its composite.

## Implementation notes

The upper square is cartesian for a reason that is visible only after evaluation at a test
scheme, where the groupoid structure becomes available: it is
`Deformation.PointwiseGroupoid.isPullback_comp_fst`, transported along the comparison
`AlgebraicGeometry.composableArrowsIsoPullback` of the presheaf of composable pairs with the
chosen fibre product. The transport is through the presheaf category, where a square is
cartesian as soon as it is cartesian at every object, and then down into the full subcategory
of algebraic spaces, where a square is cartesian as soon as its image of presheaves is. That
argument is in `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable`,
beside the two squares of Stacks 043Z it belongs with.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 043Z](https://stacks.math.columbia.edu/tag/043Z)
* [Stacks Project, Tag 04P9](https://stacks.math.columbia.edu/tag/04P9)
-/

@[expose] public section

add_to_stacks 04P9 "the lower-left square"
  AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct

add_to_stacks 04P9 "the lower-right square"
  AlgebraicGeometry.Space.isPullback_comp_source

add_to_stacks 04P9 "the upper square"
  AlgebraicGeometry.Space.isPullback_fst_comp

end
