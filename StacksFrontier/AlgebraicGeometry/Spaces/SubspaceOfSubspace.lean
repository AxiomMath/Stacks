module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation

/-!
# A subspace of a presheaf is a subspace of any larger subfunctor (Stacks 02YX)

Let `F₁ ≤ F₂` be subfunctors of a presheaf `F` on the big fppf site over `S`, and suppose
`F₁` is an open, closed, or locally closed subspace of `F`. Then the image of `F₁` inside
`F₂` is a subspace of `F₂` of the same kind. The subspace of `F₂` cut out by `F₁ ≤ F₂` is
the range of the canonical inclusion `F₁.toFunctor ⟶ F₂.toFunctor`, so the inclusion
hypothesis is part of the resulting subspace rather than an unused assumption.

## Main results

The three assertions of Stacks 02YX, `AlgebraicGeometry.Space.isOpenSubspace_of_le`,
`AlgebraicGeometry.Space.isClosedSubspace_of_le` and
`AlgebraicGeometry.Space.isLocallyClosedSubspace_of_le`, are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria`, together with the
cancellation step `CategoryTheory.MorphismProperty.presheaf_of_comp_mono` they rest on.
This module only re-exports them.

## References

* [Stacks Project, Tag 02YX](https://stacks.math.columbia.edu/tag/02YX)
-/
