module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralCoverByScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfSchemeReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningSchemeRepresentableClosedImmersion

/-!
# A thickening of a scheme is a scheme

Let `S` be a scheme and let `X ⊂ X'` be a thickening of algebraic spaces over `S`. If `X` is
(representable by) a scheme, then so is `X'`. This is [Stacks Project, Tag 05ZR].

## Main results

This module holds no declarations; it collects the imports of the development of Stacks 05ZR.
The two forms of the tag are proved, and carry `@[stacks 05ZR]`, in
`StacksFrontier/AlgebraicGeometry/Spaces/ThickeningSchemeRepresentableClosedImmersion.lean`:

* `AlgebraicGeometry.Space.isRepresentable_of_isThickening_of_isRepresentable`: **Stacks 05ZR**
  in the subspace form of Stacks 05ZK, part (1).
* `AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable`:
  **Stacks 05ZR** in the morphism form `AlgebraicGeometry.Space.IsThickeningHom`.

The same file registers **Stacks 07VU** on
`AlgebraicGeometry.IsAlgebraicSpace.isRepresentable_of_isRepresentable_reduction`: an algebraic
space whose reduction is a scheme is a scheme.

## Implementation notes

Both forms apply `AlgebraicGeometry.Space.isRepresentable_of_isClosedImmersion_of_bijective`,
the closed-immersion form of Stacks 07VV: the inclusion of a thickening is a closed immersion,
injective on points because it is a monomorphism, and surjective on points. That proof is the
reduction to the affine case: a point of `X'` comes from a point of an affine open `W` of the
thin side, the image of `W` is open in `|X'|` because the closed immersion is closed and
bijective on points, and the open subspace it cuts out is affine by the thickening case of
Stacks 07VT, `AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`,
which holds with no hypotheses. Every point of `X'` thus lies in a representable open
subspace, so `X'` is a scheme.

This route does not pass through Stacks 07VU or the general Stacks 07VT, whose library forms
carry hypotheses.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZP](https://stacks.math.columbia.edu/tag/05ZP)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
-/
