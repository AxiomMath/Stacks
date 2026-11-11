module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfFiniteSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjectionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem

/-!
# Stacks 07VR, 07VS and 07VT

This module declares nothing; it imports the three modules that prove Stacks 07VR, 07VS and 07VT.
Each tag is registered by a `@[stacks]` attribute on its declaration:

* `AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite` (Stacks 07VR), in
  `StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem`: a finite morphism of algebraic
  spaces `X ⟶ Y`, with `Y` quasi-compact and quasi-separated, is a limit of finite morphisms of
  finite presentation `X_i ⟶ Y` with closed immersions as transition morphisms.
* `AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective` (Stacks 07VS), in
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineOfFiniteSurjection`: the target of a finite
  surjection from an affine algebraic space is affine.
* `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`
  (Stacks 07VT), in
  `StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjectionUnconditional`: the
  target of a universally closed surjection from an affine algebraic space is affine.

The forms that take conclusions of other tags as hypotheses,
`AlgebraicGeometry.Space.integralFiniteSystem_of_isFinite` (07VR),
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_isFinite` (07VS) and
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed` (07VT), are not
registered.

## References

* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
-/
