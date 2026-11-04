module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfFiniteSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjectionUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismLimitSystem

/-!
# Registration of Stacks 07VR, 07VS and 07VT

* `AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite` (Stacks 07VR): a finite
  morphism of algebraic spaces `X ⟶ Y`, with `Y` quasi-compact and quasi-separated, is a limit of
  finite morphisms of finite presentation `X_i ⟶ Y` with closed immersions as transition morphisms.
* `AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective` (Stacks 07VS): the
  target of a finite surjection from an affine algebraic space is affine.
* `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`
  (Stacks 07VT): the target of a universally closed surjection from an affine algebraic space is
  affine.

## References

* [Stacks Project, Tag 07VR](https://stacks.math.columbia.edu/tag/07VR)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
-/

@[expose] public section

add_to_stacks 07VR AlgebraicGeometry.Space.exists_integralFiniteSystem_of_isFinite

add_to_stacks 07VS AlgebraicGeometry.Space.isAffineSpace_target_of_isFinite_of_isSurjective

add_to_stacks 07VT
  AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace

end
