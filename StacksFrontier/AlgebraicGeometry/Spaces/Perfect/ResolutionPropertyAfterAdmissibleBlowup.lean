module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDenseBlowupUnconditional

/-!
# The resolution property after an admissible blowup (Stacks 0GV5)

Let `X` be a quasi-compact and quasi-separated algebraic space whose space of points has finitely
many irreducible components. Stacks 0GV5 asserts a dense quasi-compact open `U ⊆ X` and a
`U`-admissible blowup `X' ⟶ X` such that `X'` has the resolution property.

The statement is proved, with no hypothesis beyond those of the tag, as
`AlgebraicGeometry.Space.exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty`
in `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDenseBlowupUnconditional`.
This file registers it as Stacks 0GV5, with `add_to_stacks` since the declaration is imported
(the `stacks` attribute writes a doc string, which Lean refuses for an imported declaration).

## References

* [Stacks Project, Tag 0GV5](https://stacks.math.columbia.edu/tag/0GV5)
-/

add_to_stacks 0GV5
  AlgebraicGeometry.Space.exists_isQuasiCompact_dense_isAdmissibleBlowup_hasResolutionProperty
