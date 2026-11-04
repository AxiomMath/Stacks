module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper

/-!
# Stacks tags for cohomology and base change for proper morphisms

The declarations below are in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper`; this file records the
Stacks tags they realize.

* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat`:
  Stacks 0CTM, part (1).
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_single_and_isIso_baseChange`:
  Stacks 0CTM, part (2), with `𝒢` flat over `Y` (the source's "flat over `S`" is false; see the
  docstring of the declaration for a counterexample).

Stacks 0E6A is
`AlgebraicGeometry.Space.exists_openSubspace_iff_isFiniteLocallyFreeOfIntRankInDegree_of_isProper`.

## References

* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0E6A](https://stacks.math.columbia.edu/tag/0E6A)
-/

add_to_stacks 0CTM "(1)"
  AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat

add_to_stacks 0CTM "(2), with 𝒢 flat over Y (the source's 'flat over S' is false)"
  AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_single_and_isIso_baseChange

add_to_stacks 0E6A
  AlgebraicGeometry.Space.exists_openSubspace_iff_isFiniteLocallyFreeOfIntRankInDegree_of_isProper
