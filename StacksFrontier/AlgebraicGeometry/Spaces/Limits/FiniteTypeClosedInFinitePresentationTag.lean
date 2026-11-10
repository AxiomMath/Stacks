module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeClosedInFinitePresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0872: finite type is closed in finite presentation, for qcqs algebraic spaces

Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over `S` which is locally of
finite type, with `X` and `Y` quasi-compact and quasi-separated. Then there are a morphism of
finite presentation `f' : X' ⟶ Y` and a closed immersion `i : X ⟶ X'` with `i ≫ f' = f`.

This is
`AlgebraicGeometry.Space.exists_isClosedImmersion_isFinitePresentation_of_isLocallyOfFiniteType`,
proved in `StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeClosedInFinitePresentation`
along the source's proof (Stacks 07SU/09NS approximation, Stacks 0828 for the eventual monomorphism,
Stacks 0463 and 082J for quasi-affineness, Stacks 0871 and Stacks 03XQ), with no hypotheses
beyond those of the source. This module registers it as Stacks 0872.

## References

* [Stacks Project, Tag 0872](https://stacks.math.columbia.edu/tag/0872)
-/

add_to_stacks 0872 "a morphism of algebraic spaces over `S`, locally of finite type, with source
  and target quasi-compact and quasi-separated, is a closed immersion `i : X ⟶ X'` followed by a
  morphism of finite presentation `f' : X' ⟶ Y` with `i ≫ f' = f`"
  AlgebraicGeometry.Space.exists_isClosedImmersion_isFinitePresentation_of_isLocallyOfFiniteType
