module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport

/-!
# Quasi-compact morphisms of algebraic spaces

The section of the source on quasi-compact morphisms of algebraic spaces observes that a
representable morphism is quasi-compact exactly when every base change to a quasi-compact
algebraic space is quasi-compact, takes the latter as the definition of a quasi-compact
morphism of algebraic spaces, so that it agrees with the existing notion for representable
morphisms, and notes that a morphism from a quasi-compact algebraic space to a quasi-separated
one, such as an affine scheme, is quasi-compact.

## Implementation notes

The definition is `AlgebraicGeometry.Space.IsQuasiCompact` (Tag 03HE), its agreement with the
representable notion `AlgebraicGeometry.Space.presheaf_quasiCompact_iff_isQuasiCompact`
(Tag 03HD), and the last observation
`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace` (Tag 073B, part (1)), applied to an
absolutely quasi-separated target. The section tag is registered on these three declarations.

## References

* [Stacks Project, Tag 03HC](https://stacks.math.columbia.edu/tag/03HC)
-/

@[expose] public section

add_to_stacks 03HC "quasi-compact morphisms of algebraic spaces"
  AlgebraicGeometry.Space.IsQuasiCompact
add_to_stacks 03HC "agreement with the notion for representable morphisms"
  AlgebraicGeometry.Space.presheaf_quasiCompact_iff_isQuasiCompact
add_to_stacks 03HC "a morphism from a quasi-compact space to a quasi-separated one is
  quasi-compact" AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace
