module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableSeparationMatch

/-!
# Separation axioms for morphisms of algebraic spaces

The relative diagonal of a morphism of algebraic spaces is representable, so it makes sense to
ask that it be a closed immersion, an immersion, or quasi-compact; this defines separated,
locally separated and quasi-separated morphisms of algebraic spaces, and for representable
morphisms these notions agree with the existing ones.

## Implementation notes

Representability of the diagonal is `AlgebraicGeometry.relativelyRepresentable_pullbackDiagonal`
(Tag 03HK, part (1)), the definitions are `AlgebraicGeometry.Space.IsSeparated`,
`AlgebraicGeometry.Space.IsLocallySeparated` and `AlgebraicGeometry.Space.IsQuasiSeparated`
(Tag 03HL), and the agreement is
`AlgebraicGeometry.Space.separationProperties_of_relativelyRepresentable` (Tag 03KY). The
section tag is registered on these declarations; the lemmas of the section are in
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms` and the modules it imports.

## References

* [Stacks Project, Tag 03HJ](https://stacks.math.columbia.edu/tag/03HJ)
-/

@[expose] public section

add_to_stacks 03HJ "the relative diagonal is representable"
  AlgebraicGeometry.relativelyRepresentable_pullbackDiagonal
add_to_stacks 03HJ "separated morphisms" AlgebraicGeometry.Space.IsSeparated
add_to_stacks 03HJ "locally separated morphisms" AlgebraicGeometry.Space.IsLocallySeparated
add_to_stacks 03HJ "quasi-separated morphisms" AlgebraicGeometry.Space.IsQuasiSeparated
add_to_stacks 03HJ "agreement with the notions for representable morphisms"
  AlgebraicGeometry.Space.separationProperties_of_relativelyRepresentable
