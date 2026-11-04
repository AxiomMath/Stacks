module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpace

/-!
# Categories fibred in groupoids representable by algebraic spaces

A category fibred in groupoids over the big fppf site of `S` is representable by an algebraic
space when it is equivalent over the site to the category associated with an algebraic space. A
representable category fibred in groupoids is representable by an algebraic space; the
representable ones are characterized as the categories fibred in setoids whose presheaf of
isomorphism classes is an algebraic space; and `1`-morphisms between two of them, up to
`2`-isomorphism, are the morphisms of the representing algebraic spaces.

## Implementation notes

The definition is `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace` (Tag 04SV), the
passage from schemes to algebraic spaces is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isRepresentableCFG`, the
characterization is `AlgebraicGeometry.isRepresentableByAlgebraicSpace_iff` (Tag 02ZX), and the
description of morphisms is `AlgebraicGeometry.Stack.morphismSpaceEquiv` together with
`AlgebraicGeometry.Stack.existsUnique_twoIso_of_morphismSpaceEquiv_eq` (Tag 04SW). The section
tag is registered on these declarations.

## References

* [Stacks Project, Tag 02ZV](https://stacks.math.columbia.edu/tag/02ZV)
-/

@[expose] public section

add_to_stacks 02ZV "representable by an algebraic space"
  AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace
add_to_stacks 02ZV "a representable category fibred in groupoids is representable by an
  algebraic space" AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isRepresentableCFG
add_to_stacks 02ZV "characterization by setoid fibres"
  AlgebraicGeometry.isRepresentableByAlgebraicSpace_iff
add_to_stacks 02ZV "1-morphisms up to 2-isomorphism are morphisms of algebraic spaces"
  AlgebraicGeometry.Stack.morphismSpaceEquiv
add_to_stacks 02ZV "uniqueness of the 1-morphism up to unique 2-isomorphism"
  AlgebraicGeometry.Stack.existsUnique_twoIso_of_morphismSpaceEquiv_eq
