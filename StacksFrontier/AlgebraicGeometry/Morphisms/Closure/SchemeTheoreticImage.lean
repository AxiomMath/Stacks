module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The scheme-theoretic image

Every morphism of schemes factors through a smallest closed subscheme of its codomain, its
scheme-theoretic image.

This file records the parts of Stacks 01R6 against the declarations that already state them.
Mathlib constructs the image from the largest ideal sheaf contained in the kernel of the map on
structure sheaves: `AlgebraicGeometry.Scheme.Hom.image` is the closed subscheme,
`AlgebraicGeometry.Scheme.Hom.imageι` its closed inclusion,
`AlgebraicGeometry.Scheme.Hom.toImage` the factoring map and
`AlgebraicGeometry.Scheme.Hom.toImage_imageι` the factorization itself. Minimality is the
remaining content: if a morphism factors through a closed immersion then
`AlgebraicGeometry.Scheme.Hom.le_ker_comp` gives the required inclusion of kernel ideal sheaves,
`AlgebraicGeometry.IsClosedImmersion.lift` produces the map from the scheme-theoretic image to
that closed subscheme, and `AlgebraicGeometry.IsClosedImmersion.lift_fac` identifies its
composite with the inclusion.

## Main definitions

There are no definitions in this file; it only attaches the tag to the existing ones.

## Main results

There are no results in this file.

## References

* [Stacks Project, Tag 01R6](https://stacks.math.columbia.edu/tag/01R6)
-/

@[expose] public section

namespace AlgebraicGeometry

add_to_stacks 01R6 "scheme-theoretic image" AlgebraicGeometry.Scheme.Hom.image
add_to_stacks 01R6 "closed inclusion" AlgebraicGeometry.Scheme.Hom.imageι
add_to_ega "I 9.5.1" AlgebraicGeometry.Scheme.Hom.imageι
add_to_ega "I 9.5.2" AlgebraicGeometry.Scheme.Hom.imageι
add_to_ega "I 9.5.3" AlgebraicGeometry.Scheme.Hom.imageι
add_to_ega "IV 2.3.2" AlgebraicGeometry.Scheme.Hom.imageι
add_to_stacks 01R6 "factorization map" AlgebraicGeometry.Scheme.Hom.toImage
add_to_ega "I 9.5.1" AlgebraicGeometry.Scheme.Hom.toImage
add_to_ega "I 9.5.2" AlgebraicGeometry.Scheme.Hom.toImage
add_to_ega "I 9.5.3" AlgebraicGeometry.Scheme.Hom.toImage
add_to_ega "IV 2.3.2" AlgebraicGeometry.Scheme.Hom.toImage
add_to_stacks 01R6 "factorization" AlgebraicGeometry.Scheme.Hom.toImage_imageι
add_to_ega "I 9.5.1" "factorization clause" AlgebraicGeometry.Scheme.Hom.toImage_imageι
add_to_ega "IV 2.3.2" AlgebraicGeometry.Scheme.Hom.toImage_imageι
add_to_stacks 01R6 "minimality of the kernel" AlgebraicGeometry.Scheme.Hom.le_ker_comp
add_to_stacks 01R6 "minimality map" AlgebraicGeometry.IsClosedImmersion.lift
add_to_stacks 01R6 "minimality map commutes" AlgebraicGeometry.IsClosedImmersion.lift_fac

end AlgebraicGeometry

end
