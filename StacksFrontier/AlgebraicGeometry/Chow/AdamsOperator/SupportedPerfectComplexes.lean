module

public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Perfect complexes supported on a closed subscheme

For a closed subscheme `Z` of a scheme `X`, the supported perfect derived category is the full
subcategory of the derived category of `X` consisting of perfect objects whose every
cohomology sheaf is supported on the underlying closed subset of `Z`. It is the category whose
K-group the Adams operators act on.

## Main definitions

* `AlgebraicGeometry.supportedPerfectDerivedCategory` is this full subcategory.

## Implementation notes

The definition already given for Tag 0FDN has exactly the object condition required here:
perfectness and support of every cohomology sheaf on the closed subscheme. We register that
definition directly rather than duplicating the full subcategory. As with that definition,
local Noetherianness is not needed to form the category; later results impose it where needed.

## References

* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
-/

add_to_stacks 0FEP "supported_perfect_complexes" AlgebraicGeometry.supportedPerfectDerivedCategory
