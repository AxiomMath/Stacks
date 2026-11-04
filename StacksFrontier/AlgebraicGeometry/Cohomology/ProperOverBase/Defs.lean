module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset

/-!
# Closed subsets proper over a base

Let `f : X ⟶ S` be a morphism of schemes locally of finite type. A closed subset `Z` of `X` is
*proper over `S`* when the closed subscheme it carries is proper over `S`. This condition does
not depend on which closed subscheme structure on `Z` is used, and it is inherited by smaller
closed subsets.

That development lives in
`StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubset`: it defines
`AlgebraicGeometry.IsProperOver`, compares the closed subscheme structures on `Z` through
`AlgebraicGeometry.isProperOver_iff_exists_isProper` and
`AlgebraicGeometry.exists_isProper_iff_forall_isProper`, and proves
`AlgebraicGeometry.isProperOver_of_le`. This module re-exports it for the cohomology files of
this directory, which are stated in terms of `AlgebraicGeometry.IsProperOver`.

## References

* [Stacks Project, Tag 0CYL](https://stacks.math.columbia.edu/tag/0CYL)
* [Stacks Project, Tag 0CYM](https://stacks.math.columbia.edu/tag/0CYM)
* [Stacks Project, Tag 0CYN](https://stacks.math.columbia.edu/tag/0CYN)
-/
