module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OneDimensionalFibres

/-!
# Tag 0E7H: vanishing above degree one for a proper morphism with one-dimensional fibres

[Stacks, Tag 0E7H] fixes a proper morphism `f : X ⟶ Y` with `dim(X_y) ≤ 1` and
`H¹(X_y, 𝒪_{X_y}) = 0` for every `y ∈ Y`, and a quasi-coherent `ℱ` on `X`, and asserts

1. `Rᵖ f_* ℱ = 0` for `p > 1`,
2. `R¹ f_* ℱ = 0` if there is a surjection `f^*𝒢 ⟶ ℱ` with `𝒢` quasi-coherent on `Y`,

and, when `Y` is affine,

3. `Hᵖ(X, ℱ) = 0` for `p ∉ {0, 1}`,
4. `H¹(X, ℱ) = 0` if `ℱ` is globally generated.

**No declaration of this tag remains in this file.** Clauses (1) and (3) are proved without
any hypothesis beyond the tag's own, from [Stacks, Tag 0E7D] at `d = 1`, in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/FibreDimensionOneCohomologyVanishing.lean`, as
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_higherDirectImage_of_one_lt_of_isProper` and
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_cohomology_of_notMem_zero_one_of_isAffine`;
the versions that stood here, which carried the residue of [Stacks, Tag 02V7] at fibre dimension
one as a hypothesis, were superseded by them and removed.

## References

* [Stacks Project, Tag 0E7H](https://stacks.math.columbia.edu/tag/0E7H)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard

noncomputable section

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
