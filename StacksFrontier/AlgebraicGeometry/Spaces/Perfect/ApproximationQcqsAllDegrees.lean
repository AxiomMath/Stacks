module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsPseudoCoherentFrom

/-!
# Approximation by perfect complexes on a qcqs algebraic space, without support condition

Stacks 08HP for the closed subset `T = |X|`: on a quasi-compact and quasi-separated algebraic
space `X` there is an integer `r` such that every `(m - r)`-pseudo-coherent `E` in `D_QCoh(𝒪_X)`
receives a map from a perfect object which is an isomorphism on `Hⁱ` for `i > m` and surjective
on `Hᵐ`. This is the base's `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_qcqs` at
`T = |X|`.

## Main results

* `AlgebraicGeometry.Space.exists_approximatesFrom_of_isPseudoCoherentFrom`.

## References

* [Stacks Project, Tag 08HP](https://stacks.math.columbia.edu/tag/08HP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.Space

end
