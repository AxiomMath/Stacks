module

public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.MittagLefflerCohomology.StableImagesACC
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.MittagLefflerCohomology.PowerCohomologyACC


/-!
# Mittag-Leffler cohomology from graded ascending chain conditions

Let `I` be an ideal in a commutative ring and let an inverse system of sheaves
of modules have transitions given by quotienting by the corresponding powers
of `I`. If the graded module formed from the stable images in degree `p + 1`
satisfies the ascending chain condition, its degree-`p` cohomology system is
Mittag-Leffler. The same conclusion holds under the stronger hypothesis that
the whole graded module `⨁ₙ Hᵖ⁺¹(X, Iⁿ𝓕ₙ₊₁)` satisfies the ascending chain
condition, because the stable images form a graded submodule of it.

## Main results

All of the following live in the namespace `Stacks.Cohomology.MittagLefflerCohomology`.

* `isMittagLeffler_cohomology_of_stableImagesGradedACC` gives the Mittag-Leffler
  criterion from ACC for the stable images.
* `cohomology_transitionImage_stable_uniformly` gives the uniform stabilization
  asserted in the source's footnote.
* `isMittagLeffler_cohomology_of_powerCohomologyGradedACC` and
  `cohomology_transitionImage_stable_uniformly_of_powerCohomologyGradedACC` are the
  same two statements under ACC for the whole graded module.
* `stableImagesHaveGradedACC_of_powerCohomologyGradedACC` passes from the second
  hypothesis to the first.

## Implementation notes

The system is indexed from zero: its term `n` represents the source's
`𝓕ₙ₊₁`. `IsQuotientTower` identifies each actual transition with
the canonical quotient map by the ideal-power subsheaf. The degree-`n` stable
image is `stableImage I F (p + 1) n`, including the intersection over
all later terms. `StableImagesHaveGradedACC` states ACC for their
direct sum under the canonical action of the associated graded ring, and
`PowerCohomologyHaveGradedACC` states it for the direct sum of the ambient
cohomology modules under the action specified the same way. The
footnote's uniform lag is written with source term `Fₙ₊₁` at index `n`, so
the image from index `i + c` to `i` is stable for every `i`.

For a nonnegatively graded module, the ascending chain condition on graded
submodules is equivalent to the Noetherian condition, so both predicates
record the latter.

## References

* [Stacks Project, Tag 0GYK](https://stacks.math.columbia.edu/tag/0GYK)
* [Stacks Project, Tag 0GYL](https://stacks.math.columbia.edu/tag/0GYL)
-/
