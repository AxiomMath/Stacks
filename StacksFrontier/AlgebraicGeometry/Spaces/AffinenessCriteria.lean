module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingTensorStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSurjectiveAffineSource
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomological criteria for an algebraic space to be affine

This file collects the criteria of Stacks, Cohomology of Algebraic Spaces, Sections 69.16 and
69.17 for an algebraic space to be an affine scheme.

* Stacks 07V6: a quasi-compact and quasi-separated algebraic space is affine if and only if the
  higher cohomology of its quasi-coherent modules vanishes,
  `AlgebraicGeometry.Space.isAffineSpace_iff_forall_isZero_rightDerived`; more precisely, every
  algebraic space as in Situation 07UY is an affine scheme,
  `AlgebraicGeometry.Space.CohomologyVanishingSituation.isAffineSpace`.
* Stacks 0D2V: a Noetherian algebraic space whose coherent modules have vanishing first
  cohomology is affine,
  `AlgebraicGeometry.Space.isAffineSpace_of_forall_isCoherent_isZero_rightDerived_one`.
* Stacks 07VP: a Noetherian algebraic space admitting a finite surjective morphism from an affine
  scheme is affine, `AlgebraicGeometry.Space.isAffineSpace_of_isFinite_of_isSurjective`.

## Main results

* `AlgebraicGeometry.Space.CohomologyVanishingSituation.isAffineSpace`: an algebraic space as in
  Situation 07UY is an affine scheme (Stacks 07V6).

## Implementation notes

In Situation 07UY the cohomology hypothesis is that of the situation itself, at
`CohomologyVanishingSituation.{u, u}`, as for Stacks 07V1, 07V4 and 07V5.

## References

* [Stacks Project, Tag 07V6](https://stacks.math.columbia.edu/tag/07V6)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 0D2V](https://stacks.math.columbia.edu/tag/0D2V)
* [Stacks Project, Tag 07VP](https://stacks.math.columbia.edu/tag/07VP)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Space

add_to_stacks 07V6 "first sentence: a quasi-compact and quasi-separated algebraic space is \
affine iff the higher cohomology of its quasi-coherent modules vanishes"
  AlgebraicGeometry.Space.isAffineSpace_iff_forall_isZero_rightDerived

add_to_stacks 0D2V
  AlgebraicGeometry.Space.isAffineSpace_of_forall_isCoherent_isZero_rightDerived_one

add_to_stacks 07VP AlgebraicGeometry.Space.isAffineSpace_of_isFinite_of_isSurjective

namespace CohomologyVanishingSituation

/-- **Stacks 07V6, more precisely.** An algebraic space in the situation of Stacks 07UY is an
affine scheme: it is represented by an object of the site over the base whose underlying scheme
is affine. -/
@[stacks 07V6 "more precisely: an algebraic space as in Situation 07UY is an affine scheme"]
theorem isAffineSpace (T : CohomologyVanishingSituation.{u, u}) :
    IsAffineSpace T.site T.base T.containsBase T.space.1 :=
  isAffineSpace_of_surjective_sectionsMap T.site T.base T.containsBase T.containsTerminal
    (fun _ _ g hg hM hN => T.surjective_sectionsMap_of_epi_of_isQuasicoherentOnSite g hg hM hN)
    T.quasiCompact T.quasiSeparated

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end
