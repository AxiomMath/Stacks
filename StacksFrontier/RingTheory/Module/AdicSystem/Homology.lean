module

public import StacksFrontier.RingTheory.Module.AdicSystem.Homology.ProIso
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology.QuotientComparison
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology.IdealPowerComparison

/-!
# Artin--Rees comparison for the homology of an adic complex

Let `I` be an ideal of a Noetherian ring `A` and let `K → L → M` be a three-term complex of
finite `A`-modules, so that the composite `K → M` is zero.  Write `H` for the homology of the
complex in the middle.  This file compares `H` with the homology of the two reduced complexes
obtained by applying `- ⧸ I ^ n -` and `I ^ n • -` termwise, and shows in both cases that the
comparison is an isomorphism of pro-objects with a *uniform* Artin--Rees bound: one shift
`n ↦ n - c`, independent of `n`, inverts the comparison at every level.

## Main results

* `Stacks.AdicSystem.ArtinReesHomology.exists_uniform_adic_homology_comparison`: the homology of
  the complex reduced
  modulo `I ^ n` is pro-isomorphic to `H ⧸ I ^ n H`.  The single positive shift `c` also
  controls the ranges of the transition maps, the comparison on ideal multiples, and the
  annihilators of the kernels and cokernels of all comparison maps; the system is
  Mittag-Leffler and its limit is the `I`-adic completion of `H`.
* `Stacks.AdicSystem.Homology.homologyIdealPowers_proIsomorphic`: the homology of the complex of `I
  ^ n`
  multiples is pro-isomorphic to the system of submodules `I ^ n H` of `H`, again with a
  uniform shift.

## Implementation notes

No new definitions are introduced.  The homology modules are written using the concrete
quotient model of the source: `H` is `ker β ⧸ (range α ⊓ ker β)`, its level-`n` analogue is
`β⁻¹(I ^ n M) ⧸ (range α + I ^ n L)` for tag 0EGU and
`(ker β ⊓ I ^ n L) ⧸ α(I ^ n K)` for tag 0G3K.  Inverse systems are functors on `ℕᵒᵖ` and
pro-isomorphism uses the explicit up-to-refinement formulation `InverseSequence.ProIso`; for
0G3K the refinement is displayed directly by the maps `forward`/`backward` on the cofinal
shift `n ↦ n + c`.

## References

* [Stacks Project, Tag 0EGU](https://stacks.math.columbia.edu/tag/0EGU)
* [Stacks Project, Tag 0G3K](https://stacks.math.columbia.edu/tag/0G3K)
-/
