module

public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.EtaleLocalizationReductionExists

/-!
# Weakly associated primes of a flat tensor product over a finitely presented algebra

This file proves [Stacks, Tag 05IG].  Let `R → S` be a ring map of finite presentation, let `N` be
a finitely presented `S`-module which is flat over `R`, let `M` be an arbitrary `R`-module and let
`𝔮` be a prime of `S` lying over a prime `𝔭` of `R`.  Then

`𝔮 ∈ WeakAss_S(N ⊗_R M) ↔ (𝔭 ∈ WeakAss_R(M) and 𝔮-bar ∈ Ass_{S-bar}(N-bar))`,

where `S-bar = S ⊗_R κ(𝔭)` is the fibre ring, `N-bar = S-bar ⊗_S N` the fibre module and `𝔮-bar`
the prime of the fibre ring contracting to `𝔮`.  The statement is
`Stacks.WeaklyAssociatedPrimes.TensorFibreFormula05IG`, written out in
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFiniteType`.  The reductions that
weaken its finiteness hypotheses —
`isWeaklyAssociatedPrime_tensorProduct_iff_of_finitePresentation'`,
`isWeaklyAssociatedPrime_tensorProduct_iff_of_finite'`,
`isWeaklyAssociatedPrime_tensorProduct_iff_of_finiteType'` and the fibrewise description of
[Stacks, Tag 05II] — are downstream of this file, in
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFormulaFiniteType` and
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreFormulaEssentiallyFiniteType`,
because the proof below runs through the comparisons those reductions are taken against.

The proof is the source's.  `Stacks.WeaklyAssociatedPrimes.nonempty_reduction` performs the
reduction — invert an element of `S` outside `𝔮` chosen so that no prime weakly associated to the
fibre module survives outside `𝔮`, apply the étale-local structure theorem [Stacks, Tag 05ID] to
make the module projective over the base, and localize the base at the resulting prime — and
`Stacks.WeaklyAssociatedPrimes.Reduction.isWeaklyAssociatedPrime_tensorProduct_iff` deduces the tag
from the reduced situation.  The fibre condition is read over `S` through
`isWeaklyAssociatedPrime_tensorResidueField_iff`, the fibre ring being Noetherian.

## Main results

* `Stacks.WeaklyAssociatedPrimes.tensorFibreFormula05IG`: [Stacks, Tag 05IG].

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.WeaklyAssociatedPrimes

/-- **[Stacks, Tag 05IG].**  Let `R → S` be a ring map of finite presentation, let `N` be a
finitely presented `S`-module which is flat as an `R`-module, let `M` be an `R`-module and let `𝔮`
be a prime of `S` lying over a prime `𝔭` of `R`.  Then `𝔮` is weakly associated to `N ⊗_R M` if and
only if `𝔭` is weakly associated to `M` and some prime of the fibre ring `S ⊗_R κ(𝔭)` associated —
in the strict sense of [Stacks, Tag 00LA] — to the fibre module contracts to `𝔮`.

Both directions are proved, and no hypothesis beyond the tag's own is used. -/
@[stacks 05IG]
theorem tensorFibreFormula05IG : TensorFibreFormula05IG.{u} := by
  intro R S _ _ _ _ M _ _ N _ _ _ _ _ _ p _ q _ _
  have : IsNoetherianRing (S ⊗[R] p.ResidueField) := isNoetherianRing_tensorResidueField p
  rw [← isWeaklyAssociatedPrime_tensorResidueField_iff p q]
  obtain ⟨D⟩ := nonempty_reduction R S N p q
  exact D.isWeaklyAssociatedPrime_tensorProduct_iff M

end Stacks.WeaklyAssociatedPrimes

end
