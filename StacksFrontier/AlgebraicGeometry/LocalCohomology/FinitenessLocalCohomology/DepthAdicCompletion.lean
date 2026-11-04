module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Support.DepthAdicCompletion
public import StacksCore.Tactic.StacksAttribute

/-!
# Depth does not decrease under adic completion

Let `A` be a Noetherian ring, `I` an ideal of `A`, and `M` a finite `A`-module. At a prime of the
`I`-adic completion lying over a prime of `A`, the depth of the completed module is at least the
depth of the original module.

## Main results

* `Module.depth_localized_adicCompletion_le`: depth does not decrease after completion and
  localization at corresponding primes.

The second display of the same tag, the invariance of depth plus dimension under completion, is
`Module.depth_add_ringKrullDim_quotient_localization_adicCompletion`.

## Implementation notes

The completed ring and module are Mathlib's canonical `AdicCompletion` constructions. Only the
prime at which depth is measured and its contraction enter, so the inequality holds without the
auxiliary larger primes or the dualizing-complex hypothesis that accompany the statement in the
Stacks Project.

## References

* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Module

/-- The depth of a finite module at a prime cannot decrease after adic completion and
localization at a prime above it. -/
@[stacks 0EHW "first display, the inequality `depth(M_𝔭) ≤ depth(M'_{𝔭'})`, without the \
dualizing complex and without the outer pair of primes"]
theorem depth_localized_adicCompletion_le
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : Ideal A) [p.IsPrime]
    (p' : Ideal (AdicCompletion I A)) [p'.IsPrime] [p'.LiesOver p] :
    Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) ≤
      Module.depth (Localization.AtPrime p') (maximalIdeal (Localization.AtPrime p'))
        (LocalizedModule p'.primeCompl (AdicCompletion I M)) := by
  rw [AlgebraicGeometry.depth_localized_adicCompletion I p p']
  exact le_add_of_nonneg_right bot_le

end Module
