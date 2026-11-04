module

public import StacksFrontier.RingTheory.Module.AdicSystem.Hom.SystemLimits
public import StacksFrontier.RingTheory.Module.AdicSystem.Hom.MittagLeffler

/-!
# Homomorphisms and isomorphisms between the adic reductions of finite modules

Let `I` be an ideal of a Noetherian ring `A` and let `M`, `N` be finite `A`-modules.  Write
`Mₙ = M ⧸ I ^ n M` and `Nₙ = N ⧸ I ^ n N`.  This file compares the inverse systems
`n ↦ Hom_{Aₙ}(Mₙ, Nₙ)` and `n ↦ Isom_{Aₙ}(Mₙ, Nₙ)` with the adic quotients of
`Hom_A(M, N)`.  Both systems are Mittag-Leffler, the comparison has uniformly bounded
kernel and cokernel, and in the limit one recovers the homomorphisms — respectively the
isomorphisms — between the `I`-adic completions of `M` and `N` over the completion of `A`.

## Main results

* `Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion`:
  the `Hom` and `Isom`
  systems of the adic reductions are Mittag-Leffler, the canonical map from
  `Hom_A(M, N) ⧸ I ^ n Hom_A(M, N)` to `Hom_{Aₙ}(Mₙ, Nₙ)` has kernel and cokernel annihilated
  by a single power of `I`, and the inverse limits compute the homomorphisms and the
  isomorphisms between the completions.
* `Stacks.AdicSystem.HomComparison.completedHomEquiv`: for finite modules over a Noetherian
  ring, the completion of `Hom_A(M, N)` is the module of homomorphisms between the completions
  of `M` and `N` over the completion of `A`.
* `Stacks.AdicSystem.HomComparison.completedHomEquiv_of_apply`: that identification sends the
  completion of `f` to the map extending `f`, which characterises it.
* `Stacks.AdicSystem.CompletionIsomorphism.adicCompletion_linearEquiv_of_quotient_linearEquiv`:
  if `Mₙ ≃ₗ Nₙ` for every
  `n`, then the `I`-adic completions of `M` and `N` are isomorphic over the completed ring.
  This is the isomorphism-detection consequence of 09BB: the `Isom` system is nonempty at
  every level and Mittag-Leffler, hence has a point in the limit.

## Implementation notes

Inverse systems are functors on `ℕᵒᵖ`; `Hom` systems are formed in `ModuleCat A` so that
`Functor.IsMittagLeffler` and the limit are available.  Adic completions are Mathlib's
`AdicCompletion`.

## References

* [Stacks Project, Tag 09BB](https://stacks.math.columbia.edu/tag/09BB)
* [Stacks Project, Tag 09BC](https://stacks.math.columbia.edu/tag/09BC)
-/
