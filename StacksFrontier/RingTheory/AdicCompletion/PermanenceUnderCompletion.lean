module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# The completion of a Noetherian local ring

For a Noetherian local ring `(A, 𝔪)`, the `𝔪`-adic completion `A^∧` is a Noetherian local ring,
complete with respect to its maximal ideal `𝔪^∧ = 𝔪 A^∧`, and `A → A^∧` is faithfully flat.
These are the standing facts of the source's section on permanence of properties under
completion.

## Main results

* `AdicCompletion.noetherian_completeLocal_faithfullyFlat`: the four assertions above.

## References

* [Stacks Project, Tag 07NU](https://stacks.math.columbia.edu/tag/07NU)
-/

@[expose] public section

open IsLocalRing

namespace AdicCompletion

/-- The completion of a Noetherian local ring `(A, 𝔪)` is a Noetherian local ring with maximal
ideal `𝔪 A^∧`, complete with respect to it, and faithfully flat over `A`. -/
@[stacks 07NU "the completion of a Noetherian local ring"]
theorem noetherian_completeLocal_faithfullyFlat (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    IsNoetherianRing (AdicCompletion (maximalIdeal A) A) ∧
      IsLocalRing (AdicCompletion (maximalIdeal A) A) ∧
      maximalIdeal (AdicCompletion (maximalIdeal A) A) =
        (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) ∧
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal A) A))
        (AdicCompletion (maximalIdeal A) A) ∧
      Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
  ⟨AdicCompletion.isNoetherianRing _, inferInstance, maximalIdeal_eq_map, inferInstance,
    faithfullyFlat_of_le_ringJacobson _ (ringJacobson_eq_maximalIdeal (R := A)).ge⟩

end AdicCompletion
