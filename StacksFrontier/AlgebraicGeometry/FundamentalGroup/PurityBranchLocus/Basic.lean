module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Spectrum.Prime.LTSeries
public import StacksCore.Tactic.StacksAttribute

/-!
# A height-one prime through an element

In a positive-dimensional Noetherian local ring, every element of the maximal ideal is
contained in a prime ideal of height one.

## Main results

* `IsLocalRing.exists_isPrime_height_eq_one_of_mem_maximalIdeal` gives a height-one prime
  containing a prescribed element of the maximal ideal.

## Implementation notes

The source states that the localization at the prime has dimension one. We state the equivalent
equality that the prime has height one; for a prime `p`,
`IsLocalization.AtPrime.ringKrullDim_eq_height` identifies this height with the Krull dimension
of `Localization.AtPrime p`.

## References

* [Stacks Project, Tag 0BJG](https://stacks.math.columbia.edu/tag/0BJG)
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- An element of the maximal ideal of a positive-dimensional Noetherian local ring is
contained in a prime ideal of height one. -/
@[stacks 0BJG]
public theorem exists_isPrime_height_eq_one_of_mem_maximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : 1 ≤ ringKrullDim A) (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A) :
    ∃ p : Ideal A, p.IsPrime ∧ f ∈ p ∧ p.height = 1 := by
  let m := IsLocalRing.maximalIdeal A
  obtain ⟨s, hs_last, hs_len⟩ := Ideal.exists_ltSeries_length_eq_height m
  have hlen : 1 ≤ s.length := by
    exact_mod_cast hs_len.symm ▸
      (WithBot.coe_le_coe.mp ((IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)) ▸ hdim) :
        (1 : ℕ∞) ≤ m.height)
  obtain ⟨t, hft, hlength, _hhead, ht_last⟩ :=
    PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last s (by simpa [hs_last, m] using hf)
  have ht_len : t.length = Order.height t.last := by
    rw [← PrimeSpectrum.height_eq_orderHeight, ← ht_last, hs_last]
    exact hlength.symm ▸ hs_len
  refine ⟨(t 1).asIdeal, (t 1).isPrime, hft, ?_⟩
  rw [PrimeSpectrum.height_eq_orderHeight]
  simpa [Nat.mod_eq_of_lt (by omega : 1 < t.length + 1)] using
    Order.height_eq_index_of_length_eq_height_last ht_len 1

end IsLocalRing
