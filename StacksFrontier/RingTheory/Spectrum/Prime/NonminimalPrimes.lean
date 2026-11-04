module

public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.Spectrum.Prime.Topology

import StacksCore.Tactic.StacksAttribute

/-!
# The nonminimal primes of a set of primes stable under specialization

For a subset `T` of the prime spectrum of a commutative ring, the *nonminimal primes* of `T`
are the primes of `T` that properly contain another prime of `T`; equivalently, those that are
not minimal in `T`. If `T` is stable under specialization then so is this subset, because a
specialization of a prime of `T` again lies in `T` and still properly contains whatever prime
of `T` the original one contained.

## Main definitions

* `PrimeSpectrum.nonminimalPrimes` — the primes of `T` that are not minimal in `T`.

## Main results

* `PrimeSpectrum.stableUnderSpecialization_nonminimalPrimes` — the nonminimal primes of a
  subset stable under specialization are again stable under specialization.
* `PrimeSpectrum.diff_nonminimalPrimes` — the complement of the nonminimal primes inside `T`
  is exactly the set of minimal primes of `T`.

## Implementation notes

Specialization on the prime spectrum is inclusion of primes, by
`PrimeSpectrum.le_iff_specializes`, so the whole statement is about the inclusion order and
needs no hypothesis on the ring. In particular the Noetherian hypothesis carried by the source
is not used here; it enters only the exact sequence that the source states alongside this
assertion.

## References

* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
-/

@[expose] public section

universe u

namespace PrimeSpectrum

variable {A : Type u} [CommRing A] {T : Set (PrimeSpectrum A)} {p : PrimeSpectrum A}

/-- The primes of `T` that are not minimal in `T`, that is, those properly containing some
other prime of `T`. -/
def nonminimalPrimes (T : Set (PrimeSpectrum A)) : Set (PrimeSpectrum A) :=
  {p | p ∈ T ∧ ∃ q ∈ T, q < p}

/-- A prime is nonminimal in `T` exactly when it lies in `T` and some prime of `T` is
properly contained in it. -/
theorem mem_nonminimalPrimes : p ∈ nonminimalPrimes T ↔ p ∈ T ∧ ∃ q ∈ T, q < p := Iff.rfl

/-- The nonminimal primes of `T` lie in `T`. -/
theorem nonminimalPrimes_subset (T : Set (PrimeSpectrum A)) : nonminimalPrimes T ⊆ T :=
  fun _ hp => hp.1

/-- The primes of `T` which are not nonminimal are precisely the minimal primes of `T`. -/
theorem diff_nonminimalPrimes (T : Set (PrimeSpectrum A)) :
    T \ nonminimalPrimes T = {p | Minimal (· ∈ T) p} := by
  ext p
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, mem_nonminimalPrimes]
  refine ⟨fun h => minimal_iff_forall_lt.mpr ⟨h.1, fun q hqp hqT => h.2 ⟨h.1, q, hqT, hqp⟩⟩,
    fun h => ⟨h.prop, fun hp => ?_⟩⟩
  obtain ⟨q, hqT, hqp⟩ := hp.2
  exact h.not_lt hqT hqp

/-- The nonminimal primes of a subset of the prime spectrum stable under specialization are
again stable under specialization. -/
@[stacks 0EF8 "T' is stable under specialization"]
theorem stableUnderSpecialization_nonminimalPrimes (hT : StableUnderSpecialization T) :
    StableUnderSpecialization (nonminimalPrimes T) := by
  intro p q hpq hp
  rw [mem_nonminimalPrimes] at hp ⊢
  obtain ⟨hpT, r, hrT, hrp⟩ := hp
  exact ⟨hT hpq hpT, r, hrT, hrp.trans_le ((le_iff_specializes p q).mpr hpq)⟩

end PrimeSpectrum
