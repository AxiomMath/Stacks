module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute

/-! Stacks tag 00ES, part by part.

Part (1), `closure {p} = V(p)`, is Mathlib's `PrimeSpectrum.closure_singleton`; part (3), the
irreducible components of `Spec R` are exactly the `V(p)` with `p` minimal, is Mathlib's
`PrimeSpectrum.zeroLocus_minimalPrimes` (Mathlib also tags the order isomorphism
`minimalPrimes.equivIrreducibleComponents` with 00ES). Part (2) is stated on the ideal side in
Mathlib (`PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible`), so it is stated here on the side
of closed subsets, in both directions. -/

@[expose] public section

add_to_stacks 00ES "(1) the closure of {p} is V(p)" PrimeSpectrum.closure_singleton
add_to_stacks 00ES "(3) the irreducible components of Spec R are exactly the V(p), p minimal"
  PrimeSpectrum.zeroLocus_minimalPrimes

namespace PrimeSpectrum

variable {R : Type*} [CommSemiring R]

/-- A subset of `Spec R` is closed and irreducible if and only if it is `V(p)` for a prime
ideal `p` of `R`. -/
@[stacks 00ES "(2) the irreducible closed subsets of Spec R are exactly the V(p), p prime"]
theorem isClosed_and_isIrreducible_iff_exists_isPrime_eq_zeroLocus {s : Set (PrimeSpectrum R)} :
    IsClosed s ∧ IsIrreducible s ↔ ∃ p : Ideal R, p.IsPrime ∧ s = zeroLocus (p : Set R) := by
  constructor
  · rintro ⟨hc, hi⟩
    exact ⟨vanishingIdeal s, isIrreducible_iff_vanishingIdeal_isPrime.mp hi,
      by rw [zeroLocus_vanishingIdeal_eq_closure, hc.closure_eq]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨isClosed_zeroLocus _, (isIrreducible_zeroLocus_iff_of_radical _ hp.isRadical).mpr hp⟩

end PrimeSpectrum
