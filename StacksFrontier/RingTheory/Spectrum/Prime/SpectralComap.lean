module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The map on prime spectra induced by a ring map is spectral

A quasi-compact open subset of a prime spectrum is the complement of the zero locus of a finite
set, so its inverse image under `PrimeSpectrum.comap f` is the complement of the zero locus of
the image of that finite set under `f`, hence again a quasi-compact open. Together with
continuity this says that `PrimeSpectrum.comap f` is a spectral map.

## Main results

* `PrimeSpectrum.isSpectralMap_comap`: `PrimeSpectrum.comap f` is a spectral map.
-/

@[expose] public section

namespace PrimeSpectrum

/-- The map on prime spectra induced by a ring map is spectral: it is continuous, and a
quasi-compact open is the complement of the zero locus of a finite set, whose inverse image is
the complement of the zero locus of the image of that set. -/
@[ega "I 1.2.3" "more general"]
theorem isSpectralMap_comap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    IsSpectralMap (PrimeSpectrum.comap f) := by
  classical
  refine ⟨PrimeSpectrum.continuous_comap f, fun U hUo hUc => ?_⟩
  obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨hUc, hUo⟩
  refine (PrimeSpectrum.isCompact_isOpen_iff.mpr ⟨t.image f, ?_⟩).1
  rw [← ht, Set.preimage_compl, PrimeSpectrum.preimage_comap_zeroLocus]
  simp

end PrimeSpectrum
