module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.TFAE

@[expose] public section

/-!
# Dense image of the map on spectra

For a ring map `f : R →+* S`, this file proves Stacks 00FL: the following are equivalent.

1. Every element of the kernel of `f` is nilpotent.
2. Every minimal prime of `R` is in the image of `Spec S → Spec R`.
3. The image of `Spec S → Spec R` is dense in `Spec R`.

The equivalences (2) ⇔ (3) and (1) ⇔ (3) are Mathlib's
`PrimeSpectrum.denseRange_comap_iff_minimalPrimes` and
`PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`.

## Main results

* `PrimeSpectrum.tfae_isNilpotent_ker_minimalPrimes_denseRange_comap`: the three conditions of
  Stacks 00FL are equivalent.
-/

namespace PrimeSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- For a ring map `f : R →+* S` the following are equivalent: every element of the kernel of `f`
is nilpotent; every minimal prime of `R` is in the image of `comap f : Spec S → Spec R`; the image
of `comap f` is dense in `Spec R`. -/
@[stacks 00FL "The three conditions of the lemma, in the order (1), (2), (3)."]
theorem tfae_isNilpotent_ker_minimalPrimes_denseRange_comap :
    List.TFAE [∀ x ∈ RingHom.ker f, IsNilpotent x,
      ∀ I (h : I ∈ minimalPrimes R), ⟨I, h.1.1⟩ ∈ Set.range (comap f),
      DenseRange (comap f)] := by
  tfae_have 1 ↔ 3 := by
    rw [denseRange_comap_iff_ker_le_nilRadical]
    exact ⟨fun h x hx ↦ mem_nilradical.mpr (h x hx), fun h x hx ↦ mem_nilradical.mp (h hx)⟩
  tfae_have 2 ↔ 3 := (denseRange_comap_iff_minimalPrimes f).symm
  tfae_finish

end PrimeSpectrum
