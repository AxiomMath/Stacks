module

public import Mathlib.RingTheory.Ideal.Height

/-!
# The dimension of a proper quotient of a local ring

A proper quotient `S ⧸ I` of a local ring is again local, with maximal ideal the image of `𝔪_S`,
so its Krull dimension is the height of that image.

## Main results

* `IsLocalRing.ringKrullDim_quotient_eq_height_map_maximalIdeal`: for a proper ideal `I` of a
  local ring `S`, the Krull dimension of `S ⧸ I` is the height of the image of `𝔪_S`.
-/

@[expose] public section

namespace IsLocalRing

/-- The Krull dimension of a proper quotient of a local ring is the height of the image of the
maximal ideal. -/
lemma ringKrullDim_quotient_eq_height_map_maximalIdeal {S : Type*} [CommRing S]
    [IsLocalRing S] {I : Ideal S} (h : I ≠ ⊤) :
    ringKrullDim (S ⧸ I) = ((maximalIdeal S).map (Ideal.Quotient.mk I)).height := by
  have : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr h
  have : IsLocalRing (S ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
    maximalIdeal_height_eq_ringKrullDim]

end IsLocalRing

end
