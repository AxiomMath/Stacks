module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Strict dimension drop at a non-maximal prime

For a local ring `A` of finite Krull dimension and a prime `p` of `A` other than the maximal
ideal, localizing at `p` strictly lowers the Krull dimension: `dim A_p < dim A`.

This is the elementary input to arguments that induct on the dimension of a local ring by passing
to the local rings at the non-closed points of its spectrum.  It is the inequality
`ht p < ht 𝔪` of `Ideal.height_strict_mono_of_isPrime_of_isPrime`, read through
`IsLocalization.AtPrime.ringKrullDim_eq_height` on the left and
`IsLocalRing.maximalIdeal_height_eq_ringKrullDim` on the right.

## Main results

* `IsLocalRing.ringKrullDim_lt_of_isLocalization_atPrime` — for an arbitrary localization of `A`
  at `p`.
* `IsLocalRing.ringKrullDim_localization_atPrime_lt` — the same for `Localization.AtPrime p`.

## Implementation notes

The finiteness hypothesis is `FiniteRingKrullDim A` rather than `IsNoetherianRing A`: it is what
the proof uses, and it is weaker.  It cannot be dropped — for a local ring of infinite dimension
both sides of the inequality can be `⊤`.  A Noetherian local ring satisfies it automatically, by
the Mathlib instance derived from Krull's height theorem, so a consumer in the Noetherian setting
need not supply it.
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- In a local ring of finite Krull dimension the maximal ideal has finite height, since its
height *is* the Krull dimension. -/
theorem finiteHeight_maximalIdeal (A : Type u) [CommRing A] [IsLocalRing A]
    [FiniteRingKrullDim A] : (maximalIdeal A).FiniteHeight := by
  refine ⟨Or.inr fun h => ringKrullDim_ne_top (R := A) ?_⟩
  rw [← maximalIdeal_height_eq_ringKrullDim, h]
  simp

/-- **Strict dimension drop at a non-maximal prime.**  If `A` is a local ring of finite Krull
dimension and `p` is a prime of `A` other than the maximal ideal, then any localization of `A` at
`p` has strictly smaller Krull dimension than `A`. -/
theorem ringKrullDim_lt_of_isLocalization_atPrime {A : Type u} [CommRing A] [IsLocalRing A]
    [FiniteRingKrullDim A] (p : Ideal A) [p.IsPrime] (hp : p ≠ maximalIdeal A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.AtPrime B p] :
    ringKrullDim B < ringKrullDim A := by
  have := finiteHeight_maximalIdeal A
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p B, ← maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast Ideal.height_strict_mono_of_isPrime_of_isPrime
    (lt_of_le_of_ne (le_maximalIdeal_of_isPrime p) hp)

/-- **Strict dimension drop at a non-maximal prime**, for `Localization.AtPrime`. -/
theorem ringKrullDim_localization_atPrime_lt {A : Type u} [CommRing A] [IsLocalRing A]
    [FiniteRingKrullDim A] (p : Ideal A) [p.IsPrime] (hp : p ≠ maximalIdeal A) :
    ringKrullDim (Localization.AtPrime p) < ringKrullDim A :=
  ringKrullDim_lt_of_isLocalization_atPrime p hp _

end IsLocalRing

end
