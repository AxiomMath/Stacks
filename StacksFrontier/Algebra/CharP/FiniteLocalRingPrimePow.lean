module

public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.LocalRing
public import Mathlib.Algebra.IsPrimePow

/-!
# A finite local ring is killed by a power of a prime dividing its order

The characteristic of a finite local ring `Λ` is a prime power `ℓ ^ a`, so `ℓ ^ a = 0` in `Λ`,
and `ℓ` divides the order of `Λ`.

## Main results

* `IsLocalRing.exists_prime_dvd_card_pow_natCast_eq_zero`: a finite local ring is killed by a
  power of a prime dividing its order.
-/

@[expose] public section

namespace IsLocalRing

/-- **A finite local ring is killed by a power of a prime dividing its order.** -/
theorem exists_prime_dvd_card_pow_natCast_eq_zero (Λ : Type*) [CommRing Λ] [Finite Λ]
    [IsLocalRing Λ] : ∃ ℓ a : ℕ, ℓ.Prime ∧ ℓ ∣ Nat.card Λ ∧ (ℓ : Λ) ^ a = 0 := by
  classical
  have hq : ringChar Λ ≠ 0 := CharP.char_ne_zero_of_finite Λ (ringChar Λ)
  rcases charP_zero_or_prime_power Λ (ringChar Λ) with h | h
  · exact absurd h hq
  obtain ⟨ℓ, a, hℓ, ha, hla⟩ := (isPrimePow_nat_iff _).1 h
  have : Fact ℓ.Prime := ⟨hℓ⟩
  let := Fintype.ofFinite Λ
  refine ⟨ℓ, a, hℓ, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card, ← hla]
    exact dvd_pow_self ℓ ha.ne'
  · rw [← Nat.cast_pow, hla, ringChar.Nat.cast_ringChar]

end IsLocalRing
