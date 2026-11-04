module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksCore.Tactic.StacksAttribute

/-!
# Powers in the image of the minimal-prime localizations

Let `A` be a one-dimensional Noetherian local ring. Its localization away from a parameter is
the product of its localizations at the minimal primes, so an element of that product differing
from the image of an element of the maximal ideal by an element of the extended nilradical is,
up to a nilpotent, the image of a ring element. Since the nilpotent part is killed by a power
and the parameter divides a power of the maximal-ideal element, a positive power of the given
element comes from `A`.

## Main results

* `IsLocalRing.exists_pow_mem_range_of_sub_mem_nilradical_map` gives a positive power in the
  image of the canonical map to the product of minimal-prime localizations.

## Implementation notes

The intersection of the minimal primes is `sInf (minimalPrimes A)`, and its extension to the
product is expressed by `Ideal.map`. The product is indexed by the minimal points of
`PrimeSpectrum A`, so each localization uses the prime ideal supplied by its index. The binomial
expansion is carried out in the localization away from the parameter and transported along the
algebra equivalence with the product.

## References

* [Stacks Project, Tag 0AB3](https://stacks.math.columbia.edu/tag/0AB3)
-/

@[expose] public section

namespace IsLocalRing

universe u

private lemma mul_le_mul_succ_sub_of_lt {q m k t : ℕ} (hk : k < t) :
    q * (m * k) ≤ t * (q * m + 1) - k := by
  have hprod := Nat.mul_le_mul_left (q * m) hk.le
  have hnk : q * m * k ≤ t * (q * m + 1) - k := by
    rw [Nat.mul_add, Nat.mul_comm t (q * m)]
    omega
  simpa [Nat.mul_assoc] using hnk

/-- In a Noetherian ring, every element of the extension of the intersection of the minimal
primes has a positive power equal to zero. -/
private lemma exists_pow_eq_zero_of_mem_map_sInf_minimalPrimes {A S : Type*} [CommRing A]
    [IsNoetherianRing A] [CommRing S] (φ : A →+* S) {y : S}
    (hy : y ∈ (sInf (minimalPrimes A)).map φ) : ∃ t, 0 < t ∧ y ^ t = 0 := by
  obtain ⟨t₀, ht₀⟩ := IsNoetherianRing.isNilpotent_nilradical A
  have hIt : sInf (minimalPrimes A) ^ (t₀ + 1) = ⊥ := by
    rw [← nilradical_eq_sInf_minimalPrimes, pow_succ, ht₀]
    simp
  have hmem := Ideal.pow_mem_pow hy (t₀ + 1)
  rw [← Ideal.map_pow, hIt, Ideal.map_bot, Ideal.mem_bot] at hmem
  exact ⟨t₀ + 1, t₀.succ_pos, hmem⟩

private lemma exists_pow_add_mem_range_away
    (A : Type u) [CommRing A] (g a : A)
    (ha : ∃ q > 0, a ^ q ∈ Ideal.span {g})
    (y : Localization.Away g) (t : ℕ) (ht : 0 < t) (hy : y ^ t = 0) :
    ∃ n : ℕ, 0 < n ∧
      (algebraMap A (Localization.Away g) a + y) ^ n ∈
        Set.range (algebraMap A (Localization.Away g)) := by
  classical
  let S := Localization.Away g
  let φ : A →+* S := algebraMap A S
  obtain ⟨q, hq, hqa⟩ := ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hqa
  obtain ⟨b, s, hs⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers g) y
  obtain ⟨m, hsm⟩ := s.2
  let d := q * m
  let n := t * (d + 1)
  have hden : φ (g ^ m) * y = φ b := by
    rw [show φ (g ^ m) = φ ↑s from congrArg φ hsm, ← hs]
    exact IsLocalization.mk'_spec' S b s
  have hdenPow (k : ℕ) : φ (g ^ (m * k)) * y ^ k = φ (b ^ k) := by
    calc
      φ (g ^ (m * k)) * y ^ k = (φ (g ^ m) * y) ^ k := by
        rw [map_pow, pow_mul, ← map_pow, ← mul_pow]
      _ = φ (b ^ k) := by rw [hden, map_pow]
  have hsumTerm (k : ℕ) :
      y ^ k * φ a ^ (n - k) * (n.choose k : S) ∈ φ.range := by
    by_cases hk : k < t
    · have hle : q * (m * k) ≤ n - k := mul_le_mul_succ_sub_of_lt hk
      let r := n - k - q * (m * k)
      have hr : q * (m * k) + r = n - k := by
        dsimp [r]
        omega
      have hterm : y ^ k * φ a ^ (n - k) =
          φ (b ^ k * c ^ (m * k) * a ^ r) := by
        calc
          y ^ k * φ a ^ (n - k) = y ^ k * φ (a ^ (q * (m * k)) * a ^ r) := by
            rw [← map_pow, ← hr, pow_add]
          _ = y ^ k * φ (g ^ (m * k) * c ^ (m * k) * a ^ r) := by
            rw [pow_mul, hc, mul_pow]
          _ = φ (b ^ k * c ^ (m * k) * a ^ r) := by
            simp only [map_mul]
            have hdenPow' := hdenPow k
            rw [Nat.mul_comm m k] at hdenPow'
            rw [← hdenPow']
            ac_rfl
      rw [hterm]
      refine ⟨b ^ k * c ^ (m * k) * a ^ r * n.choose k, ?_⟩
      simp [φ]
    · simp [pow_eq_zero_of_le (Nat.le_of_not_gt hk) hy]
  refine ⟨n, Nat.mul_pos ht (by omega), ?_⟩
  rw [add_comm (φ a) y, add_pow]
  exact φ.range.sum_mem fun k _ => hsumTerm k

/-- **Stacks 0AB3.** An element of the product of the minimal-prime localizations that is
congruent, modulo the extended nilradical, to an element of the maximal ideal has a positive
power in the image of the original ring. -/
@[stacks 0AB3]
public theorem exists_pow_mem_range_of_sub_mem_nilradical_map
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) :
    let L := ∀ p : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A},
      Localization.AtPrime p.1.asIdeal
    let I : Ideal A := sInf (minimalPrimes A)
      ∀ (f : L) (a : A), a ∈ IsLocalRing.maximalIdeal A →
      f - algebraMap A L a ∈ I.map (algebraMap A L) →
        ∃ n : ℕ, 0 < n ∧ f ^ n ∈ Set.range (algebraMap A L) := by
  classical
  intro L I f a ha hfa
  let Q := {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}
  obtain ⟨g, hg, hrad⟩ := IsLocalRing.exists_radical_span_eq_maximalIdeal (A := A) hdim
  let S := Localization.Away g
  obtain ⟨e₀⟩ :=
    (IsLocalRing.notMem_minimalPrimes_iff_localizationAway_equiv_pi_localizationAtPrime
      hdim hg).mp
      ((IsLocalRing.radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes hdim hg).mp hrad)
  let idx : minimalPrimes A ≃ Q :=
    { toFun := fun p => ⟨⟨p.1, p.2.isPrime⟩, by simp⟩
      invFun := fun p => ⟨p.1.asIdeal, p.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  let e : S ≃ₐ[A] L :=
    e₀.trans (AlgEquiv.piCongrLeft A (fun p : Q => Localization.AtPrime p.1.asIdeal) idx)
  let φS : A →+* S := algebraMap A S
  let y := e.symm f - φS a
  have hdelta : f - algebraMap A L a ∈ (I.map φS).map e.toAlgHom.toRingHom := by
    rwa [Ideal.map_map, show e.toAlgHom.toRingHom.comp φS = algebraMap A L by
      ext z p
      exact congrFun (e.commutes z) p]
  obtain ⟨z, hz, hzeq⟩ :=
    (Ideal.mem_map_iff_of_surjective e.toAlgHom.toRingHom e.surjective).mp hdelta
  have hy : y ∈ I.map φS := by
    have hzy : z = y := e.injective (by
      calc
        e z = f - algebraMap A L a := hzeq
        _ = e (e.symm f - φS a) := by
          rw [map_sub, e.apply_symm_apply, e.commutes])
    exact hzy ▸ hz
  obtain ⟨t, ht, hy0⟩ := exists_pow_eq_zero_of_mem_map_sInf_minimalPrimes φS hy
  obtain ⟨q₀, hqa₀⟩ := Ideal.mem_radical_iff.mp (hrad.symm ▸ ha)
  have hqa : a ^ (q₀ + 1) ∈ Ideal.span {g} := by
    rw [pow_succ']
    exact Ideal.mul_mem_left _ a hqa₀
  obtain ⟨n, hn, hpow⟩ :=
    exists_pow_add_mem_range_away A g a ⟨q₀ + 1, q₀.succ_pos, hqa⟩ y t ht hy0
  obtain ⟨b, hb⟩ : e.symm f ^ n ∈ Set.range φS := by
    rwa [← add_sub_cancel (φS a) (e.symm f)]
  exact ⟨n, hn, b, (e.commutes b).symm.trans ((congrArg e hb).trans (by simp))⟩

end IsLocalRing
