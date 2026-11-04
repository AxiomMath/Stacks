module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksCore.Tactic.StacksAttribute

/-!
# Equal powers from equality at the minimal primes

In a Noetherian local ring of dimension at most one, two elements whose images agree in every
localization at a minimal prime differ by a nilpotent element. If one of them lies in the
maximal ideal, then the maximal ideal is contained in the radical of the annihilator of that
difference, so a power of the element kills it and the two elements have equal positive powers.

## Main results

* `IsLocalRing.exists_pow_eq_pow_of_eq_at_minimalPrimes` gives the common power.

## Implementation notes

Equality in the product of localizations is expressed componentwise, using the canonical maps
to `Localization.AtPrime`. The exponent is required to be positive. The maximal-ideal
hypothesis on the first element is redundant: equality in all minimal-prime localizations
already implies that the difference is nilpotent. The argument also applies in dimension zero.

## References

* [Stacks Project, Tag 0AB2](https://stacks.math.columbia.edu/tag/0AB2)
-/

@[expose] public section

namespace IsLocalRing

private lemma pow_add_eq_pow_of_mul_eq_zero
    {A : Type*} [CommRing A] (a x : A) {n k : ℕ}
    (hx : x ^ k = 0) (hax : a ^ n * x = 0) :
    (a + x) ^ (n + k) = a ^ (n + k) := by
  rw [add_comm a x, (Commute.all x a).add_pow, Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    simp only [Finset.mem_range] at hi
    by_cases hik : i < k
    · have he : a ^ (n + k - i) = a ^ n * a ^ (n + k - i - n) := by
        rw [← pow_add]
        congr 1
        omega
      have hxa : x * a ^ (n + k - i) = 0 := by rw [he, ← mul_assoc, mul_comm x, hax, zero_mul]
      have hterm : x ^ i * a ^ (n + k - i) = 0 := by
        have hpow : x ^ i = x * x ^ (i - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hpow, mul_right_comm, hxa, zero_mul]
      simp [hterm]
    · have hxi : x ^ i = 0 := pow_eq_zero_of_le (by omega) hx
      simp [hxi]
  · simp

private lemma maximalIdeal_le_radical_of_avoids_minimalPrimes
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A ≤ 1) (I : Ideal A)
    (havoid : ∀ p : minimalPrimes A, ¬ I ≤ p.1) :
    IsLocalRing.maximalIdeal A ≤ I.radical := by
  classical
  have hmax : (IsLocalRing.maximalIdeal A).height ≤ 1 := by
    exact_mod_cast (show ((IsLocalRing.maximalIdeal A).height : WithBot ℕ∞) ≤ 1 by
      simpa only [IsLocalRing.maximalIdeal_height_eq_ringKrullDim] using hdim)
  rw [Ideal.radical_eq_sInf]
  intro r hr
  rw [Ideal.mem_sInf]
  intro (p : Ideal A) hp
  have : p.IsPrime := hp.2
  have hpmin : p ∉ minimalPrimes A := fun h => havoid ⟨p, h⟩ hp.1
  have hpheight : 1 ≤ p.height :=
    Order.one_le_iff_ne_zero.mpr (fun h => hpmin (Ideal.height_eq_zero_iff.mp h))
  have hple : p ≤ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal this.ne_top
  have hpeq : p = IsLocalRing.maximalIdeal A := by
    by_contra hne
    have htwo : (2 : ℕ∞) ≤ (IsLocalRing.maximalIdeal A).height :=
      (show (2 : ℕ∞) ≤ p.height + 1 by
        simpa only [one_add_one_eq_two, add_comm] using add_le_add_right hpheight 1).trans
        (Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hple hne))
    exact (not_lt_of_ge hmax) (lt_of_lt_of_le (by norm_num) htwo)
  rwa [hpeq]

/-- Two elements of a Noetherian local ring of dimension at most one which
agree at every minimal prime have equal positive powers if one lies in the
maximal ideal. -/
@[stacks 0AB2]
public theorem exists_pow_eq_pow_of_eq_at_minimalPrimes
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A ≤ 1) (a₁ a₂ : A)
    (ha₂ : a₂ ∈ IsLocalRing.maximalIdeal A)
    (heq : ∀ p : minimalPrimes A,
      (algebraMap A (@Localization.AtPrime A _ p.1 p.2.isPrime)) a₁ =
        (algebraMap A (@Localization.AtPrime A _ p.1 p.2.isPrime)) a₂) :
    ∃ n : ℕ, 0 < n ∧ a₁ ^ n = a₂ ^ n := by
  classical
  let x : A := a₁ - a₂
  have hxloc (p : minimalPrimes A) :
      algebraMap A (@Localization.AtPrime A _ p.1 p.2.isPrime) x = 0 := by
    dsimp [x]
    rw [map_sub, sub_eq_zero]
    exact heq p
  have hden (p : minimalPrimes A) :
      ∃ s : A, s ∉ p.1 ∧ s * x = 0 := by
    have : p.1.IsPrime := p.2.isPrime
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.1.primeCompl
      (Localization.AtPrime p.1) x).mp (hxloc p)
    exact ⟨s, Ideal.mem_primeCompl_iff.mp s.2, hs⟩
  have hxmin (p : minimalPrimes A) : x ∈ p.1 := by
    obtain ⟨s, hsnot, hs⟩ := hden p
    have hmul : s * x ∈ p.1 := hs ▸ p.1.zero_mem
    exact (p.2.isPrime.mul_mem_iff_mem_or_mem.mp hmul).resolve_left hsnot
  have hxnil : IsNilpotent x := by
    refine nilpotent_iff_mem_prime.2 fun q hq => ?_
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal A) ≤ q)
    exact hpq (hxmin ⟨p, hp⟩)
  let I : Ideal A := (A ∙ x).annihilator
  have havoid (p : minimalPrimes A) : ¬ I ≤ p.1 := fun hIp => by
    obtain ⟨s, hsnot, hs⟩ := hden p
    exact hsnot (hIp ((Submodule.mem_annihilator_span_singleton x s).2
      (by simpa [smul_eq_mul] using hs)))
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (maximalIdeal_le_radical_of_avoids_minimalPrimes hdim I havoid) (IsNoetherian.noetherian _)
  have ha2x : a₂ ^ n * x = 0 := by
    simpa [smul_eq_mul] using
      (Submodule.mem_annihilator_span_singleton x (a₂ ^ n)).1 (hn (Ideal.pow_mem_pow ha₂ n))
  obtain ⟨k₀, hk₀⟩ := hxnil
  refine ⟨n + (k₀ + 1), by omega, ?_⟩
  rw [show a₁ = a₂ + x from (add_sub_cancel a₂ a₁).symm]
  exact pow_add_eq_pow_of_mul_eq_zero a₂ x (pow_eq_zero_of_le k₀.le_succ hk₀) ha2x

end IsLocalRing
