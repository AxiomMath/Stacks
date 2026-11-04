module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Two identities in commutative rings for lifting powers across a nilpotent thickening

* If `x = y + ε` with `ε ^ N = 0` and `y = r * y'`, then for `q ≥ N + K` the power `x ^ q` is the
  sum over `i < N` of `binom(q, i) r^{q - i - K} y'^{q - i} (r^K ε^i)`, a combination of the
  elements `r^K ε^i` with coefficients divisible by `r`.
* If `a = r * a'`, `b = s * b'` and `r^k (a - b) = 0 = s^k (a - b)`, then `a ^ m = b ^ m` for
  `m ≥ 2k`.
* If `S` is the localization of `R` away from `f` and `δ ∈ S` is nilpotent, then for every large
  `q` the power `(f + δ)^q` is the image of an element of `f R`.

These are the two computations in the proof that some power of a section on a closed subscheme
defined by a nilpotent ideal lifts, in the proof of [Stacks, Tag 09MS].

## Main results

* `Stacks.NilpotentThickeningLift.pow_add_eq_sum`
* `Stacks.NilpotentThickeningLift.pow_eq_pow_of_mul_pow_sub_eq_zero`
* `Stacks.NilpotentThickeningLift.exists_algebraMap_mul_eq_pow_add`
-/

@[expose] public section

open Finset

namespace Stacks.NilpotentThickeningLift

variable {R : Type*} [CommRing R]

/-- **The binomial expansion truncated by a nilpotent summand.** If `ε ^ N = 0` and `y = r * y'`
then for `q ≥ N + K`,
`(y + ε) ^ q = ∑_{i < N} binom(q, i) • (r ^ (q - i - K) * y' ^ (q - i) * (r ^ K * ε ^ i))`. -/
theorem pow_add_eq_sum (y' r ε : R) (N K q : ℕ) (hε : ε ^ N = 0) (hq : N + K ≤ q) :
    (r * y' + ε) ^ q = ∑ i ∈ range N,
      (q.choose i : R) * (r ^ (q - i - K) * y' ^ (q - i) * (r ^ K * ε ^ i)) := by
  rw [add_comm, add_pow]
  have hNq : N ≤ q + 1 := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hNq]
  have hzero : ∑ i ∈ Ico N (q + 1), ε ^ i * (r * y') ^ (q - i) * (q.choose i : R) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : N ≤ i := (Finset.mem_Ico.mp hi).1
    rw [show ε ^ i = ε ^ N * ε ^ (i - N) by rw [← pow_add, Nat.add_sub_cancel' hi'], hε]
    ring
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < N := Finset.mem_range.mp hi
  have hsplit : r ^ (q - i) = r ^ (q - i - K) * r ^ K := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow, hsplit]
  ring

/-- **Powers of two elements that differ by an element killed by powers of their factors.** If
`a = r * a'`, `b = s * b'` and `r ^ k` and `s ^ k` both annihilate `a - b`, then `a ^ m = b ^ m`
for every `m ≥ 2 * k`. -/
theorem pow_eq_pow_of_mul_pow_sub_eq_zero (a' b' r s : R) (k m : ℕ)
    (hr : r ^ k * (r * a' - s * b') = 0) (hs : s ^ k * (r * a' - s * b') = 0) (hm : 2 * k ≤ m) :
    (r * a') ^ m = (s * b') ^ m := by
  rcases m with _ | m
  · simp
  rw [← sub_eq_zero, ← Commute.geom_sum₂_mul (Commute.all _ _), mul_comm,
    Finset.mul_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i < m + 1 := Finset.mem_range.mp hi
  rcases le_or_gt k i with hki | hki
  · obtain ⟨c, hc⟩ : r ^ k ∣ (r * a') ^ i :=
      (pow_dvd_pow r hki).trans (pow_dvd_pow_of_dvd (dvd_mul_right r a') i)
    rw [hc]
    rw [show (r * a' - s * b') * (r ^ k * c * (s * b') ^ (m + 1 - 1 - i)) =
      (r ^ k * (r * a' - s * b')) * (c * (s * b') ^ (m + 1 - 1 - i)) by ring, hr, zero_mul]
  · obtain ⟨c, hc⟩ : s ^ k ∣ (s * b') ^ (m + 1 - 1 - i) :=
      (pow_dvd_pow s (by omega)).trans (pow_dvd_pow_of_dvd (dvd_mul_right s b') _)
    rw [hc]
    rw [show (r * a' - s * b') * ((r * a') ^ i * (s ^ k * c)) =
      (s ^ k * (r * a' - s * b')) * ((r * a') ^ i * c) by ring, hs, zero_mul]

/-- **Powers of a nilpotent perturbation of `f` in the localization away from `f`.** Let `S` be the
localization of `R` away from `f` and let `δ ∈ S` be nilpotent. Then there is `q₀` such that for
every `q ≥ q₀` the power `(f + δ)^q` is the image of `f * h` for some `h ∈ R`. -/
theorem exists_algebraMap_mul_eq_pow_add {S : Type*} [CommRing S] [Algebra R S] (f : R)
    [IsLocalization.Away f S] (δ : S) (hδ : IsNilpotent δ) :
    ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∃ h : R, algebraMap R S (f * h) = (algebraMap R S f + δ) ^ q := by
  classical
  obtain ⟨N, hN⟩ := hδ
  choose k e he using fun i : ℕ => IsLocalization.Away.surj (S := S) f (δ ^ i)
  set K : ℕ := (range N).sup k with hK
  have hk : ∀ i ∈ range N, k i ≤ K := fun i hi => Finset.le_sup (f := k) hi
  set e' : ℕ → R := fun i => f ^ (K - k i) * e i with he'
  have he'_spec : ∀ i ∈ range N, algebraMap R S (e' i) = algebraMap R S f ^ K * δ ^ i := by
    intro i hi
    rw [he', map_mul, map_pow, ← he i, ← mul_assoc, mul_comm _ (δ ^ i), mul_assoc, ← pow_add,
      Nat.sub_add_cancel (hk i hi), mul_comm]
  refine ⟨N + K + 1, fun q hq => ?_⟩
  refine ⟨∑ i ∈ range N, (q.choose i : R) * (f ^ (q - i - K - 1) * e' i), ?_⟩
  have hexp := pow_add_eq_sum (1 : S) (algebraMap R S f) δ N K q hN (by omega)
  rw [mul_one] at hexp
  rw [hexp, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < N := Finset.mem_range.mp hi
  have hpow : f * f ^ (q - i - K - 1) = f ^ (q - i - K) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [one_pow, mul_one, show f * ((q.choose i : R) * (f ^ (q - i - K - 1) * e' i)) =
      (q.choose i : R) * ((f * f ^ (q - i - K - 1)) * e' i) by ring, hpow, map_mul, map_mul,
    map_natCast, map_pow, he'_spec i hi]

end Stacks.NilpotentThickeningLift
