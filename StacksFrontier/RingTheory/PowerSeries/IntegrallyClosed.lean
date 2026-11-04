module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Tactic.Linarith
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Normality of the power series ring over a Noetherian normal domain

Let `R` be a Noetherian normal domain, that is, a Noetherian domain which is integrally closed in
its fraction field `K`. This file proves that the formal power series ring `R⟦X⟧` is again
integrally closed in its fraction field; together with `PowerSeries.instIsNoetherianRing` and
`PowerSeries.instIsDomain` this says that `R⟦X⟧` is a Noetherian normal domain.

The argument is the source's, phrased through almost integrality. An element of the fraction field
of `R⟦X⟧` which is integral over `R⟦X⟧` is almost integral, so it is a fraction `s / h` with
`h ^ n ∣ s ^ (n + 1)` in `R⟦X⟧` for every `n`, and it lies in `R⟦X⟧` as soon as `h ∣ s`. That is
the only thing to prove, and over any domain it is the whole of integral closedness.

Comparing orders, `ord h ≤ ord s`, so over `K` the series `h` divides `s`, because `K⟦X⟧` is a
discrete valuation ring: there is `V ∈ K⟦X⟧` with `h V = s`, and dividing the relation
`h ^ n ∣ s ^ (n + 1)` by `h ^ n` shows that `h V ^ n` is a power series over `R` for every `n`. It
remains to see that the coefficients of `V` themselves lie in `R`.

That is where normality of `R` enters, in the form of the source's reduction to the leading
coefficient: after cancelling `X ^ ord h` the denominator `h` has nonzero constant coefficient `b`,
and the constant coefficient `a` of `V` then satisfies `b a ^ n ∈ R` for all `n`, so `a` is almost
integral over `R`, hence integral over `R` because `R` is Noetherian, hence in `R` because `R` is
normal. Subtracting `a` and dividing by `X` leaves the hypothesis on `V` intact, so induction peels
off one coefficient at a time: after `N` steps `V` is a power series over `R` plus `X ^ N` times
another series, which pins the coefficients of `V` below `N`.

## Main results

* `PowerSeries.instIsIntegrallyClosed`: Stacks 0BI0.

## Implementation notes

Almost integrality is Mathlib's `IsAlmostIntegral`; the source's Lemma 00GX is Mathlib's
`IsIntegral.isAlmostIntegral` and `IsAlmostIntegral.isIntegral`, and both directions are used, the
first over `R⟦X⟧` and the second over `R`. Over `R⟦X⟧` it is used only in the direction that holds
over any domain, so the normality half of the tag never needs the ascending chain condition on
`R⟦X⟧` and nothing here depends on the source's Lemma 0306; the Noetherian half of the tag is
`PowerSeries.instIsNoetherianRing`.

Through Mathlib's `PowerSeries.algebraPowerSeries`, `IsAlmostIntegral R⟦X⟧ V` for `V ∈ K⟦X⟧`
unfolds to the existence of a non-zero-divisor `h ∈ R⟦X⟧` with `map (algebraMap R K) h * V ^ n` in
the range of `PowerSeries.map (algebraMap R K)` for every `n`. The helpers state this hypothesis
explicitly, for a fixed `h`, because the peeling induction needs a fixed denominator with nonzero
constant coefficient. The two facts the argument needs are stability under subtracting an element
of the subring and cancellation of a common power of `X`.

The source's conclusion also includes Noetherianity and the domain property of `R⟦X⟧`, already
given by Mathlib's `PowerSeries.instIsNoetherianRing` and `PowerSeries.instIsDomain`. The
hypotheses `IsNoetherianRing R` and `IsIntegrallyClosed R` are used only to turn an almost integral
coefficient of the fraction field into an element of `R`; the argument also works for a completely
normal domain without the ascending chain condition.

The source works inside the field of Laurent series `K((X)) = K⟦X⟧[1/X]`, using that it is a field
to write `w = aₙ X ^ n + …` with `n ∈ ℤ`, and reads the sign condition `n ≥ 0` off the
almost-integrality relation. Here that step is the inequality `ord h ≤ ord s` of
`order_le_order_of_forall_pow_dvd_pow_succ` together with `dvd_iff_order_le`, the same computation
with the same content, which keeps the whole proof inside power series rings.

## References

* [Stacks 0BI0](https://stacks.math.columbia.edu/tag/0BI0), Lemma 10.37.9. Definition 00GW of an
  almost integral element, Lemma 00GX, and Lemma 0306 (see the implementation notes).
-/

@[expose] public section

namespace PowerSeries

section AlmostIntegral

variable {S : Type*} [CommRing S]

/-- Almost integrality with a fixed denominator is stable under translation by the subring: if
`b * V ^ n ∈ A` for every `n` and `q ∈ A`, then `b * (V - q) ^ n ∈ A` for every `n`. This is the
part of Lemma 00GX saying that almost integral elements form a ring. -/
private lemma mul_sub_pow_mem {A : Subring S} {b V : S} (H : ∀ n, b * V ^ n ∈ A) {q : S}
    (hq : q ∈ A) (n : ℕ) : b * (V - q) ^ n ∈ A := by
  rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
  refine sum_mem fun k _ => ?_
  rw [show b * (V ^ k * (-q) ^ (n - k) * n.choose k)
      = b * V ^ k * ((-q) ^ (n - k) * n.choose k) from by ring]
  exact mul_mem (H k) (mul_mem (pow_mem (neg_mem hq) _) (natCast_mem _ _))

end AlmostIntegral

section Range

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- The constant coefficient of a power series pushed forward along `f`. -/
private lemma constantCoeff_map (p : R⟦X⟧) : constantCoeff (map f p) = f (constantCoeff p) := rfl

/-- A power series over `S` comes from one over `R` exactly when each of its coefficients does. -/
private lemma mem_map_range_iff (V : S⟦X⟧) : V ∈ (map f).range ↔ ∀ i, coeff i V ∈ f.range := by
  constructor
  · rintro ⟨p, rfl⟩ i
    exact ⟨coeff i p, (coeff_map f i p).symm⟩
  · intro hV
    choose g hg using hV
    exact ⟨PowerSeries.mk g, by ext i; simp [coeff_map, hg i]⟩

/-- Multiplication by `X ^ k` only shifts coefficients, so it does not affect coming from `R`. -/
private lemma mem_map_range_of_X_pow_mul_mem (k : ℕ) {V : S⟦X⟧} (h : X ^ k * V ∈ (map f).range) :
    V ∈ (map f).range := by
  rw [mem_map_range_iff] at h ⊢
  intro i
  simpa using h (i + k)

/-- Cancelling a power of `X` from the denominator and from the series at the same time. Both
cancellations the peeling induction needs are this lemma: `k = 0` makes the denominator one of
nonzero constant coefficient, and `j = 0`, `k = 1` divides the series by `X`. -/
private lemma mul_pow_mem_map_range_of_X_pow_mul_mem {h : R⟦X⟧} {V : S⟦X⟧} {j k n : ℕ}
    (H : map f (X ^ j * h) * (X ^ k * V) ^ n ∈ (map f).range) :
    map f h * V ^ n ∈ (map f).range := by
  refine mem_map_range_of_X_pow_mul_mem f (j + k * n) ?_
  rw [show (X : S⟦X⟧) ^ (j + k * n) * (map f h * V ^ n) = map f (X ^ j * h) * (X ^ k * V) ^ n from
    by simp only [map_mul, map_pow, PowerSeries.map_X, mul_pow, pow_add, pow_mul]; ring]
  exact H

end Range

section Normal

variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- The source's reduction to the leading coefficient: if the denominator `h` has nonzero constant
coefficient `b`, then the constant coefficient `a` of `W` satisfies `b * a ^ n ∈ R` for every `n`,
so it is almost integral over `R`, hence integral, hence in `R`. -/
private lemma constantCoeff_mem_range_of_forall_mul_pow_mem {h : R⟦X⟧} (hb : constantCoeff h ≠ 0)
    {W : K⟦X⟧} (H : ∀ n, map (algebraMap R K) h * W ^ n ∈ (map (algebraMap R K)).range) :
    constantCoeff W ∈ (algebraMap R K).range := by
  have hai : IsAlmostIntegral R (constantCoeff W) := by
    refine ⟨constantCoeff h, mem_nonZeroDivisors_of_ne_zero hb, fun n => ?_⟩
    obtain ⟨p, hp⟩ := H n
    exact ⟨constantCoeff p, by
      simpa [Algebra.smul_def, constantCoeff_map] using congrArg constantCoeff hp⟩
  exact RingHom.mem_range.mpr
    (IsIntegrallyClosed.isIntegral_iff.mp (isAlmostIntegral_iff_isIntegral.mp hai))

/-- Peeling off coefficients one at a time: after `N` steps, `V` is a power series over `R` plus
`X ^ N` times a series satisfying the same hypothesis. -/
private lemma exists_eq_map_add_X_pow_mul {h : R⟦X⟧} (hb : constantCoeff h ≠ 0) {V : K⟦X⟧}
    (H : ∀ n, map (algebraMap R K) h * V ^ n ∈ (map (algebraMap R K)).range) (N : ℕ) :
    ∃ (p : R⟦X⟧) (W : K⟦X⟧), V = map (algebraMap R K) p + X ^ N * W ∧
      ∀ n, map (algebraMap R K) h * W ^ n ∈ (map (algebraMap R K)).range := by
  induction N with
  | zero => exact ⟨0, V, by simp, H⟩
  | succ N ih =>
    obtain ⟨p, W, hV, hW⟩ := ih
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp (constantCoeff_mem_range_of_forall_mul_pow_mem hb hW)
    obtain ⟨W', hW'⟩ : X ∣ W - map (algebraMap R K) (C a) := by
      rw [X_dvd_iff]; simp [ha]
    have hWeq : W = map (algebraMap R K) (C a) + X * W' := by rw [← hW']; ring
    refine ⟨p + C a * X ^ N, W', ?_, fun n => ?_⟩
    · rw [hV, hWeq]
      simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
      ring
    · refine mul_pow_mem_map_range_of_X_pow_mul_mem (algebraMap R K) (j := 0) (k := 1) ?_
      have hsub := mul_sub_pow_mem hW ⟨C a, rfl⟩ n
      rw [hW'] at hsub
      simpa using hsub

/-- A power series over the fraction field `K` of a Noetherian normal domain `R` which is almost
integral over `R⟦X⟧` with a nonzero denominator `h` is a power series over `R`. This is the content
of Stacks 0BI0: it is the only step that uses normality of `R`. -/
private lemma mem_map_range_of_forall_mul_pow_mem {h : R⟦X⟧} (hh : h ≠ 0) {V : K⟦X⟧}
    (H : ∀ n, map (algebraMap R K) h * V ^ n ∈ (map (algebraMap R K)).range) :
    V ∈ (map (algebraMap R K)).range := by
  obtain ⟨m, h₀, rfl, hb⟩ : ∃ (m : ℕ) (h₀ : R⟦X⟧), h = X ^ m * h₀ ∧ constantCoeff h₀ ≠ 0 :=
    ⟨h.order.toNat, h.divXPowOrder, X_pow_order_mul_divXPowOrder.symm,
      by rw [constantCoeff_divXPowOrder]; exact coeff_order hh⟩
  have H' : ∀ n, map (algebraMap R K) h₀ * V ^ n ∈ (map (algebraMap R K)).range := fun n =>
    mul_pow_mem_map_range_of_X_pow_mul_mem (algebraMap R K) (k := 0) (by simpa using H n)
  rw [mem_map_range_iff]
  intro i
  obtain ⟨p, W, hV, -⟩ := exists_eq_map_add_X_pow_mul hb H' (i + 1)
  rw [hV]
  simp [coeff_map, coeff_X_pow_mul']

end Normal

section Order

variable {R : Type*} [Semiring R]

/-- The order of a divisor is at most the order of the multiple. -/
private lemma order_le_order_of_dvd {h s : R⟦X⟧} (H : h ∣ s) : h.order ≤ s.order := by
  obtain ⟨c, rfl⟩ := H
  exact le_trans le_self_add (order_mul_ge h c)

end Order

section OrderDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The order comparison replacing the source's appeal to the field of Laurent series: if
`h ^ n ∣ s ^ (n + 1)` for every `n` then `ord h ≤ ord s`, since `n * ord h ≤ (n + 1) * ord s` for
every `n` and `ord s` is finite. -/
private lemma order_le_order_of_forall_pow_dvd_pow_succ {h s : R⟦X⟧} (hs : s ≠ 0)
    (H : ∀ n : ℕ, h ^ n ∣ s ^ (n + 1)) : h.order ≤ s.order := by
  have hh : h ≠ 0 := by
    rintro rfl
    exact hs ((pow_eq_zero_iff two_ne_zero).mp (zero_dvd_iff.mp (by simpa using H 1)))
  have fin : ∀ p : R⟦X⟧, p ≠ 0 → ∃ m : ℕ, p.order = m := fun p hp =>
    ⟨p.order.toNat, (ENat.natCast_toNat (order_eq_top.not.mpr hp)).symm⟩
  obtain ⟨m, hm⟩ := fin h hh
  obtain ⟨m', hm'⟩ := fin s hs
  have key : ∀ n : ℕ, n * m ≤ (n + 1) * m' := by
    intro n
    have h1 := order_le_order_of_dvd (H n)
    rw [order_pow, order_pow, hm, hm', nsmul_eq_mul, nsmul_eq_mul] at h1
    exact_mod_cast h1
  rw [hm, hm', Nat.cast_le]
  nlinarith [key (m' + 1)]

end OrderDomain

section Field

variable {K : Type*} [Field K]

/-- Over a field, `K⟦X⟧` is a discrete valuation ring with valuation the order, so a nonzero power
series divides another exactly when its order is no larger. -/
private lemma dvd_iff_order_le {h s : K⟦X⟧} (hh : h ≠ 0) : h ∣ s ↔ h.order ≤ s.order := by
  refine ⟨order_le_order_of_dvd, fun hle => ?_⟩
  rcases eq_or_ne s 0 with rfl | hs
  · exact dvd_zero h
  obtain ⟨u, hu⟩ := isUnit_divided_by_X_pow_order hh
  have hX : h ∣ X ^ h.order.toNat :=
    ⟨↑u⁻¹, (Units.eq_mul_inv_iff_mul_eq u).mpr (by rw [hu]; exact X_pow_order_mul_divXPowOrder)⟩
  exact hX.trans (X_pow_dvd_iff.mpr fun i hi => coeff_of_lt_order_toNat i
    (hi.trans_le (ENat.toNat_le_toNat hle (order_eq_top.not.mpr hs))))

end Field

section Criterion

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Dividing the almost-integrality relation by `h ^ n`: if `φ h * V = φ s` in a domain and
`h ^ n ∣ s ^ (n + 1)`, then `φ h * V ^ (n + 1)` is the image of the cofactor. -/
private lemma mul_pow_succ_mem_range_of_pow_dvd_pow_succ [IsDomain B] (φ : A →+* B) {h s : A}
    (hφ : φ h ≠ 0) {V : B} (hV : φ s = φ h * V) {n : ℕ} (H : h ^ n ∣ s ^ (n + 1)) :
    φ h * V ^ (n + 1) ∈ φ.range := by
  obtain ⟨c, hc⟩ := H
  refine ⟨c, (mul_left_cancel₀ (pow_ne_zero n hφ) ?_).symm⟩
  rw [show φ h ^ n * (φ h * V ^ (n + 1)) = (φ h * V) ^ (n + 1) from by ring, ← hV, ← map_pow, hc,
    map_mul, map_pow]

/-- A domain in which `h ^ n ∣ s ^ (n + 1)` for every `n` forces `h ∣ s` is integrally closed: an
integral element of the fraction field is almost integral, and almost integrality of a fraction
`s / h` is exactly that chain of divisibilities. -/
private lemma isIntegrallyClosed_of_forall_pow_dvd_pow_succ [IsDomain A]
    (H : ∀ h s : A, h ≠ 0 → (∀ n : ℕ, h ^ n ∣ s ^ (n + 1)) → h ∣ s) : IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro w hw
  have hinj : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective A _
  obtain ⟨h, hh0, hpow⟩ := hw.isAlmostIntegral
  have hh : h ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hh0
  have hφh : algebraMap A (FractionRing A) h ≠ 0 := (map_ne_zero_iff _ hinj).2 hh
  choose num hnum using hpow
  have key : ∀ n, algebraMap A (FractionRing A) (num n)
      = algebraMap A (FractionRing A) h * w ^ n := fun n => by rw [hnum n, Algebra.smul_def]
  obtain ⟨v, hv⟩ : h ∣ num 1 := by
    refine H h (num 1) hh fun n => ⟨num (n + 1), hinj ?_⟩
    rw [map_mul, map_pow, map_pow, key 1, key (n + 1), pow_one]
    ring
  exact ⟨v, mul_left_cancel₀ hφh (by rw [← map_mul, ← hv, key 1, pow_one])⟩

end Criterion

section

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- Over a Noetherian normal domain `R`, an element `s` of `R⟦X⟧` with `h ^ n ∣ s ^ (n + 1)` for
every `n` is divisible by `h`: the fraction `s / h`, being almost integral over `R⟦X⟧`, already
lies in `R⟦X⟧`. -/
private lemma dvd_of_forall_pow_dvd_pow_succ {h s : R⟦X⟧} (hh : h ≠ 0)
    (H : ∀ n : ℕ, h ^ n ∣ s ^ (n + 1)) : h ∣ s := by
  rcases eq_or_ne s 0 with rfl | hs
  · exact dvd_zero h
  have hinj : Function.Injective (map (algebraMap R (FractionRing R))) :=
    map_injective _ (IsFractionRing.injective R (FractionRing R))
  have hne : ∀ {p : R⟦X⟧}, p ≠ 0 → map (algebraMap R (FractionRing R)) p ≠ 0 :=
    (map_ne_zero_iff _ hinj).2
  obtain ⟨V, hV⟩ : map (algebraMap R (FractionRing R)) h ∣ map (algebraMap R (FractionRing R)) s :=
    (dvd_iff_order_le (hne hh)).mpr <| order_le_order_of_forall_pow_dvd_pow_succ (hne hs)
      fun n => by simpa only [← map_pow] using map_dvd (map (algebraMap R (FractionRing R))) (H n)
  obtain ⟨v, hv⟩ := mem_map_range_of_forall_mul_pow_mem hh (V := V) fun n => by
    cases n with
    | zero => simp
    | succ n => exact mul_pow_succ_mem_range_of_pow_dvd_pow_succ _ (hne hh) hV (H n)
  exact ⟨v, hinj (by rw [map_mul, hv, ← hV])⟩

end

/-- The formal power series ring `R⟦X⟧` over a Noetherian normal domain `R` is a normal domain:
it is integrally closed in its fraction field. Together with `PowerSeries.instIsNoetherianRing`
and `PowerSeries.instIsDomain` this says that `R⟦X⟧` is a Noetherian normal domain. -/
@[stacks 0BI0, ega "IV 21.13.9" "(iv)"]
public instance instIsIntegrallyClosed {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] : IsIntegrallyClosed R⟦X⟧ :=
  isIntegrallyClosed_of_forall_pow_dvd_pow_succ fun _ _ hh H => dvd_of_forall_pow_dvd_pow_succ hh H

end PowerSeries
