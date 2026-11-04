module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Lucas

/-!
# Hasse derivatives of `p^e`-th powers in characteristic `p`

Over a commutative ring of characteristic `p`, the Hasse derivatives `D⁽ⁱ⁾` of order
`0 < i < p^e` kill every `p^e`-th power, so `D⁽ⁱ⁾` is linear over `p^e`-th powers in that range:
`D⁽ⁱ⁾ (g^(p^e) * h) = g^(p^e) * D⁽ⁱ⁾ h`. Together with the Taylor criterion for vanishing to
order `m` these are the basic tools of Stepanov's method for counting points of curves over
finite fields.

## Main results

* `Polynomial.cast_choose_pow_mul_eq_zero`: `(p^e * m).choose a = 0` in characteristic `p`
  for `0 < a < p^e` (Lucas).
* `Polynomial.hasseDeriv_pow_char_pow`: `D⁽ⁱ⁾ (g^(p^e)) = 0` for `0 < i < p^e`.
* `Polynomial.hasseDeriv_pow_char_pow_mul`: `D⁽ⁱ⁾ (g^(p^e) * h) = g^(p^e) * D⁽ⁱ⁾ h` for
  `i < p^e`.
* `Polynomial.X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero`: if `D⁽ⁱ⁾ f (a) = 0` for all `i < m`
  then `(X - a)^m ∣ f`.
-/

@[expose] public section

open Polynomial


namespace Polynomial

/-- In characteristic `p`, the binomial coefficient `(p^e * m).choose a` vanishes for
`0 < a < p^e`. -/
theorem cast_choose_pow_mul_eq_zero {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    [CharP R p] : ∀ (e m a : ℕ), 0 < a → a < p ^ e → ((p ^ e * m).choose a : R) = 0 := by
  intro e
  induction e with
  | zero => intro m a h0 h1; simp at h1; omega
  | succ e ih =>
    intro m a h0 h1
    have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (k := a)
      (n := p * (p ^ e * m))
    rw [pow_succ', mul_assoc, (CharP.natCast_eq_natCast R p).mpr hmod, Nat.mul_mod_right]
    rcases Nat.eq_zero_or_pos (a % p) with ha | ha
    · rw [Nat.mul_div_cancel_left _ hp.out.pos, Nat.cast_mul, ih m (a / p) ?_ ?_, mul_zero]
      · exact Nat.div_pos (Nat.le_of_dvd h0 (Nat.dvd_of_mod_eq_zero ha)) hp.out.pos
      · rw [Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_succ]; exact h1
    · rw [Nat.choose_eq_zero_of_lt ha]; simp

/-- In characteristic `p`, the Hasse derivatives of order `0 < i < p^e` of a `p^e`-th power
vanish. -/
theorem hasseDeriv_pow_char_pow {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (e : ℕ) (g : R[X]) {i : ℕ} (hi0 : 0 < i) (hi : i < p ^ e) :
    hasseDeriv i (g ^ p ^ e) = 0 := by
  rw [← map_iterateFrobenius_expand, hasseDeriv_map]
  convert Polynomial.map_zero _
  ext n
  rw [hasseDeriv_coeff, coeff_zero, coeff_expand (pow_pos (Fact.out : p.Prime).pos e)]
  split_ifs with h
  · obtain ⟨m, hm⟩ := h
    rw [hm, cast_choose_pow_mul_eq_zero p e m i hi0 hi, zero_mul]
  · rw [mul_zero]

/-- In characteristic `p`, Hasse derivatives of order `< p^e` are linear over `p^e`-th powers. -/
theorem hasseDeriv_pow_char_pow_mul {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (e : ℕ) (g h : R[X]) {i : ℕ} (hi : i < p ^ e) :
    hasseDeriv i (g ^ p ^ e * h) = g ^ p ^ e * hasseDeriv i h := by
  rw [hasseDeriv_mul, Finset.sum_eq_single (0, i)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp only [zero_add] at hab; subst hab; exact absurd rfl hne
      · exact ha
    rw [hasseDeriv_pow_char_pow p e g ha (by omega), zero_mul]
  · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) h

end Polynomial

namespace Polynomial

/-- If the Hasse derivatives of order `< m` of `f` all vanish at `a`, then `(X - a)^m ∣ f`. -/
theorem X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero {R : Type*} [CommRing R] (f : R[X]) (a : R)
    (m : ℕ) (h : ∀ i < m, (hasseDeriv i f).eval a = 0) : (X - C a) ^ m ∣ f := by
  have hX : X ^ m ∣ taylor a f := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [taylor_coeff]; exact h i hi
  obtain ⟨g, hg⟩ := hX
  refine ⟨taylor (-a) g, ?_⟩
  have : f = taylor (-a) (taylor a f) := by rw [taylor_taylor, neg_add_cancel, taylor_zero]
  rw [this, hg, taylor_mul, taylor_X_pow, map_neg, sub_eq_add_neg]

end Polynomial
