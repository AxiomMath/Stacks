module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Trunc
public import StacksFrontier.RingTheory.Polynomial.ReciprocalIntegral
public import StacksFrontier.RingTheory.PowerSeries.LogDerivative

/-!
# Rationality of a zeta series from its tail, and the reciprocal roots

This file is the algebraic half of the rationality of the zeta function of a curve over a finite
field. The geometric input, for a curve `C` of genus `γ` over `𝔽̄_q` with a `q`-Frobenius `Ψ`,
consists of three facts about the numbers `A d` of `Ψ`-stable effective divisors of degree `d`
and the numbers `N m` of points fixed by `Ψ ^ m`:

* `A 0 = 1`, and `T d/dT log ∑_d A d T ^ d = ∑_{m ≥ 1} N m T ^ m` (the Euler product);
* the degrees of the `Ψ`-fixed divisor classes are the multiples of some `δ ≥ 1`, so `A d = 0`
  unless `δ ∣ d`;
* for `δ ∣ d` and `d ≥ 2γ - 1`, `(q - 1) A d = h (q ^ (d + 1 - γ) - 1)`, `h` the number of
  `Ψ`-fixed classes of degree `0` (Riemann–Roch and Lang's lemma).

From these, for `Ψ` and all its powers, this file deduces `δ = 1` (F. K. Schmidt's argument:
`∑ A d T ^ d` would have a pole of order `δ` at `T = 1` after passing to `Ψ ^ δ`,
`Stacks.Zeta.period_eq_one`), that `P = (1 - T)(1 - q T) ∑ A d T ^ d` is a polynomial of degree
at most `2γ` with `P(1) = h` and `q ^ (2γ) P(1/q) = h q ^ γ`
(`Stacks.Zeta.exists_zetaNumerator`), and finally, writing `P = ∏_{i < r} (1 - α_i T)` over
`ℚ̄`, that `N m = 1 + q ^ m - ∑ α_i ^ m`, `h_m = ∏ (1 - α_i ^ m)` and
`q ^ (m (2γ - r)) ∏ (q ^ m - α_i ^ m) = q ^ (m γ) h_m` (`Stacks.Zeta.exists_zeta_roots`).

## Main results

* `PowerSeries.logDerivative_map`, `PowerSeries.logDerivative_expand`,
  `PowerSeries.coeff_logDerivative_one_sub_C_mul_X`: the logarithmic derivative under ring
  homomorphisms, under `T ↦ T ^ δ`, and of a linear factor.
* `Stacks.Zeta.exists_zetaNumerator`: rationality with the values `P(1)` and `P(1/q)`.
* `Stacks.Zeta.period_eq_one`: `δ = 1`.
* `Polynomial.exists_eq_prod_one_sub_C_mul_X`: a polynomial with constant coefficient `1` over an
  algebraically closed field is `∏_{i < deg} (1 - α_i T)`.
* `Stacks.Zeta.exists_zeta_roots`: the reciprocal roots.
-/

@[expose] public noncomputable section

open PowerSeries Finset

/-! ### Logarithmic derivatives -/

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The inverse of a series with constant coefficient `1` is any series it multiplies to `1`. -/
theorem invOfUnit_one_eq_of_mul_eq_one {u v : R⟦X⟧} (hu : constantCoeff u = 1) (h : u * v = 1) :
    invOfUnit u 1 = v := by
  calc invOfUnit u 1 = invOfUnit u 1 * (u * v) := by rw [h, mul_one]
    _ = u * invOfUnit u 1 * v := by ring
    _ = v := by rw [mul_invOfUnit_one hu, one_mul]

/-- A ring homomorphism of power series rings commutes with `invOfUnit _ 1` on series with
constant coefficient `1`. -/
private theorem invOfUnit_one_apply {F : Type*} [FunLike F R⟦X⟧ S⟦X⟧] [RingHomClass F R⟦X⟧ S⟦X⟧]
    (φ : F) {u : R⟦X⟧} (hu : constantCoeff u = 1) (hu' : constantCoeff (φ u) = 1) :
    invOfUnit (φ u) 1 = φ (invOfUnit u 1) :=
  invOfUnit_one_eq_of_mul_eq_one hu' (by rw [← map_mul, mul_invOfUnit_one hu, map_one])

/-- The formal derivative commutes with the map induced by a ring homomorphism. -/
theorem map_derivative (f : R →+* S) (u : R⟦X⟧) : map f (d⁄dX u) = d⁄dX (map f u) := by
  ext n
  rw [coeff_map, coeff_derivative, coeff_derivative, coeff_map, map_mul, map_add, map_natCast,
    map_one]

/-- **The logarithmic derivative commutes with ring homomorphisms.** -/
theorem logDerivative_map (f : R →+* S) {u : R⟦X⟧} (hu : constantCoeff u = 1) :
    logDerivative (map f u) = map f (logDerivative u) := by
  have hu' : constantCoeff (map f u) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu,
      map_one]
  rw [logDerivative, logDerivative, invOfUnit_one_apply (map f) hu hu', map_mul,
    map_mul, map_X, map_derivative]

/-- The coefficient of `T ^ n` of `T u'` is `n` times that of `u`. -/
theorem coeff_X_mul_derivative (u : R⟦X⟧) (n : ℕ) :
    coeff n (X * d⁄dX u) = n * coeff n u := by
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    push_cast
    ring

/-- **The logarithmic derivative of `1 - a T`** is `-∑_{m ≥ 1} a ^ m T ^ m`. -/
theorem coeff_logDerivative_one_sub_C_mul_X (a : R) (m : ℕ) :
    coeff m (logDerivative (1 - C a * X)) = if m = 0 then 0 else -a ^ m := by
  have hu : constantCoeff (1 - C a * X : R⟦X⟧) = 1 := by simp
  have hgeom : (1 - C a * X) * PowerSeries.mk (fun n => a ^ n) = 1 := by
    ext n
    rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_mk, coeff_one]
    cases n with
    | zero => simp
    | succ n =>
      rw [coeff_succ_X_mul, coeff_mk, pow_succ']
      simp
  have hd : d⁄dX (1 - C a * X) = -C a := by
    rw [map_sub, derivative_one, Derivation.leibniz, derivative_X, derivative_C]
    simp
  have hrw : X * -C a * PowerSeries.mk (fun n => a ^ n) =
      -(C a * (X * PowerSeries.mk (fun n => a ^ n))) := by ring
  rw [logDerivative, invOfUnit_one_eq_of_mul_eq_one hu hgeom, hd, hrw, map_neg, coeff_C_mul]
  cases m with
  | zero => simp
  | succ m =>
    rw [coeff_succ_X_mul, coeff_mk, pow_succ']
    simp

/-- The logarithmic derivative of `∏ (1 - a_i T)` is `-∑_{k ≥ 1} (∑ a_i ^ k) T ^ k`. -/
private theorem coeff_logDerivative_prod_one_sub_C_mul_X {r : ℕ} (a : Fin r → R) {k : ℕ}
    (hk : k ≠ 0) : coeff k (logDerivative (∏ i, (1 - C (a i) * X))) = -∑ i, a i ^ k := by
  rw [logDerivative_finsetProd _ _ fun i _ => by simp, map_sum]
  simp only [coeff_logDerivative_one_sub_C_mul_X, ite_eq_right hk, Finset.sum_neg_distrib]

/-- The logarithmic derivative of a power. -/
theorem logDerivative_pow {u : R⟦X⟧} (hu : constantCoeff u = 1) (n : ℕ) :
    logDerivative (u ^ n) = (n : R⟦X⟧) * logDerivative u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, logDerivative_mul (by simp [hu]) hu, ih]
    push_cast
    ring

/-- **The logarithmic derivative of `u(T ^ δ)`** is `δ` times the logarithmic derivative of `u`,
evaluated at `T ^ δ`. -/
theorem logDerivative_expand (δ : ℕ) (hδ : δ ≠ 0) {u : R⟦X⟧} (hu : constantCoeff u = 1) :
    logDerivative (expand δ hδ u) = (δ : R⟦X⟧) * expand δ hδ (logDerivative u) := by
  have hu' : constantCoeff (expand δ hδ u) = 1 := by simp [hu]
  have hder : X * d⁄dX (expand δ hδ u) = (δ : R⟦X⟧) * expand δ hδ (X * d⁄dX u) := by
    ext n
    rw [coeff_X_mul_derivative, ← map_natCast (C (R := R)), coeff_C_mul, coeff_expand,
      coeff_expand]
    split_ifs with h
    · obtain ⟨k, rfl⟩ := h
      rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hδ), coeff_X_mul_derivative]
      push_cast
      ring
    · simp
  rw [logDerivative, logDerivative, invOfUnit_one_apply (expand δ hδ) hu hu', hder,
    mul_assoc, ← map_mul]

end PowerSeries

/-! ### Roots of a polynomial with constant coefficient one -/

namespace Polynomial

/-- `reflect 1 (T - a) = 1 - a T`. -/
theorem reflect_X_sub_C {R : Type*} [CommRing R] (a : R) : reflect 1 (X - C a) = 1 - C a * X := by
  rw [← reflect_one_sub_C_mul_X, reflect_reflect]

/-- **A polynomial with constant coefficient `1` over an algebraically closed field** is a product
`∏_{i < deg P} (1 - α_i T)`. -/
theorem exists_eq_prod_one_sub_C_mul_X {K : Type*} [Field K] [IsAlgClosed K] (P : K[X])
    (h0 : P.coeff 0 = 1) : ∃ α : Fin P.natDegree → K, P = ∏ i, (1 - C (α i) * X) := by
  classical
  set N := P.natDegree
  have hcoeffN : (reflect N P).coeff N = 1 := by
    rw [coeff_reflect, revAt_le (le_refl N), Nat.sub_self, h0]
  have hle : (reflect N P).natDegree ≤ N := by
    refine natDegree_le_iff_coeff_eq_zero.2 fun m hm => ?_
    rw [coeff_reflect, revAt_of_lt hm]
    exact coeff_eq_zero_of_natDegree_lt hm
  have hdegeq : (reflect N P).natDegree = N :=
    le_antisymm hle (le_natDegree_of_ne_zero (by simp [hcoeffN]))
  have hmonic : (reflect N P).Monic := by rw [Monic, leadingCoeff, hdegeq, hcoeffN]
  set s := (reflect N P).roots
  have hcard : s.card = N := by rw [IsAlgClosed.card_roots_eq_natDegree, hdegeq]
  have hlen : s.toList.length = N := by rw [Multiset.length_toList, hcard]
  set α : Fin N → K := fun i => s.toList[i.1]'(by rw [hlen]; exact i.2)
  have hprod : ∏ i, (X - C (α i)) = reflect N P := by
    rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic (by rw [hcard, hdegeq])]
    have h1 : ∏ i : Fin s.toList.length, (X - C (s.toList[i.1])) =
        (s.toList.map fun a => X - C a).prod := by
      rw [← List.prod_ofFn]
      congr 1
      exact List.ext_getElem (by simp) fun n h1 h2 => by simp
    have h2 : (s.toList.map fun a => X - C a).prod = (s.map fun a => X - C a).prod := by
      rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    rw [← h2, ← h1]
    exact Fintype.prod_equiv (finCongr hlen.symm) _ _ fun i => rfl
  have key := reflect_finsetProd Finset.univ (fun i : Fin N => X - C (α i)) (fun _ => 1)
    fun i _ => natDegree_X_sub_C_le (α i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, hprod,
    reflect_reflect] at key
  exact ⟨α, key.trans (Finset.prod_congr rfl fun i _ => reflect_X_sub_C (α i))⟩

end Polynomial

/-! ### The numerator -/

namespace Stacks.Zeta

/-- The coefficients of `(1 - T)(1 - Q T) ∑_n g n T ^ n`. -/
def zetaNumCoeff (Q : ℤ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  g n - (Q + 1) * (if 1 ≤ n then g (n - 1) else 0) + Q * (if 2 ≤ n then g (n - 2) else 0)

/-- The coefficient of `T ^ n` in `(1 - T)(1 - Q T) ∑_n g n T ^ n` is `zetaNumCoeff Q g n`. -/
theorem coeff_zetaNum (Q : ℤ) (g : ℕ → ℤ) (n : ℕ) :
    coeff n ((1 - X) * (1 - C Q * X) * PowerSeries.mk g) = zetaNumCoeff Q g n := by
  have h : ((1 - X) * (1 - C Q * X) : ℤ⟦X⟧) = 1 - C (Q + 1) * X ^ 1 + C Q * X ^ 2 := by
    simp only [map_add, map_one, pow_one]
    ring
  rw [h, add_mul, sub_mul, one_mul, map_add, map_sub, coeff_mk, mul_assoc, mul_assoc,
    coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul', zetaNumCoeff]
  split_ifs <;> simp_all

/-- The sum of the coefficients up to `D` telescopes. -/
theorem sum_zetaNumCoeff (Q : ℤ) (g : ℕ → ℤ) (D : ℕ) :
    ∑ n ∈ range (D + 1), zetaNumCoeff Q g n = g D - Q * (if 1 ≤ D then g (D - 1) else 0) := by
  induction D with
  | zero => simp [zetaNumCoeff]
  | succ D ih =>
    rw [Finset.sum_range_succ, ih, zetaNumCoeff]
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · simp
      ring
    · have h1 : 1 ≤ D := hD
      simp only [h1, show 1 ≤ D + 1 by omega, show 2 ≤ D + 1 by omega, ite_true,
        Nat.add_sub_cancel, show D + 1 - 2 = D - 1 by omega]
      ring

/-- The sum of the coefficients up to `D` weighted by `Q ^ (D - n)` telescopes: it is
`Q ^ D P(1/Q)` when `P` has degree at most `D`. -/
theorem sum_zetaNumCoeff_mul_pow (Q : ℤ) (g : ℕ → ℤ) (D : ℕ) :
    ∑ n ∈ range (D + 1), zetaNumCoeff Q g n * Q ^ (D - n) =
      g D - (if 1 ≤ D then g (D - 1) else 0) := by
  induction D with
  | zero => simp [zetaNumCoeff]
  | succ D ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hsum : ∑ n ∈ range (D + 1), zetaNumCoeff Q g n * Q ^ (D + 1 - n) =
        Q * ∑ n ∈ range (D + 1), zetaNumCoeff Q g n * Q ^ (D - n) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [show D + 1 - n = (D - n) + 1 by have := Finset.mem_range.1 hn; omega, pow_succ]
      ring
    rw [hsum, ih, zetaNumCoeff]
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · simp
      ring
    · have h1 : 1 ≤ D := hD
      simp only [h1, show 1 ≤ D + 1 by omega, show 2 ≤ D + 1 by omega, ite_true,
        Nat.add_sub_cancel, show D + 1 - 2 = D - 1 by omega]
      ring

/-- A power series whose coefficients vanish from `M` on is its truncation at `M`. -/
theorem coe_trunc_of_coeff_eq_zero {R : Type*} [CommRing R] {F : R⟦X⟧} {M : ℕ}
    (h : ∀ n ≥ M, coeff n F = 0) : ((trunc M F : Polynomial R) : R⟦X⟧) = F := by
  ext n
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs with hn
  · rfl
  · exact (h n (not_lt.1 hn)).symm

/-- The value at `1` of a truncation is the sum of the retained coefficients. -/
theorem eval_one_trunc {R : Type*} [CommRing R] (F : R⟦X⟧) (M : ℕ) :
    (trunc (M + 1) F).eval 1 = ∑ n ∈ range (M + 1), coeff n F := by
  rw [Polynomial.eval_eq_sum_range' (natDegree_trunc_lt F M)]
  exact Finset.sum_congr rfl fun n hn => by rw [coeff_trunc, ite_eq_left (Finset.mem_range.1 hn),
    one_pow, mul_one]

/-- **Eventual vanishing of the coefficients of the numerator.** If from `E0` on the coefficients
of `∑ g e T ^ e` satisfy `(q - 1) g e = h (K Q ^ (e - E0) - 1)`, then the coefficients of
`(1 - T)(1 - Q T) ∑ g e T ^ e` vanish from `E0 + 2` on, and the sum of all of them is
`h (Q - 1) / (q - 1)`. -/
theorem zetaNumCoeff_eventually (q Q h K : ℤ) (E0 : ℕ) (g : ℕ → ℤ) (hq : q - 1 ≠ 0)
    (hg : ∀ e ≥ E0, (q - 1) * g e = h * (K * Q ^ (e - E0) - 1)) :
    (∀ n ≥ E0 + 2, zetaNumCoeff Q g n = 0) ∧
      (q - 1) * (g (E0 + 1) - Q * g E0) = h * (Q - 1) := by
  refine ⟨fun n hn => ?_, ?_⟩
  · refine (mul_right_injective₀ hq) ?_
    simp only [zetaNumCoeff, ite_eq_left (by omega : 1 ≤ n), ite_eq_left (by omega : 2 ≤ n),
      mul_zero]
    have h0 := hg n (by omega)
    have h1 := hg (n - 1) (by omega)
    have h2 := hg (n - 2) (by omega)
    rw [show n - E0 = (n - 2 - E0) + 2 by omega, pow_add] at h0
    rw [show n - 1 - E0 = (n - 2 - E0) + 1 by omega, pow_add] at h1
    linear_combination h0 - (Q + 1) * h1 + Q * h2
  · have h0 := hg (E0 + 1) (by omega)
    have h1 := hg E0 le_rfl
    rw [show E0 + 1 - E0 = 1 by omega] at h0
    rw [Nat.sub_self] at h1
    linear_combination h0 - Q * h1

/-! ### Rationality when the period is one -/

/-- **Rationality of the zeta series.** Let `q ≥ 2` and let `A : ℕ → ℕ` with `A 0 = 1` satisfy
`(q - 1) A d = h (q ^ (d + 1 - γ) - 1)` for all `d ≥ 2γ - 1`. Then
`P = (1 - T)(1 - q T) ∑_d A d T ^ d` is a polynomial with integer coefficients, of degree at most
`2γ`, with constant coefficient `1`, `P(1) = h` and `q ^ (2γ) P(1/q) = h q ^ γ`. -/
theorem exists_zetaNumerator (q : ℕ) (hq : 2 ≤ q) (γ h : ℕ) (A : ℕ → ℕ) (hA0 : A 0 = 1)
    (hR : ∀ d, 2 * γ ≤ d + 1 → ((q : ℤ) - 1) * A d = h * ((q : ℤ) ^ (d + 1 - γ) - 1)) :
    ∃ P : Polynomial ℤ, P.natDegree ≤ 2 * γ ∧ P.coeff 0 = 1 ∧
      (P : ℤ⟦X⟧) = (1 - X) * (1 - C (q : ℤ) * X) * PowerSeries.mk (fun d => (A d : ℤ)) ∧
      P.eval 1 = h ∧
      ∑ n ∈ range (2 * γ + 1), P.coeff n * (q : ℤ) ^ (2 * γ - n) = h * (q : ℤ) ^ γ := by
  set g : ℕ → ℤ := fun d => (A d : ℤ)
  set F := (1 - X) * (1 - C (q : ℤ) * X) * PowerSeries.mk g
  have hq1 : (q : ℤ) - 1 ≠ 0 := by
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq
    omega
  have hvan : ∀ n ≥ 2 * γ + 1, coeff n F = 0 := by
    intro n hn
    rw [coeff_zetaNum]
    refine (mul_right_injective₀ hq1) ?_
    simp only [zetaNumCoeff, mul_zero]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      obtain rfl : γ = 0 := by omega
      have h0 := hR 0 (by omega)
      have h1 := hR 1 (by omega)
      simp only [ite_eq_left (le_refl 1), ite_eq_right (by omega : ¬ 2 ≤ 1), Nat.sub_self, mul_zero,
        add_zero]
      simp only [g, Nat.sub_zero, zero_add, pow_one] at h0 h1 ⊢
      linear_combination h1 - ((q : ℤ) + 1) * h0
    · have h0 := hR n (by omega)
      have h1 := hR (n - 1) (by omega)
      have h2 := hR (n - 2) (by omega)
      simp only [ite_eq_left (by omega : 1 ≤ n), ite_eq_left hn2]
      rw [show n + 1 - γ = (n - 2 + 1 - γ) + 2 by omega, pow_add] at h0
      rw [show n - 1 + 1 - γ = (n - 2 + 1 - γ) + 1 by omega, pow_add] at h1
      simp only [g] at h0 h1 h2 ⊢
      linear_combination h0 - ((q : ℤ) + 1) * h1 + (q : ℤ) * h2
  -- the last coefficient, and the last two combined with weight `c`
  have hend : ∀ c : ℤ, ((q : ℤ) - 1) * (g (2 * γ) - c * (if 1 ≤ 2 * γ then g (2 * γ - 1) else 0)) =
      h * ((q : ℤ) ^ (γ + 1) - 1 - c * ((q : ℤ) ^ γ - 1)) := by
    intro c
    rcases Nat.eq_zero_or_pos γ with rfl | hγ
    · have h0 := hR 0 (by omega)
      simp only [hA0, Nat.cast_one, zero_add, Nat.sub_zero, pow_one, mul_one] at h0
      simp only [ite_eq_right (show ¬ 1 ≤ 0 by omega), mul_zero, sub_zero, g, hA0, Nat.cast_one,
        zero_add, pow_one, pow_zero, sub_self]
      linear_combination h0
    · have h0 := hR (2 * γ) (by omega)
      have h1 := hR (2 * γ - 1) (by omega)
      rw [ite_eq_left (by omega : 1 ≤ 2 * γ), show 2 * γ + 1 - γ = γ + 1 by omega] at *
      rw [show 2 * γ - 1 + 1 - γ = γ by omega] at h1
      simp only [g] at h0 h1 ⊢
      linear_combination h0 - c * h1
  refine ⟨trunc (2 * γ + 1) F, ?_, ?_, coe_trunc_of_coeff_eq_zero hvan, ?_, ?_⟩
  · exact Nat.lt_succ_iff.1 (natDegree_trunc_lt F (2 * γ))
  · rw [coeff_trunc, ite_eq_left (by omega), coeff_zetaNum]
    simp [zetaNumCoeff, g, hA0]
  · rw [eval_one_trunc,
      Finset.sum_congr rfl fun n _ => (coeff_zetaNum (q : ℤ) g n : coeff n F = _),
      sum_zetaNumCoeff]
    refine (mul_right_injective₀ hq1) ?_
    linear_combination hend (q : ℤ)
  · have hcoeff : ∀ n ∈ range (2 * γ + 1),
        (trunc (2 * γ + 1) F).coeff n * (q : ℤ) ^ (2 * γ - n) =
          zetaNumCoeff q g n * (q : ℤ) ^ (2 * γ - n) := fun n hn => by
      rw [coeff_trunc, ite_eq_left (Finset.mem_range.1 hn), coeff_zetaNum]
    rw [Finset.sum_congr rfl hcoeff, sum_zetaNumCoeff_mul_pow]
    refine (mul_right_injective₀ hq1) ?_
    linear_combination hend 1

/-! ### The period is one -/

/-- A series supported in the multiples of `δ` is the expansion of its `δ`-th section. -/
theorem mk_eq_expand (δ : ℕ) (hδ : δ ≠ 0) (A : ℕ → ℤ) (hA : ∀ d, ¬ δ ∣ d → A d = 0) :
    PowerSeries.mk A = expand δ hδ (PowerSeries.mk fun k => A (δ * k)) := by
  ext n
  rw [coeff_expand, coeff_mk]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [coeff_mk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hδ)]
  · exact hA n h

/-- Expansion of polynomials and of power series agree. -/
theorem coe_expand {R : Type*} [CommRing R] (p : ℕ) (hp : p ≠ 0) (f : Polynomial R) :
    ((Polynomial.expand R p f : Polynomial R) : R⟦X⟧) = expand p hp (f : R⟦X⟧) := by
  ext n
  rw [Polynomial.coeff_coe, Polynomial.coeff_expand (Nat.pos_of_ne_zero hp), coeff_expand,
    Polynomial.coeff_coe]

/-- **Rationality of the `δ`-th section.** If `(q - 1) A (δ k) = h (q ^ (δ k + 1 - γ) - 1)` for
`δ k ≥ 2γ - 1`, then `(1 - T)(1 - q ^ δ T) ∑_k A (δ k) T ^ k` is a polynomial whose value at `1`
is nonzero (it is `h (q ^ δ - 1) / (q - 1)`). -/
theorem exists_num_of_tail (q : ℤ) (hq : 2 ≤ q) (δ γ : ℕ) (hδ : 0 < δ) (h : ℤ) (hh : h ≠ 0)
    (A : ℕ → ℤ)
    (htail : ∀ k, 2 * γ ≤ δ * k + 1 → (q - 1) * A (δ * k) = h * (q ^ (δ * k + 1 - γ) - 1)) :
    ∃ P : Polynomial ℤ, P.eval 1 ≠ 0 ∧
      (P : ℤ⟦X⟧) = (1 - X) * (1 - C (q ^ δ) * X) * PowerSeries.mk (fun k => A (δ * k)) := by
  set g : ℕ → ℤ := fun k => A (δ * k)
  set E0 := 2 * γ with hE0
  set F := (1 - X) * (1 - C (q ^ δ) * X) * PowerSeries.mk g
  have hq1 : q - 1 ≠ 0 := by omega
  have hg : ∀ e ≥ E0, (q - 1) * g e = h * (q ^ (δ * E0 + 1 - γ) * (q ^ δ) ^ (e - E0) - 1) := by
    intro e he
    rw [← pow_mul, ← pow_add, show δ * E0 + 1 - γ + δ * (e - E0) = δ * e + 1 - γ by
      have : δ * E0 ≤ δ * e := Nat.mul_le_mul_left δ he
      have : E0 ≤ δ * E0 := Nat.le_mul_of_pos_left E0 hδ
      rw [Nat.mul_sub]
      omega]
    exact htail e (by nlinarith)
  obtain ⟨hvan, hval⟩ := zetaNumCoeff_eventually q (q ^ δ) h _ E0 g hq1 hg
  have hvan' : ∀ n ≥ E0 + 2, coeff n F = 0 := fun n hn =>
    (coeff_zetaNum (q ^ δ) g n).trans (hvan n hn)
  refine ⟨trunc (E0 + 2) F, ?_, coe_trunc_of_coeff_eq_zero hvan'⟩
  rw [eval_one_trunc, Finset.sum_congr rfl fun n _ => (coeff_zetaNum (q ^ δ) g n : coeff n F = _),
    sum_zetaNumCoeff, ite_eq_left (by omega), Nat.add_sub_cancel]
  intro h0
  rw [h0, mul_zero] at hval
  have hQ : q ^ δ - 1 ≠ 0 := by
    have : q ≤ q ^ δ := le_self_pow₀ (by omega) hδ.ne'
    omega
  exact mul_ne_zero hh hQ hval.symm

/-- **F. K. Schmidt's argument: the period is one.** Let `A` be the counts of a zeta series of
period `δ` (`A d = 0` unless `δ ∣ d`) whose `δ`-th section has the tail of the curve of genus `γ`
over the field with `q` elements, and let `A'` be the counts of the zeta series of the `δ`-th power
of the Frobenius, of some period `δ'`, with the tail for `q ^ δ`. If the logarithmic derivatives
are related as the point counts are (`N'_k = N_{δ k}`), then `δ = 1`: otherwise `∑ A' d T ^ d`
would be `(∑_k A (δ k) T ^ k) ^ δ`, which has a pole of order `δ` at `T = 1`, while its own
rationality gives a simple pole. -/
theorem period_eq_one (q : ℤ) (hq : 2 ≤ q) (γ : ℕ) (A A' : ℕ → ℤ) (hA0 : A 0 = 1)
    (hA0' : A' 0 = 1) (δ δ' : ℕ) (hδ : 0 < δ) (hδ' : 0 < δ') (h h' : ℤ) (hh : h ≠ 0)
    (hh' : h' ≠ 0) (hA : ∀ d, ¬ δ ∣ d → A d = 0)
    (htail : ∀ k, 2 * γ ≤ δ * k + 1 → (q - 1) * A (δ * k) = h * (q ^ (δ * k + 1 - γ) - 1))
    (hA' : ∀ d, ¬ δ' ∣ d → A' d = 0)
    (htail' : ∀ k, 2 * γ ≤ δ' * k + 1 →
      (q ^ δ - 1) * A' (δ' * k) = h' * ((q ^ δ) ^ (δ' * k + 1 - γ) - 1))
    (hrel : ∀ k, 0 < k → coeff k (logDerivative (PowerSeries.mk A')) =
      coeff (δ * k) (logDerivative (PowerSeries.mk A))) :
    δ = 1 := by
  set B : ℕ → ℤ := fun k => A (δ * k)
  set B' : ℕ → ℤ := fun k => A' (δ' * k)
  have hB : constantCoeff (PowerSeries.mk B) = 1 := by simp [B, hA0]
  have hA'c : constantCoeff (PowerSeries.mk A') = 1 := by simp [hA0']
  -- the zeta series of the power is the `δ`-th power of the section
  have key : PowerSeries.mk A' = (PowerSeries.mk B) ^ δ := by
    refine eq_of_logDerivative_eq hA'c (by simp [hB]) (PowerSeries.ext fun k => ?_)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [coeff_zero_eq_constantCoeff_apply, constantCoeff_logDerivative]
    rw [hrel k hk, mk_eq_expand δ hδ.ne' A hA, logDerivative_expand δ hδ.ne' hB,
      logDerivative_pow hB, ← map_natCast (C (R := ℤ)), coeff_C_mul, coeff_C_mul, coeff_expand_mul]
  obtain ⟨P, hP1, hP⟩ := exists_num_of_tail q hq δ γ hδ h hh A htail
  obtain ⟨P', -, hP'⟩ := exists_num_of_tail (q ^ δ) (le_trans hq (le_self_pow₀ (by omega)
    hδ.ne')) δ' γ hδ' h' hh' A' htail'
  set Q := q ^ δ
  set Q' := Q ^ δ'
  -- the two expressions for `(1 - T ^ δ')(1 - Q' T ^ δ') ((1 - T)(1 - Q T)) ^ δ ∑ A' d T ^ d`
  have hexp : (1 - X ^ δ') * (1 - C Q' * X ^ δ') * PowerSeries.mk A' =
      ((Polynomial.expand ℤ δ' P' : Polynomial ℤ) : ℤ⟦X⟧) := by
    rw [coe_expand δ' hδ'.ne', hP', mk_eq_expand δ' hδ'.ne' A' hA']
    simp only [map_mul, map_sub, map_one, expand_X, expand_C]
  have hpoly : (1 - Polynomial.X) ^ δ * (1 - Polynomial.C Q * Polynomial.X) ^ δ *
        Polynomial.expand ℤ δ' P' =
      (1 - Polynomial.X ^ δ') * (1 - Polynomial.C Q' * Polynomial.X ^ δ') * P ^ δ := by
    refine Polynomial.coe_injective ℤ ?_
    push_cast
    rw [← hexp, hP, mul_pow, mul_pow, ← key]
    ring
  by_contra hne
  obtain ⟨d, rfl⟩ : ∃ d, δ = d + 2 := ⟨δ - 2, by omega⟩
  have hgeom := mul_neg_geom_sum (Polynomial.X : Polynomial ℤ) δ'
  have hfac : (1 - Polynomial.X : Polynomial ℤ) *
        ((1 - Polynomial.X) ^ (d + 1) * (1 - Polynomial.C Q * Polynomial.X) ^ (d + 2) *
          Polynomial.expand ℤ δ' P') =
      (1 - Polynomial.X) * ((∑ i ∈ range δ', Polynomial.X ^ i) *
        (1 - Polynomial.C Q' * Polynomial.X ^ δ') * P ^ (d + 2)) := by
    calc _ = (1 - Polynomial.X) ^ (d + 2) * (1 - Polynomial.C Q * Polynomial.X) ^ (d + 2) *
          Polynomial.expand ℤ δ' P' := by rw [pow_succ' (1 - Polynomial.X) (d + 1)]; ring
      _ = _ := hpoly
      _ = _ := by rw [← hgeom]; ring
  have hne1 : (1 - Polynomial.X : Polynomial ℤ) ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    simp at this
  have hcancel := congrArg (Polynomial.eval 1) (mul_left_cancel₀ hne1 hfac)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, sub_self, zero_pow (Nat.succ_ne_zero d), zero_mul,
    Polynomial.eval_finsetSum, one_pow, Finset.sum_const, Finset.card_range,
    Polynomial.eval_C, mul_one, nsmul_eq_mul] at hcancel
  have hQ' : Q' - 1 ≠ 0 := by
    have : q ≤ Q' := le_trans (le_self_pow₀ (by omega) (by omega : d + 2 ≠ 0))
      (le_self_pow₀ (le_trans (by omega) (le_self_pow₀ (by omega) (by omega : d + 2 ≠ 0)))
        hδ'.ne')
    omega
  have : (δ' : ℤ) * (1 - Q') * P.eval 1 ^ (d + 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hδ'.ne') (by omega)) (pow_ne_zero _ hP1)
  exact this hcancel.symm

/-! ### The reciprocal roots -/

/-- The logarithmic derivative of the image of the numerator in a ring `K`. -/
theorem coeff_logDerivative_map_numerator {K : Type*} [CommRing K] (ι : ℤ →+* K) (Q : ℤ)
    (A : ℕ → ℤ) (hA0 : A 0 = 1) (P : Polynomial ℤ)
    (hP : (P : ℤ⟦X⟧) = (1 - X) * (1 - C Q * X) * PowerSeries.mk A) {k : ℕ} (hk : k ≠ 0) :
    coeff k (logDerivative (map ι (P : ℤ⟦X⟧))) =
      -1 - ι Q ^ k + ι (coeff k (logDerivative (PowerSeries.mk A))) := by
  have hA : constantCoeff (PowerSeries.mk A) = 1 := by simp [hA0]
  have h1 : map ι (1 - X : ℤ⟦X⟧) = 1 - C (1 : K) * X := by simp
  have h2 : map ι (1 - C Q * X : ℤ⟦X⟧) = 1 - C (ι Q) * X := by simp
  have c1 : constantCoeff (1 - C (1 : K) * X) = 1 := by simp
  have c2 : constantCoeff (1 - C (ι Q) * X) = 1 := by simp
  have c3 : constantCoeff (map ι (PowerSeries.mk A)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_mk, hA0, map_one]
  rw [hP, map_mul, map_mul, h1, h2, logDerivative_mul (by rw [map_mul, c1, c2, one_mul]) c3,
    logDerivative_mul c1 c2, logDerivative_map ι hA, map_add, map_add,
    coeff_logDerivative_one_sub_C_mul_X, coeff_logDerivative_one_sub_C_mul_X, ite_eq_right hk,
    ite_eq_right hk, coeff_map, one_pow]
  ring

/-- The value of `T ^ D P(1/T)` at `Q`, for a product of `r ≤ D` reciprocal linear factors. -/
theorem sum_coeff_mul_pow_prod {K : Type*} [Field K] {r : ℕ} (a : Fin r → K) (D : ℕ)
    (hD : r ≤ D) (Q : K) (hQ : Q ≠ 0) :
    ∑ n ∈ range (D + 1), (∏ i, (1 - Polynomial.C (a i) * Polynomial.X)).coeff n * Q ^ (D - n) =
      Q ^ (D - r) * ∏ i, (Q - a i) := by
  set F := ∏ i, (1 - Polynomial.C (a i) * Polynomial.X)
  have hdeg : F.natDegree < D + 1 := by
    have h1 : ∑ i, (1 - Polynomial.C (a i) * Polynomial.X).natDegree ≤ ∑ _i : Fin r, 1 :=
      Finset.sum_le_sum fun i _ => Polynomial.natDegree_one_sub_C_mul_X_le (a i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
    exact lt_of_le_of_lt ((Polynomial.natDegree_prod_le _ _).trans h1) (Nat.lt_succ_of_le hD)
  have hsum : ∑ n ∈ range (D + 1), F.coeff n * Q ^ (D - n) = Q ^ D * F.eval Q⁻¹ := by
    rw [Polynomial.eval_eq_sum_range' hdeg Q⁻¹, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn : n ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    rw [inv_pow, show Q ^ D = Q ^ (D - n) * Q ^ n by rw [← pow_add, Nat.sub_add_cancel hn]]
    field_simp
  rw [hsum, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [show Q ^ D = Q ^ (D - r) * Q ^ r by rw [← pow_add, Nat.sub_add_cancel hD], mul_assoc]
  congr 1
  rw [show Q ^ r = ∏ _i : Fin r, Q by simp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  field_simp

/-- **The reciprocal roots of the zeta function.** Let `q ≥ 2` and `γ`, and for every `m ≥ 1` let
`A m : ℕ → ℕ` be the counts of a zeta series for the field with `q ^ m` elements: `A m 0 = 1`, of
some period `δ m ≥ 1` (`A m d = 0` unless `δ m ∣ d`), with the tail
`(q ^ m - 1) A m d = h m ((q ^ m) ^ (d + 1 - γ) - 1)` for `δ m ∣ d`, `d ≥ 2γ - 1`, `h m ≥ 1`, and
logarithmic derivative `∑_{k ≥ 1} N (m k) T ^ k`. Then there are `r ≤ 2γ` algebraic integers
`α_i` in `ℚ̄` with, for all `m ≥ 1`,

* `N m = 1 + q ^ m - ∑ α_i ^ m`,
* `h m = ∏ (1 - α_i ^ m)`,
* `q ^ (m (2γ - r)) ∏ (q ^ m - α_i ^ m) = q ^ (m γ) h m`.

These are the counts of the curve and of its powers of Frobenius; the last identity is
`P_m(q ^ (-m)) = q ^ (-m γ) P_m(1)` for `P_m = ∏ (1 - α_i ^ m T)`. -/
theorem exists_zeta_roots (q : ℕ) (hq : 2 ≤ q) (γ : ℕ) (N δ h : ℕ → ℕ) (A : ℕ → ℕ → ℕ)
    (hδ : ∀ m, 0 < m → 0 < δ m) (hh : ∀ m, 0 < m → 0 < h m) (hA0 : ∀ m, 0 < m → A m 0 = 1)
    (hR : ∀ m, 0 < m → ∀ d, (¬ δ m ∣ d → A m d = 0) ∧ (δ m ∣ d → 2 * γ ≤ d + 1 →
      ((q : ℤ) ^ m - 1) * A m d = h m * (((q : ℤ) ^ m) ^ (d + 1 - γ) - 1)))
    (hE : ∀ m, 0 < m → ∀ k, k ≠ 0 →
      coeff k (logDerivative (PowerSeries.mk fun d => (A m d : ℤ))) = N (m * k)) :
    ∃ (r : ℕ) (α : Fin r → AlgebraicClosure ℚ), r ≤ 2 * γ ∧ (∀ i, IsIntegral ℤ (α i)) ∧
      ∀ m, 0 < m →
        (N m : AlgebraicClosure ℚ) = 1 + (q : AlgebraicClosure ℚ) ^ m - ∑ i, α i ^ m ∧
        (h m : AlgebraicClosure ℚ) = ∏ i, (1 - α i ^ m) ∧
        (q : AlgebraicClosure ℚ) ^ (m * (2 * γ - r)) *
            ∏ i, ((q : AlgebraicClosure ℚ) ^ m - α i ^ m) =
          (q : AlgebraicClosure ℚ) ^ (m * γ) * h m := by
  set K := AlgebraicClosure ℚ
  set ι : ℤ →+* K := Int.castRingHom K
  have hqm : ∀ m, 0 < m → (2 : ℤ) ≤ (q : ℤ) ^ m := fun m hm =>
    le_trans (by exact_mod_cast hq) (le_self_pow₀ (by omega) hm.ne')
  -- the period is one for every power
  have hδ1 : ∀ m, 0 < m → δ m = 1 := by
    intro m hm
    have hm' : 0 < m * δ m := Nat.mul_pos hm (hδ m hm)
    refine period_eq_one ((q : ℤ) ^ m) (hqm m hm) γ (fun d => A m d) (fun d => A (m * δ m) d)
      (by simp [hA0 m hm]) (by simp [hA0 _ hm']) (δ m) (δ (m * δ m)) (hδ m hm) (hδ _ hm')
      (h m) (h (m * δ m)) (by exact_mod_cast (hh m hm).ne') (by exact_mod_cast (hh _ hm').ne')
      (fun d hd => by simp [(hR m hm d).1 hd]) (fun k hk => (hR m hm _).2 (dvd_mul_right _ _) hk)
      (fun d hd => by simp [(hR _ hm' d).1 hd]) (fun k hk => ?_) (fun k hk => ?_)
    · rw [← pow_mul]
      exact (hR _ hm' _).2 (dvd_mul_right _ _) hk
    · rw [hE _ hm' k hk.ne', hE m hm _ (Nat.mul_ne_zero (hδ m hm).ne' hk.ne'), mul_assoc]
  -- the numerators
  have hP : ∀ m, 0 < m → ∃ P : Polynomial ℤ, P.natDegree ≤ 2 * γ ∧ P.coeff 0 = 1 ∧
      (P : ℤ⟦X⟧) = (1 - X) * (1 - C ((q : ℤ) ^ m) * X) *
        PowerSeries.mk (fun d => (A m d : ℤ)) ∧ P.eval 1 = h m ∧
      ∑ n ∈ range (2 * γ + 1), P.coeff n * ((q : ℤ) ^ m) ^ (2 * γ - n) =
        h m * ((q : ℤ) ^ m) ^ γ := by
    intro m hm
    have := exists_zetaNumerator (q ^ m)
      (le_trans hq (Nat.le_self_pow hm.ne' q)) γ (h m) (A m) (hA0 m hm)
      fun d hd => by exact_mod_cast (hR m hm d).2 (by simp [hδ1 m hm]) hd
    exact_mod_cast this
  choose! P hPdeg hP0 hPeq hP1 hPq using hP
  -- the reciprocal roots of the first numerator
  have h0map : ((P 1).map ι).coeff 0 = 1 := by rw [Polynomial.coeff_map, hP0 1 one_pos, map_one]
  obtain ⟨α, hα⟩ := Polynomial.exists_eq_prod_one_sub_C_mul_X _ h0map
  have hdegmap : ((P 1).map ι).natDegree = (P 1).natDegree :=
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int ι) _
  have hcoeprod : ∀ a : Fin ((P 1).map ι).natDegree → K,
      ((∏ i, (1 - Polynomial.C (a i) * Polynomial.X) : Polynomial K) : K⟦X⟧) =
        ∏ i, (1 - C (a i) * X) := fun a => by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    simp
  refine ⟨((P 1).map ι).natDegree, α, hdegmap.le.trans (hPdeg 1 one_pos), fun i =>
    isIntegral_of_prod_one_sub_C_mul_X_eq_map α (P := P 1) (by simp [hdegmap]) (hP0 1 one_pos)
      hα i, ?_⟩
  -- the point counts
  have hN : ∀ k, 0 < k → (N k : K) = 1 + (q : K) ^ k - ∑ i, α i ^ k := by
    intro k hk
    have e1 := coeff_logDerivative_map_numerator ι (q : ℤ) (fun d => (A 1 d : ℤ))
      (by simp [hA0 1 one_pos]) (P 1) (by rw [hPeq 1 one_pos, pow_one]) hk.ne'
    rw [hE 1 one_pos k hk.ne', one_mul, ← Polynomial.polynomial_map_coe, hα, hcoeprod,
      coeff_logDerivative_prod_one_sub_C_mul_X _ hk.ne'] at e1
    simp only [map_natCast] at e1
    linear_combination -e1
  -- the numerator of the `m`-th power
  have hPm : ∀ m, 0 < m → (P m).map ι = ∏ i, (1 - Polynomial.C (α i ^ m) * Polynomial.X) := by
    intro m hm
    refine Polynomial.coe_injective K ?_
    rw [Polynomial.polynomial_map_coe, hcoeprod (fun i => α i ^ m)]
    refine eq_of_logDerivative_eq ?_ (by simp) (PowerSeries.ext fun k => ?_)
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, Polynomial.coeff_coe, hP0 m hm,
        map_one]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [coeff_zero_eq_constantCoeff_apply, constantCoeff_logDerivative]
    rw [coeff_logDerivative_map_numerator ι _ (fun d => (A m d : ℤ)) (by simp [hA0 m hm]) (P m)
      (hPeq m hm) hk.ne',
      hE m hm k hk.ne', coeff_logDerivative_prod_one_sub_C_mul_X _ hk.ne']
    simp only [map_natCast, map_pow]
    rw [hN (m * k) (Nat.mul_pos hm hk)]
    simp only [← pow_mul]
    ring
  intro m hm
  refine ⟨hN m hm, ?_, ?_⟩
  · have := congrArg (Polynomial.eval 1) (hPm m hm)
    rw [Polynomial.eval_one_map, hP1 m hm, Polynomial.eval_prod] at this
    simpa using this
  · have hq0 : (q : K) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
    have hsum := congrArg ι (hPq m hm)
    simp only [map_sum, map_mul, map_pow, map_natCast] at hsum
    have hcoeff : ∀ n, ι ((P m).coeff n) =
        (∏ i, (1 - Polynomial.C (α i ^ m) * Polynomial.X)).coeff n := fun n => by
      rw [← hPm m hm, Polynomial.coeff_map]
    simp only [hcoeff] at hsum
    rw [sum_coeff_mul_pow_prod (fun i => α i ^ m) (2 * γ) (hdegmap.le.trans (hPdeg 1 one_pos))
      _ hq0] at hsum
    rw [pow_mul, pow_mul, hsum]
    ring

end Stacks.Zeta

end
