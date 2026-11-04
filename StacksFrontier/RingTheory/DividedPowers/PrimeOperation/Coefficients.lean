module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.RingTheory.DividedPowers.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Basic
public import StacksFrontier.RingTheory.DividedPowers.PolynomialAlgebra
public import StacksFrontier.RingTheory.DividedPowers.Ring

/-!
# Divided powers over `ℤ_(p)`: the digit coefficients

Let `p` be a prime and let `A` be a commutative ring in which every integer prime to `p` is
invertible. This file defines the auxiliary family `primeGamma`, from which the divided
power structure of `DividedPowers.existsUnique_of_prime_operation` (Stacks Tag 07GS) is
assembled, together with its integral coefficients and the arithmetic identities between them.

## Implementation notes

The hypothesis that `A` is a `ℤ_(p)`-algebra is stated intrinsically, as the assertion that
every natural number not divisible by `p` maps to a unit of `A`. This is equivalent to the
localization formulation, and it is what supplies the coefficients `1/n!` appearing in the
addition law; those coefficients are the ones constructed in
`StacksFrontier.RingTheory.DividedPowers.PolynomialAlgebra`, so `DividedPowers.factorialInverse`
is reused here rather than redefined.

The operations are assembled from `δ` by writing `n` in base `p` one digit at a time: the
auxiliary `primeGamma` divides `n` by `p`, raises `x` to the remainder, and recurses on `δ x`,
with the integral coefficient `uniformBell (n / p) p · ∏_{j < n % p} (p · (n / p) + j + 1)`
inverted in `A`.
-/

@[expose] public section

open Finset

namespace DividedPowers

private lemma uniformBell_not_dvd {p m : ℕ} (hp : p.Prime) :
    ¬ p ∣ Nat.uniformBell m p := by
  have hmul := Nat.uniformBell_mul_eq m hp.ne_zero
  have hval := congrArg (fun n : ℕ => emultiplicity p n) hmul
  have hfacp : emultiplicity p p.factorial = 1 := by
    have h := hp.emultiplicity_factorial_mul (n := 1)
    have hzero : emultiplicity p 1 = 0 := emultiplicity_eq_zero.mpr hp.not_dvd_one
    simpa [Nat.mul_one, Nat.factorial_one, hzero] using h
  have hfactor := by
    simpa [hp.emultiplicity_mul, hp.emultiplicity_pow, hfacp,
      Nat.mul_comm m p, hp.emultiplicity_factorial_mul, add_assoc] using hval
  have hfinite : emultiplicity p m.factorial ≠ (⊤ : ℕ∞) := by
    intro ht
    have hfin : FiniteMultiplicity p m.factorial :=
      Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, Nat.factorial_pos _⟩
    exact (emultiplicity_eq_top.mp ht) hfin
  have hsum : emultiplicity p m.factorial +
      (emultiplicity p (Nat.uniformBell m p) + m) =
      emultiplicity p m.factorial + m := by
    simpa [add_assoc, add_left_comm, add_comm] using hfactor
  have hcancel : emultiplicity p (Nat.uniformBell m p) + m = m :=
    WithTop.add_left_cancel hfinite hsum
  have hvalzero : emultiplicity p (Nat.uniformBell m p) = 0 := by
    cases hb : emultiplicity p (Nat.uniformBell m p) with
    | top => simp [hb] at hcancel
    | coe k =>
        rw [hb] at hcancel
        have hk : k = 0 := by
          have hkn : k + m = m := by exact_mod_cast hcancel
          omega
        rw [hk]
        simp
  exact emultiplicity_eq_zero.mp hvalzero

private def digitCoefficient (p m r : ℕ) : ℕ :=
  Nat.uniformBell m p * ∏ j ∈ range r, (p * m + j + 1)

private lemma digitProduct_not_dvd {p m r : ℕ} (hp : p.Prime) (hr : r < p) :
    ¬p ∣ ∏ j ∈ range r, (p * m + j + 1) := by
  induction r with
  | zero => simp [hp.ne_one]
  | succ r ih =>
      rw [Finset.prod_range_succ, hp.dvd_mul]
      apply not_or.mpr
      refine ⟨ih (by omega), ?_⟩
      intro hd
      have hlt : r + 1 < p := by omega
      have hd' : p ∣ r + 1 := (Nat.dvd_add_right ⟨m, rfl⟩).mp hd
      have hle : p ≤ r + 1 := Nat.le_of_dvd (by omega) hd'
      omega

private lemma digitCoefficient_not_dvd {p m r : ℕ} (hp : p.Prime) (hr : r < p) :
    ¬p ∣ digitCoefficient p m r := by
  rw [digitCoefficient, hp.dvd_mul]
  exact not_or.mpr ⟨uniformBell_not_dvd hp, digitProduct_not_dvd hp hr⟩

private noncomputable def digitCoefficientInverse {A : Type*} [CommRing A] (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (m r : ℕ) (hr : r < p) : A :=
  ↑(hA (digitCoefficient p m r) (digitCoefficient_not_dvd hp hr)).unit⁻¹

private noncomputable def primeGamma {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I) :
    ℕ → I → A
  | 0, _ => 1
  | 1, x => (x : A)
  | n + 2, x =>
      let m := (n + 2) / p
      let r := (n + 2) % p
      let u := hA (digitCoefficient p m r) (digitCoefficient_not_dvd hp (Nat.mod_lt _ hp.pos))
      ↑(u.unit⁻¹) * (x : A) ^ r * primeGamma p hp hA δ m (δ x)
termination_by n _ => n
decreasing_by
  exact Nat.div_lt_self (by omega) hp.one_lt

private lemma primeGamma_digit_rec {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (n : ℕ) (x : I) :
    primeGamma p hp hA δ n x =
      digitCoefficientInverse p hp hA (n / p) (n % p) (Nat.mod_lt _ hp.pos) *
        (x : A) ^ (n % p) * primeGamma p hp hA δ (n / p) (δ x) := by
  cases n with
  | zero =>
      simp [primeGamma, digitCoefficientInverse, digitCoefficient,
        Nat.uniformBell_zero_left]
  | succ n =>
      cases n with
      | zero =>
          have hp2 : 1 < p := hp.one_lt
          simp only [Nat.div_eq_of_lt hp2, Nat.mod_eq_of_lt (by omega)]
          have hC : digitCoefficient p 0 1 = 1 := by
            simp [digitCoefficient, Nat.uniformBell_zero_left]
          have hnC : ¬p ∣ digitCoefficient p 0 1 := by
            apply digitCoefficient_not_dvd hp
            omega
          let u := hA (digitCoefficient p 0 1) hnC
          have hu : u.unit = 1 := by
            apply Units.ext
            show (u.unit.val : A) = 1
            rw [u.unit_spec]
            simp [hC]
          have hInv : digitCoefficientInverse p hp hA 0 1 (by omega) = 1 := by
            unfold digitCoefficientInverse
            show (↑(u.unit⁻¹) : A) = 1
            rw [hu]
            simp
          simp only [primeGamma]
          rw [hInv]
          simp [primeGamma]
      | succ k =>
          simp only [primeGamma, digitCoefficientInverse]

private lemma primeGamma_at_prime {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I) (x : I) :
    primeGamma p hp hA δ p x = δ x := by
  cases p with
  | zero => exact (hp.ne_zero rfl).elim
  | succ p =>
      cases p with
      | zero => exact (hp.ne_one rfl).elim
      | succ k =>
          simp [primeGamma, digitCoefficient, Nat.div_self (by omega : 0 < k + 2),
            Nat.mod_self, Nat.uniformBell_one_left]

private lemma factorial_mul_digitCoefficient {p m r : ℕ} (hp : p.Prime) :
    digitCoefficient p m r * (p.factorial ^ m * m.factorial) = (p * m + r).factorial := by
  have hbell := Nat.uniformBell_mul_eq m hp.ne_zero
  have hprod : (p * m).factorial *
      (∏ j ∈ range r, (p * m + j + 1)) = (p * m + r).factorial := by
    induction r with
    | zero => simp
    | succ r ih =>
        rw [Finset.prod_range_succ]
        calc
          (p * m).factorial *
              ((∏ j ∈ range r, (p * m + j + 1)) * (p * m + r + 1)) =
              ((p * m).factorial * ∏ j ∈ range r, (p * m + j + 1)) *
                (p * m + r + 1) := by ring
          _ = (p * m + r).factorial * (p * m + r + 1) := by rw [ih]
          _ = (p * m + r + 1).factorial := by
                rw [Nat.factorial_succ]
                ring
          _ = (p * m + (r + 1)).factorial := by
                congr 1
  unfold digitCoefficient
  calc
    (Nat.uniformBell m p * ∏ j ∈ range r, (p * m + j + 1)) *
        (p.factorial ^ m * m.factorial) =
        (Nat.uniformBell m p * (p.factorial ^ m * m.factorial)) *
          ∏ j ∈ range r, (p * m + j + 1) := by ring
    _ = (p * m).factorial * ∏ j ∈ range r, (p * m + j + 1) := by
      rw [show Nat.uniformBell m p * (p.factorial ^ m * m.factorial) =
        (m * p).factorial by simpa [mul_assoc] using hbell]
      rw [Nat.mul_comm m p]
    _ = (p * m + r).factorial := hprod

private lemma digitCoefficient_uniformBell_identity {p m r : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hr : r < p) :
    Nat.uniformBell p m * p.factorial ^ r * digitCoefficient p (p * m + r) 0 =
      Nat.uniformBell p (p * m + r) * digitCoefficient p m r ^ (p - 1) *
        digitCoefficient p m 0 := by
  let n := p * m + r
  let F := p.factorial
  let M := m.factorial
  let N := n.factorial
  let P := (p * m).factorial
  let Q := (p * n).factorial
  let d := digitCoefficient p m r
  let d₀ := digitCoefficient p m 0
  let d₁ := digitCoefficient p n 0
  let u := Nat.uniformBell p m
  let v := Nat.uniformBell p n
  have hd : d * (F ^ m * M) = N := by
    simpa [d, F, M, N, n] using factorial_mul_digitCoefficient hp (m := m) (r := r)
  have hd₀ : d₀ * (F ^ m * M) = P := by
    simpa [d₀, F, M, P] using factorial_mul_digitCoefficient hp (m := m) (r := 0)
  have hd₁ : d₁ * (F ^ n * N) = Q := by
    simpa [d₁, F, N, Q, n] using factorial_mul_digitCoefficient hp (m := n) (r := 0)
  have hu : u * M ^ p * F = P := by
    simpa [u, M, F, P, mul_comm] using Nat.uniformBell_mul_eq p (Nat.ne_of_gt hm)
  have hv : v * N ^ p * F = Q := by
    have hnpos : 0 < n := by
      dsimp [n]
      exact lt_of_lt_of_le (Nat.mul_pos hp.pos hm) (Nat.le_add_right _ _)
    simpa [v, N, F, Q, n, mul_comm] using Nat.uniformBell_mul_eq p hnpos.ne'
  have hpowF : F ^ (p * m + 1) = F ^ (m * (p - 1)) * F ^ m * F := by
    have hmp : m * p = m * (p - 1) + m := by
      calc
        m * p = m * ((p - 1) + 1) := by congr 1; omega
        _ = m * (p - 1) + m := by simp [Nat.mul_add]
    have he : p * m + 1 = m * (p - 1) + m + 1 := by
      rw [Nat.mul_comm p m, hmp]
    rw [he, pow_add, pow_add]
    simp [pow_one]
  have hpowF' : F ^ r * F ^ (p * m + 1) = F * F ^ n := by
    rw [← pow_add, ← pow_succ']
    congr 1
    dsimp [n]
    omega
  have hpowD : d ^ (p - 1) * M ^ (p - 1) * F ^ (m * (p - 1)) = N ^ (p - 1) := by
    have h := congrArg (fun z : ℕ => z ^ (p - 1)) hd
    rw [mul_pow, mul_pow, ← pow_mul] at h
    simpa [F, M, mul_assoc, mul_left_comm, mul_comm] using h
  have hd₀' : d₀ * F ^ m * M = P := by simpa [mul_assoc] using hd₀
  have hd₁' : d₁ * N * F ^ n = Q := by
    simpa [F, N, mul_assoc, mul_left_comm, mul_comm] using hd₁
  have hMp : M ^ p = M ^ (p - 1) * M := by
    calc
      M ^ p = M ^ ((p - 1) + 1) := by congr 1; omega
      _ = M ^ (p - 1) * M := by rw [pow_add, pow_one]
  let K := M ^ p * N * F ^ (p * m + 1)
  have hK : 0 < K := by positivity
  apply Nat.eq_of_mul_eq_mul_right hK
  calc
    (u * F ^ r * d₁) * K = (u * M ^ p * F) * d₁ * N * F ^ n := by
      dsimp [K]
      calc
        (u * F ^ r * d₁) * (M ^ p * N * F ^ (p * m + 1)) =
            u * M ^ p * d₁ * N * (F ^ r * F ^ (p * m + 1)) := by ring
        _ = u * M ^ p * d₁ * N * (F * F ^ n) := by rw [hpowF']
        _ = _ := by ring
    _ = P * d₁ * N * F ^ n := by rw [hu]
    _ = P * Q := by rw [← hd₁']; ring
    _ = (v * N ^ p * F) * (d₀ * F ^ m * M) := by
      rw [hv, hd₀']
      ring
    _ = (v * d ^ (p - 1) * d₀) * K := by
      dsimp [K]
      calc
        (v * N ^ p * F) * (d₀ * F ^ m * M) =
            v * N ^ (p - 1) * N * F * d₀ * F ^ m * M := by
              rw [show p = (p - 1) + 1 by omega, pow_add]
              simp only [pow_one]
              rw [show p - 1 + 1 - 1 = p - 1 by omega]
              ring
        _ = v * (d ^ (p - 1) * M ^ (p - 1) * F ^ (m * (p - 1))) *
              N * F * d₀ * F ^ m * M := by rw [← hpowD]
        _ = (v * d ^ (p - 1) * d₀) *
              (M ^ p * N * F ^ (p * m + 1)) := by
                rw [hpowF]
                rw [hMp]
                ring

private lemma digitCoefficient_low_uniformBell_identity {p r : ℕ} (hp : p.Prime)
    (hrpos : 0 < r) :
    p.factorial ^ (r - 1) * digitCoefficient p r 0 =
      Nat.uniformBell p r * digitCoefficient p 0 r ^ (p - 1) := by
  let F := p.factorial
  let R := r.factorial
  let d₀ := digitCoefficient p 0 r
  let d₁ := digitCoefficient p r 0
  have hd₀ : d₀ = R := by
    simpa [d₀, R, Nat.mul_zero, Nat.pow_zero, Nat.factorial_zero] using
      factorial_mul_digitCoefficient hp (m := 0) (r := r)
  have hd₁ : d₁ * (F ^ r * R) = (p * r).factorial := by
    simpa [d₁, F, R, Nat.add_zero] using
      factorial_mul_digitCoefficient hp (m := r) (r := 0)
  have hu : Nat.uniformBell p r * R ^ p * F = (p * r).factorial := by
    simpa [R, F, mul_comm] using Nat.uniformBell_mul_eq p (Nat.ne_of_gt hrpos)
  have hRp : R ^ p = R ^ (p - 1) * R := by rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
  let K := F * R
  have hK : 0 < K := by positivity
  apply Nat.eq_of_mul_eq_mul_right hK
  calc
    (F ^ (r - 1) * d₁) * K = d₁ * (F ^ r * R) := by
      dsimp [K, F]
      have hr : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hrpos)
      calc
        (p.factorial ^ (r - 1) * d₁) * (p.factorial * R) =
            d₁ * ((p.factorial ^ (r - 1) * p.factorial) * R) := by ring
        _ = d₁ * (p.factorial ^ r * R) := by rw [← pow_succ, hr]
    _ = (p * r).factorial := hd₁
    _ = (Nat.uniformBell p r * R ^ p * F) := hu.symm
    _ = (Nat.uniformBell p r * d₀ ^ (p - 1)) * K := by
      rw [hd₀]
      dsimp [K, F]
      rw [hRp]
      ring

private lemma digitCoefficientInverse_uniformBell_identity {A : Type*} [CommRing A]
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    {m r : ℕ} (hm : 0 < m) (hr : r < p) :
    digitCoefficientInverse p hp hA m r hr ^ p * (p.factorial : A) ^ r *
        (Nat.uniformBell p m : A) *
          digitCoefficientInverse p hp hA m 0 (Nat.zero_lt_of_ne_zero (by omega)) =
      (Nat.uniformBell p (p * m + r) : A) *
        digitCoefficientInverse p hp hA m r hr *
          digitCoefficientInverse p hp hA (p * m + r) 0 (Nat.zero_lt_of_ne_zero (by omega)) := by
  let d := digitCoefficient p m r
  let d₀ := digitCoefficient p m 0
  let d₁ := digitCoefficient p (p * m + r) 0
  have hd : ¬p ∣ d := digitCoefficient_not_dvd hp hr
  have hd₀ : ¬p ∣ d₀ := by
    simpa [d₀] using digitCoefficient_not_dvd hp (by omega : 0 < p)
  have hd₁ : ¬p ∣ d₁ := by
    simpa [d₁] using digitCoefficient_not_dvd hp (by omega : 0 < p)
  let uD : IsUnit (d : A) := hA d hd
  let u₀ : IsUnit (d₀ : A) := hA d₀ hd₀
  let u₁ : IsUnit (d₁ : A) := hA d₁ hd₁
  let eD : Aˣ := uD.unit⁻¹
  let e₀ : Aˣ := u₀.unit⁻¹
  let e₁ : Aˣ := u₁.unit⁻¹
  let w : Aˣ := uD.unit ^ p * u₀.unit * u₁.unit
  have hpow : uD.unit ^ p = uD.unit ^ (p - 1) * uD.unit := by
    calc
      uD.unit ^ p = uD.unit ^ ((p - 1) + 1) := by congr 1; omega
      _ = uD.unit ^ (p - 1) * uD.unit := by rw [pow_add, pow_one]
  have hleft : w * eD ^ p * e₀ = u₁.unit := by
    dsimp [w, eD, e₀]
    calc
      uD.unit ^ p * u₀.unit * u₁.unit * (uD.unit⁻¹) ^ p * u₀.unit⁻¹ =
          (uD.unit ^ p * (uD.unit⁻¹) ^ p) * (u₀.unit * u₀.unit⁻¹) * u₁.unit := by ac_rfl
      _ = u₁.unit := by rw [← mul_pow]; simp
  have hright : w * eD * e₁ = uD.unit ^ (p - 1) * u₀.unit := by
    calc
      w * eD * e₁ = (uD.unit ^ p * eD) * u₀.unit * (u₁.unit * e₁) := by
        dsimp [w]
        ac_rfl
      _ = uD.unit ^ (p - 1) * u₀.unit := by
        rw [show uD.unit ^ p * eD = uD.unit ^ (p - 1) by
          rw [hpow]; simp [eD]]
        simp [e₁]
  have hnat := digitCoefficient_uniformBell_identity hp hm hr
  have hnatA :
      ((Nat.uniformBell p m * p.factorial ^ r * d₁ : ℕ) : A) =
        ((Nat.uniformBell p (p * m + r) * d ^ (p - 1) * d₀ : ℕ) : A) :=
    congrArg (fun z : ℕ => (z : A)) (by simpa [d, d₀, d₁] using hnat)
  have hcastD : (uD.unit : A) = d := by simp
  have hcast0 : (u₀.unit : A) = d₀ := by simp
  have hcast1 : (u₁.unit : A) = d₁ := by simp
  apply (Units.isUnit w).mul_left_cancel
  calc
    (w : A) *
        (digitCoefficientInverse p hp hA m r hr ^ p * (p.factorial : A) ^ r *
          (Nat.uniformBell p m : A) *
            digitCoefficientInverse p hp hA m 0 (Nat.zero_lt_of_ne_zero (by omega))) =
        ((Nat.uniformBell p m * p.factorial ^ r * d₁ : ℕ) : A) := by
          show (w : A) *
              ((eD : A) ^ p * (p.factorial : A) ^ r * (Nat.uniformBell p m : A) *
                (e₀ : A)) = _
          have hleftA := congrArg (fun z : Aˣ => (z : A)) hleft
          rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val] at hleftA
          calc
            (w : A) *
                ((eD : A) ^ p * (p.factorial : A) ^ r * (Nat.uniformBell p m : A) *
                  (e₀ : A)) =
                ((w : A) * (eD : A) ^ p * (e₀ : A)) *
                  ((p.factorial : A) ^ r * (Nat.uniformBell p m : A)) := by ring
            _ = (u₁.unit : A) *
                  ((p.factorial : A) ^ r * (Nat.uniformBell p m : A)) := by rw [hleftA]
            _ = ((Nat.uniformBell p m * p.factorial ^ r * d₁ : ℕ) : A) := by
                  rw [hcast1]
                  push_cast
                  ring
    _ = ((Nat.uniformBell p (p * m + r) * d ^ (p - 1) * d₀ : ℕ) : A) := hnatA
    _ = (w : A) *
        ((Nat.uniformBell p (p * m + r) : A) *
          digitCoefficientInverse p hp hA m r hr *
            digitCoefficientInverse p hp hA (p * m + r) 0 (Nat.zero_lt_of_ne_zero (by omega))) := by
          show _ = (w : A) *
            ((Nat.uniformBell p (p * m + r) : A) * (eD : A) * (e₁ : A))
          have hrightA := congrArg (fun z : Aˣ => (z : A)) hright
          simp only [Units.val_mul, Units.val_pow_eq_pow_val, hcastD, hcast0] at hrightA
          calc
            ((Nat.uniformBell p (p * m + r) * d ^ (p - 1) * d₀ : ℕ) : A) =
                (Nat.uniformBell p (p * m + r) : A) *
                  ((w : A) * (eD : A) * (e₁ : A)) := by
                    push_cast
                    calc
                      _ = (Nat.uniformBell p (p * m + r) : A) *
                          ((d : A) ^ (p - 1) * (d₀ : A)) := by ring
                      _ = (Nat.uniformBell p (p * m + r) : A) *
                          ((w : A) * (eD : A) * (e₁ : A)) := by rw [← hrightA]
            _ = _ := by ring

private lemma digitCoefficientInverse_low_uniformBell_identity {A : Type*} [CommRing A]
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    {r : ℕ} (hrpos : 0 < r) (hr : r < p) :
    digitCoefficientInverse p hp hA 0 r hr ^ p * (p.factorial : A) ^ (r - 1) =
      (Nat.uniformBell p r : A) *
        digitCoefficientInverse p hp hA r 0 (Nat.zero_lt_of_ne_zero (by omega)) *
          digitCoefficientInverse p hp hA 0 r hr := by
  let d₀ := digitCoefficient p 0 r
  let d₁ := digitCoefficient p r 0
  have hd₀ : ¬p ∣ d₀ := by simpa [d₀] using digitCoefficient_not_dvd hp hr
  have hd₁ : ¬p ∣ d₁ := by
    simpa [d₁] using digitCoefficient_not_dvd hp (by omega : 0 < p)
  let u₀ : IsUnit (d₀ : A) := hA d₀ hd₀
  let u₁ : IsUnit (d₁ : A) := hA d₁ hd₁
  let e₀ : Aˣ := u₀.unit⁻¹
  let e₁ : Aˣ := u₁.unit⁻¹
  let w : Aˣ := u₀.unit ^ p * u₁.unit
  have hunit : w * e₀ ^ p = u₁.unit := by
    dsimp [w, e₀]
    calc
      u₀.unit ^ p * u₁.unit * (u₀.unit⁻¹) ^ p =
          (u₀.unit ^ p * (u₀.unit⁻¹) ^ p) * u₁.unit := by ac_rfl
      _ = u₁.unit := by rw [← mul_pow]; simp
  have hpow : u₀.unit ^ p = u₀.unit ^ (p - 1) * u₀.unit := by
    calc
      u₀.unit ^ p = u₀.unit ^ ((p - 1) + 1) := by congr 1; omega
      _ = u₀.unit ^ (p - 1) * u₀.unit := by rw [pow_add, pow_one]
  have hunit' : w * e₁ * e₀ = u₀.unit ^ (p - 1) := by
    dsimp [w, e₁, e₀]
    calc
      u₀.unit ^ p * u₁.unit * u₁.unit⁻¹ * u₀.unit⁻¹ =
          (u₀.unit ^ p * u₀.unit⁻¹) * (u₁.unit * u₁.unit⁻¹) := by ac_rfl
      _ = u₀.unit ^ (p - 1) := by
        rw [hpow]
        simp
  have hnat := digitCoefficient_low_uniformBell_identity hp hrpos
  have hnatA :
      ((p.factorial ^ (r - 1) * d₁ : ℕ) : A) =
        ((Nat.uniformBell p r * d₀ ^ (p - 1) : ℕ) : A) := by
    simpa [d₀, d₁, mul_comm, mul_left_comm, mul_assoc] using
      congrArg (fun z : ℕ => (z : A)) hnat
  have hcast0 : (u₀.unit : A) = d₀ := by simp
  have hcast1 : (u₁.unit : A) = d₁ := by simp
  apply (Units.isUnit w).mul_left_cancel
  calc
    (w : A) *
        (digitCoefficientInverse p hp hA 0 r hr ^ p *
          (p.factorial : A) ^ (r - 1)) =
        ((p.factorial ^ (r - 1) * d₁ : ℕ) : A) := by
          show (w : A) * ((e₀ : A) ^ p * (p.factorial : A) ^ (r - 1)) = _
          have hunitA := congrArg (fun z : Aˣ => (z : A)) hunit
          simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hunitA
          calc
            _ = ((w : A) * (e₀ : A) ^ p) * (p.factorial : A) ^ (r - 1) := by ring
            _ = (u₁.unit : A) * (p.factorial : A) ^ (r - 1) := by rw [hunitA]
            _ = _ := by rw [hcast1]; push_cast; ring
    _ = ((Nat.uniformBell p r * d₀ ^ (p - 1) : ℕ) : A) := hnatA
    _ = (w : A) *
        ((Nat.uniformBell p r : A) *
          digitCoefficientInverse p hp hA r 0 (Nat.zero_lt_of_ne_zero (by omega)) *
            digitCoefficientInverse p hp hA 0 r hr) := by
          show _ = (w : A) *
            ((Nat.uniformBell p r : A) * (e₁ : A) * (e₀ : A))
          have hunitA := congrArg (fun z : Aˣ => (z : A)) hunit'
          simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hunitA
          push_cast
          calc
            _ = (Nat.uniformBell p r : A) * ((d₀ : A) ^ (p - 1)) := by ring
            _ = (Nat.uniformBell p r : A) * ((u₀.unit : A) ^ (p - 1)) := by
                  rw [hcast0]
            _ = (Nat.uniformBell p r : A) * ((w : A) * (e₁ : A) * (e₀ : A)) := by
                  rw [← hunitA]
            _ = _ := by ring

private lemma factorial_eq_choose_mul_digitCoefficient_mul {p a b r s : ℕ} (hp : p.Prime) :
    (p * a + r + (p * b + s)).factorial =
      (p * (a + b) + r + s).choose (p * a + r) * digitCoefficient p a r *
        digitCoefficient p b s * (p.factorial ^ (a + b) * a.factorial * b.factorial) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := p * a + r + (p * b + s))
    (k := p * a + r) (by omega)
  rw [Nat.add_sub_cancel_left] at h
  rw [show p * (a + b) + r + s = p * a + r + (p * b + s) by ring, ← h,
    ← factorial_mul_digitCoefficient hp (m := a) (r := r),
    ← factorial_mul_digitCoefficient hp (m := b) (r := s), pow_add]
  ring

private lemma digitCoefficient_mul_choose_noCarry {p a b r s : ℕ} (hp : p.Prime) :
    digitCoefficient p (a + b) (r + s) * (a + b).choose a =
      (p * (a + b) + r + s).choose (p * a + r) *
        digitCoefficient p a r * digitCoefficient p b s := by
  have hchoose : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
    simpa [Nat.add_sub_cancel_left, Nat.mul_assoc] using
      Nat.choose_mul_factorial_mul_factorial (n := a + b) (k := a) (by omega)
  have hfac : digitCoefficient p (a + b) (r + s) *
      (p.factorial ^ (a + b) * (a + b).factorial) = (p * a + r + (p * b + s)).factorial := by
    rw [factorial_mul_digitCoefficient hp]
    congr 1
    ring
  apply Nat.eq_of_mul_eq_mul_right
    (show 0 < p.factorial ^ (a + b) * a.factorial * b.factorial by positivity)
  rw [← factorial_eq_choose_mul_digitCoefficient_mul hp, ← hfac, ← hchoose]
  ring

private lemma digitCoefficient_mul_choose_carry {p a b r s : ℕ} (hp : p.Prime)
    (hrs : p ≤ r + s) :
    p.factorial * (b + 1) * (a + b + 1).choose a *
        digitCoefficient p (a + b + 1) (r + s - p) =
      (p * (a + b) + r + s).choose (p * a + r) *
        digitCoefficient p a r * digitCoefficient p b s := by
  have hchoose : (a + b + 1).choose a * a.factorial * (b + 1) * b.factorial =
      (a + b + 1).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := a + b + 1) (k := a) (by omega)
    rw [show a + b + 1 - a = b + 1 by omega, Nat.factorial_succ b] at h
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hfac : digitCoefficient p (a + b + 1) (r + s - p) *
      (p.factorial ^ (a + b + 1) * (a + b + 1).factorial) =
        (p * a + r + (p * b + s)).factorial := by
    rw [factorial_mul_digitCoefficient hp]
    congr 1
    have : p * (a + b + 1) = p * a + p * b + p := by ring
    omega
  apply Nat.eq_of_mul_eq_mul_right
    (show 0 < p.factorial ^ (a + b) * a.factorial * b.factorial by positivity)
  rw [← factorial_eq_choose_mul_digitCoefficient_mul hp, ← hfac, ← hchoose, pow_succ]
  ring

private lemma digitCoefficient_mul_digitCoefficientInverse {A : Type*} [CommRing A] (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) {m r : ℕ} (hr : r < p) :
    (digitCoefficient p m r : A) * digitCoefficientInverse p hp hA m r hr = 1 := by
  simp [digitCoefficientInverse]

/-- Cancels three factors from `X * c₃ = Y * c₁ * c₂` using their inverses `i₁`, `i₂`, `i₃`. -/
private lemma mul_inv_eq_mul_inv {A : Type*} [CommRing A] {c₁ c₂ c₃ i₁ i₂ i₃ X Y : A}
    (h₁ : c₁ * i₁ = 1) (h₂ : c₂ * i₂ = 1) (h₃ : c₃ * i₃ = 1) (h : X * c₃ = Y * c₁ * c₂) :
    i₁ * i₂ * X = Y * i₃ := by
  linear_combination (-(i₁ * i₂ * X)) * h₃ + i₁ * i₂ * i₃ * h + Y * i₃ * (c₂ * i₂) * h₁ +
    Y * i₃ * h₂

private lemma digitCoefficientInverse_mul_choose_noCarry {A : Type*} [CommRing A]
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    {a b r s : ℕ} (hr : r < p) (hs : s < p) (hrs : r + s < p) :
    digitCoefficientInverse p hp hA a r hr * digitCoefficientInverse p hp hA b s hs *
      ((a + b).choose a : A) =
        ((p * (a + b) + r + s).choose (p * a + r) : A) *
          digitCoefficientInverse p hp hA (a + b) (r + s) hrs := by
  have hnum := congrArg (Nat.cast : ℕ → A)
    (digitCoefficient_mul_choose_noCarry hp (a := a) (b := b) (r := r) (s := s))
  push_cast at hnum
  exact mul_inv_eq_mul_inv (digitCoefficient_mul_digitCoefficientInverse p hp hA hr)
    (digitCoefficient_mul_digitCoefficientInverse p hp hA hs)
    (digitCoefficient_mul_digitCoefficientInverse p hp hA hrs) (by linear_combination hnum)

private lemma digitCoefficientInverse_mul_choose_carry {A : Type*} [CommRing A]
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    {a b r s : ℕ} (hr : r < p) (hs : s < p) (hrs : p ≤ r + s) :
    (p.factorial : A) * (b + 1 : A) * ((a + b + 1).choose a : A) *
        digitCoefficientInverse p hp hA a r hr * digitCoefficientInverse p hp hA b s hs =
      ((p * (a + b) + r + s).choose (p * a + r) : A) *
        digitCoefficientInverse p hp hA (a + b + 1) (r + s - p) (by omega) := by
  have hnum := congrArg (Nat.cast : ℕ → A)
    (digitCoefficient_mul_choose_carry hp (a := a) (b := b) (r := r) (s := s) hrs)
  push_cast at hnum
  have := mul_inv_eq_mul_inv (digitCoefficient_mul_digitCoefficientInverse p hp hA hr)
    (digitCoefficient_mul_digitCoefficientInverse p hp hA hs)
    (digitCoefficient_mul_digitCoefficientInverse p hp hA (by omega : r + s - p < p))
    (X := (p.factorial : A) * (b + 1 : A) * ((a + b + 1).choose a : A))
    (Y := ((p * (a + b) + r + s).choose (p * a + r) : A)) (by linear_combination hnum)
  linear_combination this

end DividedPowers
