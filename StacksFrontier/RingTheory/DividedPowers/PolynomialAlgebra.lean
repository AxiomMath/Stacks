module

public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.RingTheory.DividedPowers.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Divided powers at a prime (Stacks chapter divided power algebra)

Let `p` be a prime and let `A` be a commutative ring in which every integer not divisible by
`p` is invertible, so that `A` is a `ℤ_(p)`-algebra. A divided power structure on an ideal of
such a ring is determined by its `p`th operation, because every other operation is obtained
from it by multiplying by a unit of `A` and composing. The identities that a proposed `p`th
operation `δ` has to satisfy are therefore the ones inherited from the three divided power
axioms: the factorial identity `p! · δ(x) = xᵖ`, homogeneity `δ(a • x) = aᵖ • δ(x)`, and the
addition law, whose cross terms carry the coefficients `1/i! · 1/(p-i)!` for `0 < i < p`.

This file shows that the factorial identity is redundant: homogeneity and the addition law
already force `p! · δ(x) = xᵖ`. The argument computes `δ(n • x)` for a natural number `n` by
induction, which produces the integer polynomial `∑_{i<p} (binom(p, i)/p) nⁱ`; summing it over
`n < p` gives `p^(p-1) - 1`, a unit of `A`, and cancelling that unit yields the identity.

## Main definitions

* `DividedPowers.factorialInverse` — the inverse of `i!` in `A` for `i < p`, which is the
  coefficient appearing in the addition law for the `p`th divided power operation.

## Main results

* `DividedPowers.factorial_mul_of_smul_add` — homogeneity and the addition law for a proposed
  `p`th divided power operation imply its factorial identity.

## Implementation notes

The hypothesis that `A` is a `ℤ_(p)`-algebra is stated intrinsically, as the assertion that
every natural number not divisible by `p` maps to a unit of `A`. This is equivalent to the
localization formulation and it is also what supplies the coefficients `1/i!` occurring in the
addition law. Outside the range `i < p` the value of `factorialInverse` is irrelevant to that
law, and is set to zero.

## References

* [Stacks Project, Tag 07GS](https://stacks.math.columbia.edu/tag/07GS)
* [Stacks Project, Tag 0H87](https://stacks.math.columbia.edu/tag/0H87)
-/

@[expose] public section

open Finset

namespace DividedPowers

/-- The inverse in `A` of `n!` when `n < p`. The value outside that range is irrelevant to the
divided-power addition formula and is set to zero. -/
public noncomputable def factorialInverse {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime)
    (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (n : ℕ) : A :=
  if hn : n < p then
    ↑(hA n.factorial (by simpa [hp.dvd_factorial] using hn)).unit⁻¹
  else 0

/-- The integer `binom(p, i) / p`, which is the normalized binomial coefficient occurring in
the expansion of `(k + 1) ^ p` once the prime `p` has been divided out. -/
private def normalizedBinom (p i : ℕ) : ℕ := p.choose i / p

/-- The polynomial `∑_{i < p} (binom(p, i) / p) kⁱ` measuring the defect of `k ↦ kᵖ` from
additivity. -/
private def normalizedBinomPoly (p k : ℕ) : ℕ :=
  ∑ i ∈ range p, normalizedBinom p i * k ^ i

private lemma sum_range_pred_succ {M : Type*} [AddCommMonoid M] (p : ℕ) (hp : 0 < p)
    (f : ℕ → M) :
    (∑ i ∈ range p, f i) = (∑ i ∈ range (p - 1), f (i + 1)) + f 0 := by
  have h : p - 1 + 1 = p := by omega
  rw [← h, Finset.sum_range_succ']
  simp [h]

/-- `p * (binom(p, i) / p) = binom(p, i)` for `0 < i < p`. -/
private lemma mul_normalizedBinom {p i : ℕ} (hp : p.Prime) (hi0 : i ≠ 0) (hip : i < p) :
    p * normalizedBinom p i = p.choose i :=
  Nat.mul_div_cancel' (Nat.Prime.dvd_choose_self hp hi0 hip)

private lemma normalizedBinomPoly_step {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (k + 1) ^ p = k ^ p + p * normalizedBinomPoly p k + 1 := by
  have hpone : 1 < p := hp.one_lt
  have hbin : (k + 1) ^ p =
      ∑ i ∈ range (p + 1), k ^ i * p.choose i := by
    rw [add_pow]
    simp
  rw [Finset.sum_range_succ] at hbin
  rw [sum_range_pred_succ p hp.pos] at hbin
  have h0 : k ^ 0 * p.choose 0 = 1 := by simp
  have hpterm : k ^ p * p.choose p = k ^ p := by simp
  have hmiddle :
      (∑ i ∈ range (p - 1), k ^ (i + 1) * p.choose (i + 1)) =
        p * normalizedBinomPoly p k := by
    have hpoly :
        (∑ i ∈ range (p - 1), normalizedBinom p (i + 1) * k ^ (i + 1)) =
          normalizedBinomPoly p k := by
      unfold normalizedBinomPoly
      rw [sum_range_pred_succ p hp.pos]
      simp [normalizedBinom, hpone]
    calc
      _ = ∑ i ∈ range (p - 1), p *
          (normalizedBinom p (i + 1) * k ^ (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [← mul_normalizedBinom hp (by omega : i + 1 ≠ 0) (by omega)]
        ring
      _ = p * normalizedBinomPoly p k := by rw [← Finset.mul_sum, hpoly]
  rw [h0, hpterm, hmiddle] at hbin
  omega

private lemma sum_normalizedBinomPoly {p : ℕ} (hp : p.Prime) :
    (∑ k ∈ range p, normalizedBinomPoly p k) = p ^ (p - 1) - 1 := by
  have hsum :
      (∑ k ∈ range p, (k + 1) ^ p) =
        (∑ k ∈ range p, k ^ p) + p * (∑ k ∈ range p, normalizedBinomPoly p k) + p := by
    calc
      (∑ k ∈ range p, (k + 1) ^ p) =
          ∑ k ∈ range p, (k ^ p + p * normalizedBinomPoly p k + 1) :=
            Finset.sum_congr rfl (fun k _ => normalizedBinomPoly_step hp k)
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum, add_left_comm, add_comm]
  have hshift :
      (∑ k ∈ range p, (k + 1) ^ p) = (∑ k ∈ range p, k ^ p) + p ^ p := by
    simpa [Finset.sum_range_succ, hp.ne_zero] using
      (Finset.sum_range_succ' (fun k => k ^ p) p).symm
  have hcancel : p ^ (p - 1) = (∑ k ∈ range p, normalizedBinomPoly p k) + 1 := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    rw [mul_pow_sub_one hp.ne_zero, mul_add_one]
    omega
  omega

private lemma factorialInverse_mul_factorial {A : Type*} [CommRing A] (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) {i : ℕ} (hi : i < p) :
    (i.factorial : A) * factorialInverse p hp hA i = 1 := by
  simp [factorialInverse, hi]

private lemma inverseFactorial_binom {A : Type*} [CommRing A] {p i : ℕ}
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    (hi0 : i ≠ 0) (hip : i < p) :
    factorialInverse p hp hA i * factorialInverse p hp hA (p - i) =
      (normalizedBinom p i : A) * factorialInverse p hp hA (p - 1) := by
  have hp0 := hp.pos
  have hpi : p - i < p := by omega
  have hnat : normalizedBinom p i * i.factorial * (p - i).factorial = (p - 1).factorial := by
    apply Nat.eq_of_mul_eq_mul_left hp0
    calc
      p * (normalizedBinom p i * i.factorial * (p - i).factorial) =
          p.choose i * i.factorial * (p - i).factorial := by
        rw [← mul_normalizedBinom hp hi0 hip]
        ring
      _ = p.factorial := Nat.choose_mul_factorial_mul_factorial (by omega)
      _ = p * (p - 1).factorial := (Nat.mul_factorial_pred hp.ne_zero).symm
  have hnatA : (normalizedBinom p i : A) * i.factorial * (p - i).factorial =
      (p - 1).factorial := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, hnat]
  calc
    factorialInverse p hp hA i * factorialInverse p hp hA (p - i) =
        factorialInverse p hp hA i * factorialInverse p hp hA (p - i) *
            (((p - 1).factorial : A) * factorialInverse p hp hA (p - 1)) := by
      rw [factorialInverse_mul_factorial p hp hA (by omega : p - 1 < p), mul_one]
    _ = ((i.factorial : A) * factorialInverse p hp hA i) *
          (((p - i).factorial : A) * factorialInverse p hp hA (p - i)) *
          ((normalizedBinom p i : A) * factorialInverse p hp hA (p - 1)) := by
      rw [← hnatA]
      ring
    _ = (normalizedBinom p i : A) * factorialInverse p hp hA (p - 1) := by
      rw [factorialInverse_mul_factorial p hp hA hip, factorialInverse_mul_factorial p hp hA hpi,
        one_mul, one_mul]

/-- The image in `A` of `normalizedBinomPoly p k`, scaled by the inverse of `(p - 1)!`. -/
private noncomputable def normalizedBinomPolyA {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime)
    (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (k : ℕ) : A :=
  ∑ i ∈ range p,
    (normalizedBinom p i : A) * factorialInverse p hp hA (p - 1) * (k : A) ^ i

/-- The partial sums of `normalizedBinomPolyA`, which is the coefficient appearing in the
expansion of the `p`th operation at `n • x`. -/
private noncomputable def normalizedBinomSumA {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime)
    (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (n : ℕ) : A :=
  ∑ k ∈ range n, normalizedBinomPolyA p hp hA k

private lemma crossTerm_sum_eq {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (x : I) (n : ℕ) :
    (∑ ij ∈ (antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0),
      factorialInverse p hp hA ij.1 * factorialInverse p hp hA ij.2 *
        ((n : A) * (x : A)) ^ ij.1 * (x : A) ^ ij.2) =
      normalizedBinomPolyA p hp hA n * (x : A) ^ p := by
  have hp0 := hp.pos
  have hpone : 1 < p := hp.one_lt
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  let F : ℕ → A := fun i =>
    if i ≠ 0 ∧ p - i ≠ 0 then
      factorialInverse p hp hA i * factorialInverse p hp hA (p - i) *
        ((n : A) * (x : A)) ^ i * (x : A) ^ (p - i) else 0
  show (∑ i ∈ range (p + 1), F i) = _
  rw [Finset.sum_range_succ, show F p = 0 by simp [F], add_zero, sum_range_pred_succ p hp0 F,
    show F 0 = 0 by simp [F], add_zero]
  unfold normalizedBinomPolyA
  rw [sum_range_pred_succ p hp0 (fun i =>
    (normalizedBinom p i : A) * factorialInverse p hp hA (p - 1) * (n : A) ^ i)]
  have hpoly0 : normalizedBinom p 0 = 0 := by
    simp [normalizedBinom, hpone]
  rw [show (normalizedBinom p 0 : A) * factorialInverse p hp hA (p - 1) * (n : A) ^ 0 = 0 by
    simp [hpoly0], add_zero, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have hi0 : i + 1 ≠ 0 := by omega
  have hip : i + 1 < p := by omega
  have hpow : (x : A) ^ (i + 1) * (x : A) ^ (p - (i + 1)) = (x : A) ^ p := by
    rw [← pow_add]
    congr 1
    omega
  show (if i + 1 ≠ 0 ∧ p - (i + 1) ≠ 0 then
      factorialInverse p hp hA (i + 1) * factorialInverse p hp hA (p - (i + 1)) *
        ((n : A) * (x : A)) ^ (i + 1) * (x : A) ^ (p - (i + 1)) else 0) = _
  rw [ite_eq_left ⟨hi0, by omega⟩, mul_pow, ← hpow, ← inverseFactorial_binom hp hA hi0 hip]
  ring

private lemma normalizedBinomSumA_at_prime {A : Type*} [CommRing A] (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) :
    normalizedBinomSumA p hp hA p =
      ((p ^ (p - 1) - 1 : ℕ) : A) * factorialInverse p hp hA (p - 1) := by
  unfold normalizedBinomSumA normalizedBinomPolyA
  rw [← sum_normalizedBinomPoly hp]
  simp only [normalizedBinomPoly, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- Homogeneity and the divided-power addition law imply the factorial identity for the
`p`th operation. -/
@[stacks 0H87]
public lemma factorial_mul_of_smul_add {A : Type*} [CommRing A] (I : Ideal A) (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (smul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x)
    (add : ∀ x y : I,
      (δ (x + y) : A) = (δ x : A) +
        ∑ ij ∈ (antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0),
          factorialInverse p hp hA ij.1 * factorialInverse p hp hA ij.2 *
            (x : A) ^ ij.1 * (y : A) ^ ij.2 +
        (δ y : A)) :
    ∀ x : I, (p.factorial : A) * (δ x : A) = (x : A) ^ p := by
  have hp2 : 2 ≤ p := hp.two_le
  intro x
  have hmultiple (n : ℕ) :
      (δ (n • x) : A) = (n : A) * (δ x : A) + normalizedBinomSumA p hp hA n * (x : A) ^ p := by
    induction n with
    | zero =>
      have hz : δ (0 : I) = 0 := by
        simpa [zero_pow hp.ne_zero] using smul (0 : A) x
      simp [hz, normalizedBinomSumA]
    | succ n ih =>
      rw [succ_nsmul]
      have hadd := add (n • x) x
      have hcoe : ((n • x : I) : A) = (n : A) * (x : A) := by
        show n • (x : A) = _
        simp [nsmul_eq_mul]
      rw [hcoe, crossTerm_sum_eq p hp hA x n] at hadd
      rw [hadd, ih]
      simp [normalizedBinomSumA, Finset.sum_range_succ, normalizedBinomPolyA,
        add_left_comm, add_comm]
      ring
  have hsmul : (δ (p • x) : A) = (p : A) ^ p * (δ x : A) := by
    simpa [Nat.cast_smul_eq_nsmul] using congrArg (fun z : I => (z : A)) (smul (p : A) x)
  have hrel : ((p : A) ^ p - (p : A)) * (δ x : A) =
      normalizedBinomSumA p hp hA p * (x : A) ^ p := by
    rw [sub_mul, ← hsmul, hmultiple p]
    ring
  let k : ℕ := p ^ (p - 1) - 1
  have hkndiv : ¬p ∣ k := by
    intro hk
    have h : p ∣ p ^ (p - 1) - 1 + 1 := by
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
      exact dvd_pow_self p (by omega)
    exact hp.not_dvd_one ((Nat.dvd_add_right hk).mp h)
  have hkp : (p : A) ^ p - (p : A) = (p : A) * (k : A) := by
    dsimp [k]
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hp.pos), ← mul_pow_sub_one hp.ne_zero (p : A)]
    simp only [Nat.cast_pow, Nat.cast_one]
    ring
  rw [normalizedBinomSumA_at_prime p hp hA, hkp] at hrel
  have hcancel : (p : A) * (δ x : A) = factorialInverse p hp hA (p - 1) * (x : A) ^ p := by
    apply (hA k hkndiv).mul_left_cancel
    simpa only [mul_assoc, mul_left_comm, mul_comm, k] using hrel
  rw [← Nat.mul_factorial_pred hp.ne_zero, Nat.cast_mul, mul_comm (p : A), mul_assoc, hcancel,
    ← mul_assoc, factorialInverse_mul_factorial p hp hA (by omega), one_mul]

end DividedPowers
