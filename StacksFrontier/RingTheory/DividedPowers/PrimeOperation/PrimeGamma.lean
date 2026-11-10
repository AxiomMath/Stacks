module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.RingTheory.DividedPowers.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Basic
public import StacksFrontier.RingTheory.DividedPowers.PolynomialAlgebra
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.DividedPowers.PrimeOperation.Coefficients
import all StacksFrontier.RingTheory.DividedPowers.PrimeOperation.Coefficients

/-!
# Divided powers over `ℤ_(p)`: the operations `primeGamma`

Properties of the auxiliary family `primeGamma` built from a proposed `p`th operation `δ`:
the factorial identity `n! · γₙ(x) = xⁿ`, additivity below `p`, the product rule
`γₘ · γₙ = (m + n choose m) · γ_{m+n}`, homogeneity, membership in `I`, and the
composition rule with `δ`.
-/

@[expose] public section

open Finset

namespace DividedPowers

lemma primeGamma_factorial_mul {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (factorial_mul : ∀ x : I, (p.factorial : A) * (δ x : A) = (x : A) ^ p) :
    ∀ n (x : I), (n.factorial : A) * primeGamma p hp hA δ n x = (x : A) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x
      cases n with
      | zero => simp [primeGamma]
      | succ n =>
          cases n with
          | zero => simp [primeGamma]
          | succ k =>
              let N := k + 2
              let m := N / p
              let r := N % p
              let d := digitCoefficient p m r
              have hm : m < N := Nat.div_lt_self (by omega) hp.one_lt
              have hd := hA d (digitCoefficient_not_dvd hp (Nat.mod_lt _ hp.pos))
              have hrec := ih m hm (δ x)
              have hN : p * m + r = N := Nat.div_add_mod N p
              simp only [primeGamma]
              rw [show (N.factorial : A) =
                ((d : A) * (p.factorial : A) ^ m * (m.factorial : A)) by
                  have hnat := factorial_mul_digitCoefficient hp
                    (m := m) (r := r)
                  have hnatA := congrArg (fun z : ℕ => (z : A)) hnat
                  rw [hN] at hnatA
                  have hfacA : (N.factorial : A) =
                      (d : A) * (p.factorial : A) ^ m * (m.factorial : A) := by
                    simpa [mul_assoc] using hnatA.symm
                  exact hfacA]
              have hunit : (d : A) * ↑(hd.unit⁻¹) = 1 := by
                simp [d, digitCoefficient]
              have hpcast : (p.factorial : A) * (δ x : A) = (x : A) ^ p :=
                factorial_mul x
              calc
                _ = ((d : A) * ↑(hd.unit⁻¹)) *
                    ((p.factorial : A) ^ m * (m.factorial : A) *
                      primeGamma p hp hA δ m (δ x)) * (x : A) ^ r := by
                      ring
                _ = ((p.factorial : A) ^ m *
                    ((m.factorial : A) * primeGamma p hp hA δ m (δ x))) *
                    (x : A) ^ r := by rw [hunit]; ring
                _ = ((p.factorial : A) ^ m * (δ x : A) ^ m) * (x : A) ^ r := by
                      rw [hrec]
                _ = ((p.factorial : A) * (δ x : A)) ^ m * (x : A) ^ r := by rw [mul_pow]
                _ = (x : A) ^ (p * m) * (x : A) ^ r := by rw [hpcast, ← pow_mul]
                _ = (x : A) ^ N := by
                      rw [← pow_add]
                      congr 1

lemma primeGamma_eq_inv_factorial {A : Type*} [CommRing A] {I : Ideal A}
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (factorial_mul : ∀ x : I, (p.factorial : A) * (δ x : A) = (x : A) ^ p)
    {n : ℕ} (hn : n < p) (x : I) :
    primeGamma p hp hA δ n x =
      ↑(hA n.factorial (by simpa [hp.dvd_factorial] using hn)).unit⁻¹ * (x : A) ^ n := by
  let u := hA n.factorial (by simpa [hp.dvd_factorial] using hn)
  have hfac := primeGamma_factorial_mul p hp hA δ factorial_mul n x
  have huval : (↑u.unit : A) = (n.factorial : A) := u.unit_spec
  apply u.mul_left_cancel
  calc
    ↑u.unit * primeGamma p hp hA δ n x = (x : A) ^ n := by rw [huval]; exact hfac
    _ = ↑u.unit * (↑(u.unit⁻¹) * (x : A) ^ n) := (u.unit.mul_inv_cancel_left _).symm

private lemma factorialInverse_mul_factorial {A : Type*} [CommRing A] (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    {n : ℕ} (hn : n < p) :
    (n.factorial : A) * factorialInverse p hp hA n = 1 := by
  unfold factorialInverse
  rw [dite_eq_left hn]
  simp

lemma factorialInverse_mul_choose {A : Type*} [CommRing A] (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    {n i : ℕ} (hn : n < p) (hi : i ≤ n) :
    factorialInverse p hp hA n * (n.choose i : A) =
      factorialInverse p hp hA i * factorialInverse p hp hA (n - i) := by
  have hi' : i < p := lt_of_le_of_lt hi hn
  have hj' : n - i < p := lt_of_le_of_lt (Nat.sub_le _ _) hn
  have hfacn := factorialInverse_mul_factorial p hp hA hn
  have hfac_i := factorialInverse_mul_factorial p hp hA hi'
  have hfac_j := factorialInverse_mul_factorial p hp hA hj'
  have hunitn : IsUnit (n.factorial : A) :=
    hA n.factorial (by simpa [hp.dvd_factorial] using hn)
  have hnat := Nat.choose_mul_factorial_mul_factorial hi
  have hcast := congrArg (fun z : ℕ => (z : A)) hnat
  simp only [Nat.cast_mul] at hcast
  have hfacpair :
      ((i.factorial : A) * factorialInverse p hp hA i) *
        (((n - i).factorial : A) * factorialInverse p hp hA (n - i)) = 1 := by
    rw [hfac_i, hfac_j]
    simp
  have hcoeff : (n.choose i : A) =
      ((n.choose i : A) * (i.factorial : A) * ((n - i).factorial : A)) *
        (factorialInverse p hp hA i * factorialInverse p hp hA (n - i)) := by
    calc
      (n.choose i : A) = (n.choose i : A) *
          (((i.factorial : A) * factorialInverse p hp hA i) *
            (((n - i).factorial : A) * factorialInverse p hp hA (n - i))) := by
        rw [hfacpair]
        simp
      _ = _ := by ring
  apply hunitn.mul_left_cancel
  calc
    (n.factorial : A) *
        (factorialInverse p hp hA n * (n.choose i : A)) =
        (n.factorial : A) * factorialInverse p hp hA n * (n.choose i : A) := by ring
    _ = (n.choose i : A) := by rw [hfacn]; simp
    _ = (n.factorial : A) *
        (factorialInverse p hp hA i * factorialInverse p hp hA (n - i)) := by
          calc
            _ = ((n.choose i : A) * (i.factorial : A) * ((n - i).factorial : A)) *
                  (factorialInverse p hp hA i * factorialInverse p hp hA (n - i)) := hcoeff
            _ = _ := by rw [← hcast]

lemma primeGamma_eq_factorialInverse {A : Type*} [CommRing A] {I : Ideal A}
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (factorial_mul : ∀ x : I, (p.factorial : A) * (δ x : A) = (x : A) ^ p)
    {n : ℕ} (hn : n < p) (x : I) :
    primeGamma p hp hA δ n x = factorialInverse p hp hA n * (x : A) ^ n := by
  simpa [factorialInverse, hn] using
    (primeGamma_eq_inv_factorial p hp hA δ factorial_mul hn x)

lemma primeGamma_add_of_lt_prime {A : Type*} [CommRing A] {I : Ideal A}
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (factorial_mul : ∀ x : I, (p.factorial : A) * (δ x : A) = (x : A) ^ p)
    {n : ℕ} (hn : n < p) (x y : I) :
    primeGamma p hp hA δ n (x + y) =
      (antidiagonal n).sum fun ij ↦
        primeGamma p hp hA δ ij.1 x * primeGamma p hp hA δ ij.2 y := by
  rw [primeGamma_eq_factorialInverse p hp hA δ factorial_mul hn (x + y)]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change factorialInverse p hp hA n * ((x : A) + (y : A)) ^ n = _
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hi_lt : i < p := lt_of_le_of_lt hi_le hn
  have hj_lt : n - i < p := lt_of_le_of_lt (Nat.sub_le _ _) hn
  rw [primeGamma_eq_factorialInverse p hp hA δ factorial_mul hi_lt x,
    primeGamma_eq_factorialInverse p hp hA δ factorial_mul hj_lt y]
  have hcoef := factorialInverse_mul_choose p hp hA hn hi_le
  calc
    factorialInverse p hp hA n *
        ((x : A) ^ i * (y : A) ^ (n - i) * (n.choose i : A)) =
        (factorialInverse p hp hA n * (n.choose i : A)) *
          ((x : A) ^ i * (y : A) ^ (n - i)) := by ring
    _ = (factorialInverse p hp hA i * factorialInverse p hp hA (n - i)) *
          ((x : A) ^ i * (y : A) ^ (n - i)) := by rw [hcoef]
    _ = (factorialInverse p hp hA i * (x : A) ^ i) *
          (factorialInverse p hp hA (n - i) * (y : A) ^ (n - i)) := by ring

lemma primeGamma_mul_dpow_of_lt_prime {A : Type*} [CommRing A] {I : Ideal A}
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (factorial_mul : ∀ x : I, (p.factorial : A) * (δ x : A) = (x : A) ^ p)
    {m n : ℕ} (hmn : m + n < p) (x : I) :
    primeGamma p hp hA δ m x * primeGamma p hp hA δ n x =
      (m + n).choose m * primeGamma p hp hA δ (m + n) x := by
  have hm : m < p := lt_of_le_of_lt (Nat.le_add_right m n) hmn
  have hn : n < p := lt_of_le_of_lt (Nat.le_add_left n m) (by simpa [Nat.add_comm] using hmn)
  have hsum : m + n < p := hmn
  rw [primeGamma_eq_factorialInverse p hp hA δ factorial_mul hm x,
    primeGamma_eq_factorialInverse p hp hA δ factorial_mul hn x,
    primeGamma_eq_factorialInverse p hp hA δ factorial_mul hsum x]
  have hcoef := factorialInverse_mul_choose p hp hA hsum (n := m + n) (i := m)
    (by omega)
  have hcoef' : factorialInverse p hp hA (m + n) * ((m + n).choose m : A) =
      factorialInverse p hp hA m * factorialInverse p hp hA n := by
    simpa [Nat.add_sub_cancel_left] using hcoef
  calc
    (factorialInverse p hp hA m * (x : A) ^ m) *
        (factorialInverse p hp hA n * (x : A) ^ n) =
        (factorialInverse p hp hA m * factorialInverse p hp hA n) *
          (x : A) ^ (m + n) := by rw [pow_add]; ring
    _ = ((m + n).choose m : A) *
        (factorialInverse p hp hA (m + n) * (x : A) ^ (m + n)) := by
          rw [← hcoef']
          ring

lemma primeGamma_mul_dpow {A : Type*} [CommRing A] {I : Ideal A}
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (factorial_mul : ∀ x : I, (p.factorial : A) * (δ x : A) = (x : A) ^ p) :
    ∀ m n (x : I), primeGamma p hp hA δ m x * primeGamma p hp hA δ n x =
      (m + n).choose m * primeGamma p hp hA δ (m + n) x := by
  intro m n x
  induction hmn : m + n using Nat.strong_induction_on generalizing m n x with
  | h k ih =>
      by_cases hm : m = 0
      · subst m
        have hk : k = n := by simpa using hmn.symm
        subst k
        simp [primeGamma]
      by_cases hn : n = 0
      · subst n
        have hk : k = m := by simpa using hmn.symm
        subst k
        simp [primeGamma]
      by_cases hk : k < p
      · simpa [hmn] using (primeGamma_mul_dpow_of_lt_prime p hp hA δ factorial_mul
          (m := m) (n := n) (by omega) x)
      have hkp : p ≤ k := Nat.le_of_not_gt hk
      let a := m / p
      let r := m % p
      let b := n / p
      let s := n % p
      let q := a + b
      have hmdec : m = p * a + r := by
        dsimp [a, r]
        exact (Nat.div_add_mod m p).symm
      have hndec : n = p * b + s := by
        dsimp [b, s]
        exact (Nat.div_add_mod n p).symm
      have hr : r < p := by dsimp [r]; exact Nat.mod_lt _ hp.pos
      have hs : s < p := by dsimp [s]; exact Nat.mod_lt _ hp.pos
      have htotal : k = p * q + (r + s) := by
        rw [← hmn, hmdec, hndec]
        dsimp [q]
        ring
      have hqLt : q < k := by
        have hmul : 2 * q ≤ p * q := Nat.mul_le_mul_right q hp.two_le
        have hlo : p * q ≤ k := by rw [htotal]; omega
        by_cases hq0 : q = 0
        · subst q
          omega
        · omega
      have hdm : ∀ q t, t < p → k = p * q + t → (m + n) / p = q ∧ (m + n) % p = t :=
        fun q t ht h ↦ (Nat.div_mod_unique hp.pos).2 ⟨by rw [hmn, h, Nat.add_comm], ht⟩
      have hchooseTop : p * (a + b) + r + s = m + n := by
        rw [hmdec, hndec]
        ring
      have hchooseBot : p * a + r = m := hmdec.symm
      have hlhs : primeGamma p hp hA δ m x * primeGamma p hp hA δ n x =
          digitCoefficientInverse p hp hA a r hr *
            digitCoefficientInverse p hp hA b s hs *
            ((x : A) ^ r * (x : A) ^ s) *
            (primeGamma p hp hA δ a (δ x) * primeGamma p hp hA δ b (δ x)) := by
        rw [primeGamma_digit_rec p hp hA δ m x, primeGamma_digit_rec p hp hA δ n x]
        simp only [a, r, b, s]
        ring
      by_cases hrs : r + s < p
      · obtain ⟨hq, hrem⟩ := hdm q (r + s) hrs htotal
        have hrec := ih q hqLt a b (δ x) rfl
        have hcoef := digitCoefficientInverse_mul_choose_noCarry p hp hA
          (a := a) (b := b) hr hs hrs
        rw [hchooseTop, hchooseBot] at hcoef
        rw [hlhs, ← hmn, primeGamma_digit_rec p hp hA δ (m + n) x]
        simp only [hq, hrem]
        calc
          _ = digitCoefficientInverse p hp hA a r hr *
                digitCoefficientInverse p hp hA b s hs *
                ((a + b).choose a : A) *
                ((x : A) ^ (r + s) * primeGamma p hp hA δ (a + b) (δ x)) := by
                  rw [hrec, ← pow_add]
                  ring
          _ = _ := by rw [hcoef]; ring
      · have hcarry : p ≤ r + s := Nat.le_of_not_gt hrs
        let t := r + s - p
        have hsum : r + s = p + t := by dsimp [t]; omega
        have ht : t < p := by dsimp [t]; omega
        let q' := q + 1
        have htotal' : k = p * q' + t := by
          rw [← hmn, hmdec, hndec]
          dsimp [q', q]
          calc
            (p * a + r) + (p * b + s) = p * (a + b) + (r + s) := by ring
            _ = p * (a + b + 1) + t := by
              rw [hsum, Nat.mul_add]
              ring
        have hq'Lt : q' < k := by
          have hmul : 2 * q' ≤ p * q' := Nat.mul_le_mul_right q' hp.two_le
          have hlo : p * q' ≤ k := by rw [htotal']; omega
          have hqpos : 0 < q' := by simp [q']
          omega
        have hb1Lt : b + 1 < k := by
          have hle : b + 1 ≤ q' := by simp [q', q]
          exact lt_of_le_of_lt hle hq'Lt
        obtain ⟨hq, hrem⟩ := hdm q' t ht htotal'
        have hrecAB1 := ih q' hq'Lt a (b + 1) (δ x) (by dsimp [q', q]; omega)
        have hrecB1 := ih (b + 1) hb1Lt b 1 (δ x) rfl
        have hchooseB : (b + 1).choose b = b + 1 := by
          simp
        have hcoef := digitCoefficientInverse_mul_choose_carry p hp hA
          (a := a) (b := b) (r := r) (s := s) hr hs hcarry
        rw [hchooseTop, hchooseBot] at hcoef
        have hpcast := factorial_mul x
        rw [hlhs, ← hmn, primeGamma_digit_rec p hp hA δ (m + n) x]
        simp only [hq, hrem]
        calc
          _ = digitCoefficientInverse p hp hA a r hr *
                digitCoefficientInverse p hp hA b s hs * (p.factorial : A) *
                (x : A) ^ t * (δ x : A) *
                (primeGamma p hp hA δ a (δ x) * primeGamma p hp hA δ b (δ x)) := by
                  rw [← pow_add, hsum, pow_add, ← hpcast]
                  ring
          _ = (digitCoefficientInverse p hp hA a r hr *
                digitCoefficientInverse p hp hA b s hs * (p.factorial : A) *
                (b + 1 : A) * ((a + b + 1).choose a : A)) *
                ((x : A) ^ t * primeGamma p hp hA δ (a + b + 1) (δ x)) := by
                  calc
                    _ = digitCoefficientInverse p hp hA a r hr *
                        digitCoefficientInverse p hp hA b s hs * (p.factorial : A) *
                        (x : A) ^ t *
                        (primeGamma p hp hA δ a (δ x) *
                          (primeGamma p hp hA δ b (δ x) *
                            primeGamma p hp hA δ 1 (δ x))) := by
                          simp only [primeGamma]
                          ring
                    _ = digitCoefficientInverse p hp hA a r hr *
                        digitCoefficientInverse p hp hA b s hs * (p.factorial : A) *
                        (b + 1 : A) * (x : A) ^ t *
                        (primeGamma p hp hA δ a (δ x) *
                          primeGamma p hp hA δ (b + 1) (δ x)) := by
                          rw [hrecB1, hchooseB]
                          push_cast
                          ring
                    _ = _ := by rw [hrecAB1]; ring
          _ = ((p.factorial : A) * (b + 1 : A) *
                ((a + b + 1).choose a : A) *
                digitCoefficientInverse p hp hA a r hr *
                digitCoefficientInverse p hp hA b s hs) *
                ((x : A) ^ t * primeGamma p hp hA δ (a + b + 1) (δ x)) := by ring
          _ = _ := by rw [hcoef]; ring

lemma primeGamma_smul {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (smul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x) :
    ∀ (n : ℕ) (a : A) (x : I),
      primeGamma p hp hA δ n (a • x) = a ^ n * primeGamma p hp hA δ n x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a x
      cases n with
      | zero => simp [primeGamma]
      | succ n =>
          cases n with
          | zero => simp [primeGamma]
          | succ k =>
              let N := k + 2
              let m := N / p
              let r := N % p
              have hm : m < N := Nat.div_lt_self (by omega) hp.one_lt
              have hrec := ih m hm (a ^ p) (δ x)
              simp only [primeGamma]
              rw [smul]
              dsimp [N, m, r] at hrec ⊢
              rw [hrec]
              change
                (↑(hA (digitCoefficient p ((k + 2) / p) ((k + 2) % p))
                    (digitCoefficient_not_dvd hp (Nat.mod_lt _ hp.pos))).unit⁻¹) *
                    (a * (x : A)) ^ ((k + 2) % p) *
                    ((a ^ p) ^ ((k + 2) / p) *
                      primeGamma p hp hA δ ((k + 2) / p) (δ x)) =
                  a ^ (k + 1 + 1) *
                    ((↑(hA (digitCoefficient p ((k + 2) / p) ((k + 2) % p))
                      (digitCoefficient_not_dvd hp (Nat.mod_lt _ hp.pos))).unit⁻¹) *
                    (x : A) ^ ((k + 2) % p) *
                    primeGamma p hp hA δ ((k + 2) / p) (δ x))
              rw [mul_pow, ← pow_mul]
              set c : A := ↑(hA (digitCoefficient p ((k + 2) / p) ((k + 2) % p))
                (digitCoefficient_not_dvd hp (Nat.mod_lt _ hp.pos))).unit⁻¹
              set z : A := primeGamma p hp hA δ ((k + 2) / p) (δ x)
              have hpow : a ^ ((k + 2) % p) * a ^ (p * ((k + 2) / p)) =
                  a ^ (k + 2) := by
                rw [← pow_add, Nat.mod_add_div (k + 2) p]
              calc
                c * (a ^ ((k + 2) % p) * (x : A) ^ ((k + 2) % p)) *
                    (a ^ (p * ((k + 2) / p)) * z) =
                    c * ((a ^ ((k + 2) % p) * a ^ (p * ((k + 2) / p))) *
                      ((x : A) ^ ((k + 2) % p) * z)) := by ring
                _ = c * (a ^ (k + 2) * ((x : A) ^ ((k + 2) % p) * z)) := by rw [hpow]
                _ = a ^ (k + 1 + 1) * (c * (x : A) ^ ((k + 2) % p) * z) := by ring

lemma primeGamma_mem {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I) :
    ∀ (n : ℕ), n ≠ 0 → ∀ x : I, primeGamma p hp hA δ n x ∈ I := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn x
      cases n with
      | zero => exact (hn rfl).elim
      | succ n =>
          cases n with
          | zero => simp [primeGamma]
          | succ k =>
              let N := k + 2
              let m := N / p
              let r := N % p
              have hm : m < N := Nat.div_lt_self (by omega) hp.one_lt
              have hN : N = r + p * m := by
                dsimp [m, r, N]
                exact (Nat.mod_add_div _ _).symm
              simp only [primeGamma]
              let c : A := ↑(hA (digitCoefficient p m r)
                (digitCoefficient_not_dvd hp (Nat.mod_lt _ hp.pos))).unit⁻¹
              let z : A := primeGamma p hp hA δ m (δ x)
              change c * (x : A) ^ r * z ∈ I
              by_cases hr : r = 0
              · have hmne : m ≠ 0 := by
                  intro hm0
                  have hN0 := hN
                  rw [hm0, hr] at hN0
                  simp at hN0
                have hrec : z ∈ I := by
                  dsimp [z]
                  exact ih m hm hmne (δ x)
                simpa [hr] using I.mul_mem_left c hrec
              · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
                have hxpow : (x : A) ^ r ∈ I := by
                  rw [show r = (r - 1) + 1 by omega, pow_succ]
                  exact I.mul_mem_left _ x.property
                simpa [mul_assoc, mul_comm, mul_left_comm] using
                  I.mul_mem_left (z * c) hxpow

lemma primeGamma_delta_comp {A : Type*} [CommRing A] {I : Ideal A} (p : ℕ)
    (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (factorial_mul : ∀ x : I, (p.factorial : A) * (δ x : A) = (x : A) ^ p)
    (smul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x) :
    ∀ (n : ℕ), (hn : n ≠ 0) → ∀ x : I,
      (δ (⟨primeGamma p hp hA δ n x,
        primeGamma_mem p hp hA δ n hn x⟩ : I) : A) =
        (Nat.uniformBell p n : A) * primeGamma p hp hA δ (p * n) x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn x
      cases n with
      | zero => exact (hn rfl).elim
      | succ n =>
          cases n with
          | zero =>
              have hpval := primeGamma_at_prime p hp hA δ x
              have hbell : Nat.uniformBell p 1 = 1 := Nat.uniformBell_one_right p
              have hsub :
                  (⟨primeGamma p hp hA δ 1 x,
                    primeGamma_mem p hp hA δ 1 (by omega) x⟩ : I) = x := by
                apply Subtype.ext
                simp [primeGamma]
              rw [hsub]
              change (δ x : A) = (Nat.uniformBell p 1 : A) *
                primeGamma p hp hA δ (p * 1) x
              simp [hbell, hpval]
          | succ k =>
              let N := k + 2
              let m := N / p
              let r := N % p
              let d := digitCoefficientInverse p hp hA m r (Nat.mod_lt _ hp.pos)
              have hm : m < N := Nat.div_lt_self (by omega) hp.one_lt
              have hN : p * m + r = N := Nat.div_add_mod N p
              have hrec := primeGamma_digit_rec p hp hA δ N x
              have hpmul : ∀ (j : ℕ) (y : I), primeGamma p hp hA δ (p * j) y =
                  digitCoefficientInverse p hp hA j 0 hp.pos * primeGamma p hp hA δ j (δ y) := by
                intro j y
                simpa [Nat.mul_div_cancel_left j hp.pos, Nat.mul_mod_right p j] using
                  primeGamma_digit_rec p hp hA δ (p * j) y
              have hrec0' := hpmul N x
              have hxp : ∀ j : ℕ, (x : A) ^ (p * j) = (p.factorial : A) ^ j * (δ x : A) ^ j := by
                intro j
                rw [pow_mul, ← factorial_mul x, mul_pow]
              by_cases hm0 : m = 0
              · subst m
                have hN' : r = N := by
                  rw [hm0] at hN
                  simpa using hN
                have hrpos : 0 < r := by
                  rw [hN']
                  omega
                have hrlt : r < p := Nat.mod_lt _ hp.pos
                have hlow := digitCoefficient_low_uniformBell_identity hp hrpos
                have hd : d = digitCoefficientInverse p hp hA 0 r hrlt := by
                  dsimp [d]
                  rw [hm0]
                have hcoeff : d ^ p * (p.factorial : A) ^ (r - 1) =
                    (Nat.uniformBell p r : A) *
                      digitCoefficientInverse p hp hA r 0
                        (Nat.zero_lt_of_ne_zero (by omega)) * d := by
                  have hlowInv := digitCoefficientInverse_low_uniformBell_identity
                    p hp hA hrpos hrlt
                  simpa [hd] using hlowInv
                have hsmall : ∀ y : I, primeGamma p hp hA δ N y = d * (y : A) ^ r := by
                  intro y
                  simpa [d, r, hm0, primeGamma] using primeGamma_digit_rec p hp hA δ N y
                have harg :
                    (⟨primeGamma p hp hA δ N x,
                      primeGamma_mem p hp hA δ N (by omega) x⟩ : I) =
                      (d * (x : A) ^ (r - 1)) • x := by
                  apply Subtype.ext
                  change primeGamma p hp hA δ N x =
                    (d * (x : A) ^ (r - 1)) * (x : A)
                  calc
                    _ = d * (x : A) ^ r := hsmall x
                    _ = d * ((x : A) ^ (r - 1) * (x : A)) := by
                      have hpowx : (x : A) ^ r = (x : A) ^ (r - 1) * (x : A) := by
                        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
                      rw [hpowx]
                    _ = _ := by ring
                rw [harg, smul]
                simp only [Submodule.coe_smul, smul_eq_mul]
                change (d * (x : A) ^ (r - 1)) ^ p * (δ x : A) = _
                have hpow : (d * (x : A) ^ (r - 1)) ^ p * (δ x : A) =
                    d ^ p * (p.factorial : A) ^ (r - 1) * (δ x : A) ^ r := by
                  have hdpow : (δ x : A) ^ r = (δ x : A) ^ (r - 1) * (δ x : A) := by
                    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
                  rw [mul_pow, ← pow_mul, Nat.mul_comm (r - 1) p, hxp, hdpow]
                  ring
                calc
                  (d * (x : A) ^ (r - 1)) ^ p * (δ x : A) =
                      d ^ p * (p.factorial : A) ^ (r - 1) * (δ x : A) ^ r := hpow
                  _ = (Nat.uniformBell p r : A) *
                      digitCoefficientInverse p hp hA r 0
                        (Nat.zero_lt_of_ne_zero (by omega)) * d * (δ x : A) ^ r := by
                        rw [hcoeff]
                  _ = (Nat.uniformBell p r : A) *
                      (digitCoefficientInverse p hp hA r 0
                        (Nat.zero_lt_of_ne_zero (by omega)) *
                        primeGamma p hp hA δ N (δ x)) := by
                        rw [hsmall (δ x)]
                        ring
                  _ = (Nat.uniformBell p N : A) *
                      digitCoefficientInverse p hp hA N 0 hp.pos *
                        primeGamma p hp hA δ N (δ x) := by
                        rw [hN']
                        ring
                  _ = (Nat.uniformBell p N : A) * primeGamma p hp hA δ (p * N) x := by
                        rw [hrec0']
                        ring
              · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
                have hposm := ih m hm hm0 (δ x)
                have hmem : primeGamma p hp hA δ m (δ x) ∈ I :=
                  primeGamma_mem p hp hA δ m hm0 (δ x)
                let y : I := ⟨primeGamma p hp hA δ m (δ x), hmem⟩
                have harg :
                    (⟨primeGamma p hp hA δ N x,
                      primeGamma_mem p hp hA δ N (by omega) x⟩ : I) =
                      (d * (x : A) ^ r) • y := by
                  apply Subtype.ext
                  rw [Submodule.coe_smul, smul_eq_mul]
                  simpa [d, y] using hrec
                rw [harg, smul]
                change (d * (x : A) ^ r) ^ p * (δ y : A) = _
                rw [show (δ y : A) =
                  (Nat.uniformBell p m : A) * primeGamma p hp hA δ (p * m) (δ x) by
                    exact hposm]
                have hcoeff := digitCoefficientInverse_uniformBell_identity p hp hA
                  (m := m) (r := r) hmpos (Nat.mod_lt _ hp.pos)
                have hcoeff' :
                    d ^ p * (p.factorial : A) ^ r *
                        (Nat.uniformBell p m : A) *
                      digitCoefficientInverse p hp hA m 0
                            hp.pos =
                    (Nat.uniformBell p N : A) * d *
                      digitCoefficientInverse p hp hA N 0
                        hp.pos := by
                  simpa [d, N, hN] using hcoeff
                have hrecδ := primeGamma_digit_rec p hp hA δ N (δ x)
                have hnrec :
                    primeGamma p hp hA δ N (δ x) =
                      d * (δ x : A) ^ r * primeGamma p hp hA δ m (δ (δ x)) := by
                  simpa [d, m, r] using hrecδ
                rw [mul_pow, ← pow_mul, Nat.mul_comm r p, hxp, hpmul m (δ x)]
                calc
                  _ = (d ^ p * (p.factorial : A) ^ r *
                      (Nat.uniformBell p m : A) *
                        digitCoefficientInverse p hp hA m 0 hp.pos) *
                        ((δ x : A) ^ r * primeGamma p hp hA δ m (δ (δ x))) := by ring
                  _ = ((Nat.uniformBell p N : A) * d *
                      digitCoefficientInverse p hp hA N 0 hp.pos) *
                        ((δ x : A) ^ r * primeGamma p hp hA δ m (δ (δ x))) := by
                        rw [hcoeff']
                  _ = (Nat.uniformBell p N : A) *
                      (digitCoefficientInverse p hp hA N 0 hp.pos *
                        (d * (δ x : A) ^ r *
                          primeGamma p hp hA δ m (δ (δ x)))) := by ring
                  _ = (Nat.uniformBell p N : A) *
                      (digitCoefficientInverse p hp hA N 0 hp.pos *
                        primeGamma p hp hA δ N (δ x)) := by rw [hnrec]
                  _ = (Nat.uniformBell p N : A) *
                      primeGamma p hp hA δ (p * N) x := by rw [hrec0']

end DividedPowers
