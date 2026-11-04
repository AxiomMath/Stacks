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
public import StacksFrontier.RingTheory.DividedPowers.PrimeOperation.PrimeGamma
import all StacksFrontier.RingTheory.DividedPowers.PrimeOperation.PrimeGamma

/-!
# Divided powers over `ℤ_(p)`: transport from the polynomial algebra

Verifying that the family `primeGamma` satisfies the additivity axiom is the only step that
does not reduce to a direct computation; it is done by transporting the axiom from the
canonical divided power structure on the two-variable divided power polynomial algebra
`A⟨x₀, x₁⟩`. The algebra homomorphism `A⟨x₀, x₁⟩ → A` performing the transport is
`primeGammaPolynomialEval`, built from the monomial basis of
`StacksFrontier.RingTheory.DividedPowers.Polynomial.Basic`; its multiplicativity is exactly the
product rule for `primeGamma`.
-/

@[expose] public section

open Finset

namespace DividedPowers

private lemma dividedPowerPolynomialMonomial_univ_prod {A : Type*} [CommRing A]
    (e : Fin 2 →₀ ℕ) :
    dividedPowerPolynomialMonomial A e =
      ∏ i : Fin 2, DividedPowerAlgebra.dp A (e i) (Finsupp.single i 1) := by
  classical
  rw [dividedPowerPolynomialMonomial, Finsupp.prod]
  exact Finset.prod_subset (Finset.subset_univ _) (by
    intro i hi hni
    have hzero : e i = 0 := by simpa using hni
    simp [hzero, DividedPowerAlgebra.dp_zero])

private lemma dividedPowerPolynomialMonomial_mul {A : Type*} [CommRing A]
    (e f : Fin 2 →₀ ℕ) :
    dividedPowerPolynomialMonomial A e *
        dividedPowerPolynomialMonomial A f =
      (∏ i : Fin 2, ((e i + f i).choose (e i) : A)) •
        dividedPowerPolynomialMonomial A (e + f) := by
  rw [dividedPowerPolynomialMonomial_univ_prod,
    dividedPowerPolynomialMonomial_univ_prod,
    dividedPowerPolynomialMonomial_univ_prod]
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ i : Fin 2,
        DividedPowerAlgebra.dp A (e i) (Finsupp.single i (1 : A)) *
          DividedPowerAlgebra.dp A (f i) (Finsupp.single i (1 : A))) =
      ∏ i : Fin 2,
        ((e i + f i).choose (e i) : A) •
          DividedPowerAlgebra.dp A (e i + f i) (Finsupp.single i (1 : A)) := by
          apply Finset.prod_congr rfl
          intro i hi
          simpa only [Nat.cast_smul_eq_nsmul] using
            (DividedPowerAlgebra.dp_mul (R := A) (M := Fin 2 →₀ A)
              (n := e i) (p := f i) (m := Finsupp.single i (1 : A)))
    _ = (∏ i : Fin 2, ((e i + f i).choose (e i) : A)) •
        ∏ i : Fin 2,
          DividedPowerAlgebra.dp A (e i + f i) (Finsupp.single i (1 : A)) := by
          simpa using (Finset.prod_smul (M := A)
            (N := DividedPowerAlgebra A (Fin 2 →₀ A)) (s := Finset.univ)
            (fun i : Fin 2 ↦ ((e i + f i).choose (e i) : A))
            (fun i : Fin 2 ↦ DividedPowerAlgebra.dp A (e i + f i)
              (Finsupp.single i (1 : A))))

private noncomputable def primeGammaPolynomialEval {A : Type*} [CommRing A] {I : Ideal A}
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    (δ : I → I) (x : Fin 2 → I)
    (factorial_mul : ∀ z : I, (p.factorial : A) * (δ z : A) = (z : A) ^ p) :
    DividedPowerAlgebra A (Fin 2 →₀ A) →ₐ[A] A := by
  let b := dividedPowerPolynomialMonomialBasis A (Fin 2)
  let v : (Fin 2 →₀ ℕ) → A := fun e ↦ ∏ i : Fin 2,
    primeGamma p hp hA δ (e i) (x i)
  let l : DividedPowerAlgebra A (Fin 2 →₀ A) →ₗ[A] A := b.constr A v
  refine AlgHom.ofLinearMap l ?_ ?_
  · change l 1 = 1
    have hb0 : b 0 = 1 := by
      rw [dividedPowerPolynomialMonomialBasis_apply,
        dividedPowerPolynomialMonomial_univ_prod]
      simp [DividedPowerAlgebra.dp_zero]
    rw [← hb0]
    simp [l, v, Module.Basis.constr_apply, primeGamma]
  · intro z w
    classical
    let F := (LinearMap.mul A (DividedPowerAlgebra A (Fin 2 →₀ A))).compr₂ l
    let G := (LinearMap.mul A A).compl₁₂ l l
    have hv : ∀ e f : Fin 2 →₀ ℕ,
        (∏ i : Fin 2, ((e i + f i).choose (e i) : A)) * (v (e + f)) = v e * v f := by
      intro e f
      change (∏ i : Fin 2, ((e i + f i).choose (e i) : A)) *
          (∏ i : Fin 2, primeGamma p hp hA δ ((e + f) i) (x i)) =
        (∏ i : Fin 2, primeGamma p hp hA δ (e i) (x i)) *
          (∏ i : Fin 2, primeGamma p hp hA δ (f i) (x i))
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Finsupp.add_apply]
      simpa [Finsupp.add_apply] using
        (primeGamma_mul_dpow p hp hA δ factorial_mul (e i) (f i) (x i)).symm
    have hb (e : Fin 2 →₀ ℕ) :
        b e = dividedPowerPolynomialMonomial A e := by
      change (dividedPowerPolynomialMonomialBasis A (Fin 2)) e = _
      exact dividedPowerPolynomialMonomialBasis_apply A e
    have hl (e : Fin 2 →₀ ℕ) :
        l (dividedPowerPolynomialMonomial A e) = v e := by
      rw [← hb e]
      simp [l, Module.Basis.constr_apply]
    have hMono : ∀ e f : Fin 2 →₀ ℕ,
        l (dividedPowerPolynomialMonomial A e *
          dividedPowerPolynomialMonomial A f) =
        l (dividedPowerPolynomialMonomial A e) *
          l (dividedPowerPolynomialMonomial A f) := by
      intro e f
      calc
        l (dividedPowerPolynomialMonomial A e *
            dividedPowerPolynomialMonomial A f) =
            l ((∏ i : Fin 2, ((e i + f i).choose (e i) : A)) •
              dividedPowerPolynomialMonomial A (e + f)) := by
                rw [dividedPowerPolynomialMonomial_mul]
        _ = (∏ i : Fin 2, ((e i + f i).choose (e i) : A)) • v (e + f) := by
              rw [map_smul, hl]
        _ = v e * v f := hv e f
        _ = l (dividedPowerPolynomialMonomial A e) *
              l (dividedPowerPolynomialMonomial A f) := by
                rw [← hl e, ← hl f]
    have hBasis : ∀ e f : Fin 2 →₀ ℕ,
        l (b e * b f) = l (b e) * l (b f) := by
      intro e f
      simpa [hb e, hb f] using hMono e f
    have hFG : F = G := b.ext fun e => b.ext fun f => hBasis e f
    change F z w = G z w
    rw [hFG]

private lemma dividedPowers_dpow_eq_factorialInverse {A : Type*} [CommRing A]
    {J : Ideal A} (p : ℕ) (hp : p.Prime)
    (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (D : _root_.DividedPowers J)
    {n : ℕ} (hn : n < p) {x : A} (hx : x ∈ J) :
    D.dpow n x = factorialInverse p hp hA n * x ^ n := by
  let u := hA n.factorial (by simpa [hp.dvd_factorial] using hn)
  have hfac := D.factorial_mul_dpow_eq_pow hx (n := n)
  have huval : (u.unit : A) = (n.factorial : A) := u.unit_spec
  apply u.mul_left_cancel
  calc
    (u.unit : A) * D.dpow n x = x ^ n := by rw [huval]; exact hfac
    _ = (u.unit : A) * (factorialInverse p hp hA n * x ^ n) := by
      calc
        x ^ n = ((n.factorial : A) * factorialInverse p hp hA n) * x ^ n := by
          rw [factorialInverse_mul_factorial p hp hA hn]
          simp
        _ = (u.unit : A) * (factorialInverse p hp hA n * x ^ n) := by
          rw [huval]
          ring

private lemma dividedPowers_dpow_p_add_formula {A : Type*} [CommRing A]
    {J : Ideal A} (p : ℕ) (hp : p.Prime)
    (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (D : _root_.DividedPowers J)
    {x y : A} (hx : x ∈ J) (hy : y ∈ J) :
    D.dpow p (x + y) = D.dpow p x +
      ∑ ij ∈ (antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0),
        factorialInverse p hp hA ij.1 * factorialInverse p hp hA ij.2 *
          x ^ ij.1 * y ^ ij.2 + D.dpow p y := by
  have hpartition : antidiagonal p =
      insert (0, p) (insert (p, 0)
        ((antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0))) := by
    ext ij
    rcases ij with ⟨i, j⟩
    simp only [mem_antidiagonal, mem_insert, mem_filter]
    constructor
    · intro hij
      by_cases hi : i = 0
      · left
        subst i
        have hj : j = p := by omega
        subst j
        simp
      · by_cases hj : j = 0
        · right
          left
          subst j
          have hi' : i = p := by omega
          subst i
          simp
        · right
          right
          exact ⟨hij, hi, hj⟩
    · intro h
      rcases h with h | h
      · cases h
        simp
      · rcases h with h | h
        · cases h
          simp
        · exact h.1
  have hnot₁ : (0, p) ∉ (antidiagonal p).filter
      (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0) := by simp
  have hnot₂ : (p, 0) ∉ (antidiagonal p).filter
      (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0) := by simp
  have hnot₁' : (0, p) ∉ insert (p, 0)
      ((antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0)) := by
    simp [hp.ne_zero]
  rw [D.dpow_add hx hy]
  conv_lhs => rw [hpartition]
  rw [sum_insert hnot₁', sum_insert hnot₂]
  rw [D.dpow_zero hx, D.dpow_zero hy]
  simp only [one_mul, mul_one]
  have hinterior :
      ∑ ij ∈ (antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0),
        D.dpow ij.1 x * D.dpow ij.2 y =
      ∑ ij ∈ (antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0),
        factorialInverse p hp hA ij.1 * factorialInverse p hp hA ij.2 *
          x ^ ij.1 * y ^ ij.2 := by
    apply sum_congr rfl
    intro ij hij
    rcases ij with ⟨i, j⟩
    simp only [mem_filter, mem_antidiagonal] at hij
    rcases hij with ⟨hij, hi, hj⟩
    have hi_lt : i < p := by omega
    have hj_lt : j < p := by omega
    rw [dividedPowers_dpow_eq_factorialInverse p hp hA D hi_lt hx,
      dividedPowers_dpow_eq_factorialInverse p hp hA D hj_lt hy]
    ring
  rw [hinterior]
  ring

private lemma primeGammaPolynomialEval_monomial {A : Type*} [CommRing A] {I : Ideal A}
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    (δ : I → I) (x : Fin 2 → I)
    (factorial_mul : ∀ z : I, (p.factorial : A) * (δ z : A) = (z : A) ^ p)
    (e : Fin 2 →₀ ℕ) :
    primeGammaPolynomialEval p hp hA δ x factorial_mul
      (dividedPowerPolynomialMonomial A e) =
        ∏ i : Fin 2, primeGamma p hp hA δ (e i) (x i) := by
  show (dividedPowerPolynomialMonomialBasis A (Fin 2)).constr A
    (fun e ↦ ∏ i : Fin 2, primeGamma p hp hA δ (e i) (x i))
      (dividedPowerPolynomialMonomial A e) = _
  rw [← dividedPowerPolynomialMonomialBasis_apply]
  exact Module.Basis.constr_basis _ _ _ _

private lemma primeGammaPolynomialEval_variableMonomial {A : Type*} [CommRing A]
    {I : Ideal A} (p : ℕ) (hp : p.Prime)
    (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I) (x : Fin 2 → I)
    (factorial_mul : ∀ z : I, (p.factorial : A) * (δ z : A) = (z : A) ^ p)
    (i : Fin 2) (n : ℕ) :
    primeGammaPolynomialEval p hp hA δ x factorial_mul
      (dividedPowerPolynomialVariableMonomial A i n) =
        primeGamma p hp hA δ n (x i) := by
  have he : dividedPowerPolynomialMonomial A (Finsupp.single i n) =
      dividedPowerPolynomialVariableMonomial A i n :=
    Finsupp.prod_single_index DividedPowerAlgebra.dp_zero
  rw [← he, primeGammaPolynomialEval_monomial]
  classical
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Finsupp.single_eq_of_ne hji, primeGamma]
  · simp

private lemma map_factorialInverse {A B : Type*} [CommRing A] [CommRing B]
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    (hB : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : B)) (f : B →+* A) {n : ℕ} (hn : n < p) :
    f (factorialInverse p hp hB n) = factorialInverse p hp hA n := by
  apply (hA n.factorial (by simpa [hp.dvd_factorial] using hn)).mul_left_cancel
  have h := congrArg f (factorialInverse_mul_factorial p hp hB hn)
  simpa only [map_mul, map_natCast, map_one,
    factorialInverse_mul_factorial p hp hA hn] using h

private lemma map_dpow_prime_add {A B : Type*} [CommRing A] [CommRing B]
    {J : Ideal B} (p : ℕ) (hp : p.Prime)
    (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    (hB : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : B)) (D : _root_.DividedPowers J)
    (f : B →+* A) {x y : B} (hx : x ∈ J) (hy : y ∈ J) :
    f (D.dpow p (x + y)) = f (D.dpow p x) +
      ∑ ij ∈ (antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0),
        factorialInverse p hp hA ij.1 * factorialInverse p hp hA ij.2 *
          f x ^ ij.1 * f y ^ ij.2 + f (D.dpow p y) := by
  rw [dividedPowers_dpow_p_add_formula p hp hB D hx hy]
  simp only [map_add, map_sum, map_mul, map_pow]
  congr 2
  apply Finset.sum_congr rfl
  intro ij hij
  have h := Finset.mem_filter.mp hij
  have he := Finset.mem_antidiagonal.mp h.1
  rw [map_factorialInverse p hp hA hB f (by omega : ij.1 < p),
    map_factorialInverse p hp hA hB f (by omega : ij.2 < p)]

private lemma primeGamma_comp_prime {A : Type*} [CommRing A] {I : Ideal A}
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    (δ : I → I) (m : ℕ) (x : I) :
    primeGamma p hp hA δ m (δ x) =
      (Nat.uniformBell m p : A) * primeGamma p hp hA δ (m * p) x := by
  rw [primeGamma_digit_rec p hp hA δ (m * p)]
  simp only [Nat.mul_div_left _ hp.pos, Nat.mul_mod_left, pow_zero, mul_one]
  unfold digitCoefficientInverse
  have he : digitCoefficient p m 0 = Nat.uniformBell m p := by simp [digitCoefficient]
  rw [← mul_assoc]
  have hinv : (Nat.uniformBell m p : A) *
      ↑(hA (digitCoefficient p m 0) (digitCoefficient_not_dvd hp hp.pos)).unit⁻¹ = 1 := by
    simpa only [IsUnit.unit_spec, he] using
      Units.mul_inv (hA (digitCoefficient p m 0) (digitCoefficient_not_dvd hp hp.pos)).unit
  rw [hinv, one_mul]

private lemma map_dpow_eq_primeGamma {A B : Type*} [CommRing A] [CommRing B]
    {I : Ideal A} {J : Ideal B} (p : ℕ) (hp : p.Prime)
    (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A)) (δ : I → I)
    (factorial_mul : ∀ z : I, (p.factorial : A) * (δ z : A) = (z : A) ^ p)
    (D : _root_.DividedPowers J) (f : B →+* A)
    (hf : ∀ z ∈ J, f z ∈ I)
    (hfδ : ∀ (z : B) (hz : z ∈ J), f (D.dpow p z) = δ ⟨f z, hf z hz⟩)
    (n : ℕ) (z : B) (hz : z ∈ J) :
    f (D.dpow n z) = primeGamma p hp hA δ n ⟨f z, hf z hz⟩ := by
  induction n using Nat.strong_induction_on generalizing z with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      simp [D.dpow_zero hz, primeGamma]
    by_cases hd : p ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm : m < p * m := by
        have : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp.two_le
        have : m ≠ 0 := by rintro rfl; simp at hn0
        omega
      apply (hA (Nat.uniformBell m p) (uniformBell_not_dvd hp)).mul_left_cancel
      have hc := congrArg f (D.dpow_comp (m := m) hp.ne_zero hz)
      simp only [map_mul, map_natCast] at hc
      rw [← Nat.mul_comm m p, ← hc, ih m hm _ (D.dpow_mem hp.ne_zero hz)]
      have he : (⟨f (D.dpow p z), hf _ (D.dpow_mem hp.ne_zero hz)⟩ : I) =
          δ ⟨f z, hf z hz⟩ := Subtype.ext (hfδ z hz)
      rw [he, primeGamma_comp_prime]
    · apply (hA n hd).mul_left_cancel
      have hn : n - 1 + 1 = n := by omega
      have hc : n.choose (n - 1) = n := by
        rw [Nat.choose_symm (by omega)]
        simp
      have hD := congrArg f (D.mul_dpow (m := n - 1) (n := 1) hz)
      rw [D.dpow_one hz, hn, hc] at hD
      simp only [map_mul, map_natCast] at hD
      have hG := primeGamma_mul_dpow p hp hA δ factorial_mul (n - 1) 1
        ⟨f z, hf z hz⟩
      rw [hn, hc] at hG
      simp only [primeGamma] at hG
      simpa only [primeGamma] using hD.symm.trans
        ((congrArg (fun a : A ↦ a * f z) (ih (n - 1) (by omega) z hz)).trans hG)


private lemma map_dpow_prime_of_span {A B : Type*} [CommRing A] [CommRing B]
    {I : Ideal A} {J : Ideal B} (p : ℕ) (hp : p.Prime)
    (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    (hB : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : B)) (δ : I → I)
    (smul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x)
    (add : ∀ x y : I,
      (δ (x + y) : A) = (δ x : A) +
        ∑ ij ∈ (antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0),
          factorialInverse p hp hA ij.1 * factorialInverse p hp hA ij.2 *
            (x : A) ^ ij.1 * (y : A) ^ ij.2 + (δ y : A))
    (D : _root_.DividedPowers J) (f : B →+* A) (hf : ∀ z ∈ J, f z ∈ I)
    (S : Set B) (hS : J = Ideal.span S)
    (hgen : ∀ (z : B) (hz : z ∈ S),
      f (D.dpow p z) = δ ⟨f z, hf z (hS ▸ Ideal.subset_span hz)⟩)
    (z : B) (hz : z ∈ J) : f (D.dpow p z) = δ ⟨f z, hf z hz⟩ := by
  have hzero : δ (0 : I) = 0 := by
    have h := smul 0 (0 : I)
    simpa [zero_pow hp.ne_zero] using h
  have hmem : ∀ z ∈ Ideal.span S, z ∈ J := by rw [hS]; exact fun _ h ↦ h
  have goal : ∀ (z : B) (hz : z ∈ Ideal.span S),
      f (D.dpow p z) = δ ⟨f z, hf z (hmem z hz)⟩ := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact hgen z hz
    | zero =>
      simp only [D.dpow_eval_zero hp.ne_zero, map_zero]
      exact congrArg Subtype.val hzero.symm
    | add z w hz hw ihz ihw =>
      rw [map_dpow_prime_add p hp hA hB D f (hmem z hz) (hmem w hw), ihz, ihw]
      have he : (⟨f (z + w), hf _ (hmem _ (Ideal.add_mem _ hz hw))⟩ : I) =
          ⟨f z, hf z (hmem z hz)⟩ + ⟨f w, hf w (hmem w hw)⟩ :=
        Subtype.ext (map_add f z w)
      rw [he, add]
    | smul a z hz ih =>
      show f (D.dpow p (a * z)) = _
      rw [D.dpow_mul (hmem z hz), map_mul, map_pow, ih]
      have he : (⟨f (a * z), hf _ (hmem _ (Submodule.smul_mem _ a hz))⟩ : I) =
          f a • ⟨f z, hf z (hmem z hz)⟩ := Subtype.ext (map_mul f a z)
      simp only [smul_eq_mul] at *
      rw [he, smul]
      rfl
  exact goal z (hS ▸ hz)


private lemma primeGamma_polynomial_lift {A : Type*} [CommRing A] {I : Ideal A}
    (p : ℕ) (hp : p.Prime) (hA : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : A))
    (δ : I → I)
    (factorial_mul : ∀ z : I, (p.factorial : A) * (δ z : A) = (z : A) ^ p)
    (smul : ∀ (a : A) (x : I), δ (a • x) = a ^ p • δ x)
    (add : ∀ x y : I,
      (δ (x + y) : A) = (δ x : A) +
        ∑ ij ∈ (antidiagonal p).filter (fun ij ↦ ij.1 ≠ 0 ∧ ij.2 ≠ 0),
          factorialInverse p hp hA ij.1 * factorialInverse p hp hA ij.2 *
            (x : A) ^ ij.1 * (y : A) ^ ij.2 + (δ y : A))
    (x : Fin 2 → I) :
    ∃ (J : Ideal (DividedPowerAlgebra A (Fin 2 →₀ A))) (D : _root_.DividedPowers J)
      (f : DividedPowerAlgebra A (Fin 2 →₀ A) →+* A) (hf : ∀ z ∈ J, f z ∈ I)
      (v : Fin 2 → J),
      (∀ i, f (v i) = x i) ∧ ∀ (n : ℕ) (z : DividedPowerAlgebra A (Fin 2 →₀ A))
        (hz : z ∈ J), f (D.dpow n z) = primeGamma p hp hA δ n ⟨f z, hf z hz⟩ := by
  classical
  let P := DividedPowerAlgebra A (Fin 2 →₀ A)
  let R : _root_.DividedPowerRing := .of A ⊥ (dividedPowersBot A)
  let J := dividedPowerPolynomialPositiveIdeal A (Fin 2)
  have hJ : dividedPowerPolynomialIdeal R.ideal (Fin 2) = J := by
    simp [R, J, dividedPowerPolynomialIdeal]
  let D : _root_.DividedPowers J := hJ ▸
    dividedPowerPolynomialDividedPowers R (Fin 2)
  have hcast (K L : Ideal P) (h : K = L) (E : _root_.DividedPowers K) :
      (h ▸ E).dpow = E.dpow := by subst L; rfl
  have hDvar (i : Fin 2) (n : ℕ) :
      D.dpow n (dividedPowerPolynomialVariable A i) =
        dividedPowerPolynomialVariableMonomial A i n := by
    show (hJ ▸ dividedPowerPolynomialDividedPowers R (Fin 2)).dpow n _ = _
    rw [hcast]
    exact dividedPowerPolynomialDividedPowers_dpow_variable R (Fin 2) i n
  let f := (primeGammaPolynomialEval p hp hA δ x factorial_mul).toRingHom
  have hfmon (i : Fin 2) (n : ℕ) :
      f (dividedPowerPolynomialVariableMonomial A i n) =
        primeGamma p hp hA δ n (x i) :=
    primeGammaPolynomialEval_variableMonomial p hp hA δ x factorial_mul i n
  let S : Set P := {z | ∃ (i : Fin 2) (n : ℕ), n ≠ 0 ∧
    z = dividedPowerPolynomialVariableMonomial A i n}
  have hspan : J = Ideal.span S := positiveIdeal_eq_span_variableMonomials A (Fin 2)
  have hf : ∀ z ∈ J, f z ∈ I := by
    show J ≤ I.comap f
    rw [hspan]
    apply Ideal.span_le.mpr
    rintro z ⟨i, n, hn, rfl⟩
    show f (dividedPowerPolynomialVariableMonomial A i n) ∈ I
    rw [hfmon]
    exact primeGamma_mem p hp hA δ n hn (x i)
  have hv (i : Fin 2) : dividedPowerPolynomialVariable A i ∈ J := by
    rw [hspan]
    exact Ideal.subset_span ⟨i, 1, one_ne_zero, rfl⟩
  let v : Fin 2 → J := fun i ↦ ⟨dividedPowerPolynomialVariable A i, hv i⟩
  have hP : ∀ n : ℕ, ¬p ∣ n → IsUnit (n : P) := by
    intro n hn
    simpa using (hA n hn).map (algebraMap A P)
  have hgen (z : P) (hz : z ∈ S) :
      f (D.dpow p z) = δ ⟨f z, hf z (hspan ▸ Ideal.subset_span hz)⟩ := by
    rcases hz with ⟨i, n, hn, rfl⟩
    have he : (⟨f (dividedPowerPolynomialVariableMonomial A i n),
        hf _ (hspan ▸ Ideal.subset_span ⟨i, n, hn, rfl⟩)⟩ : I) =
        ⟨primeGamma p hp hA δ n (x i), primeGamma_mem p hp hA δ n hn (x i)⟩ :=
      Subtype.ext (hfmon i n)
    rw [he, primeGamma_delta_comp p hp hA δ factorial_mul smul n hn]
    rw [← hDvar i n, D.dpow_comp hn (hv i), map_mul, map_natCast,
      hDvar i (p * n), hfmon]
  have hfδ := map_dpow_prime_of_span p hp hA hP δ smul add D f hf S hspan hgen
  refine ⟨J, D, f, hf, v, ?_, ?_⟩
  · intro i
    simpa only [v, dividedPowerPolynomialVariable,
      dividedPowerPolynomialVariableMonomial, primeGamma] using hfmon i 1
  · exact map_dpow_eq_primeGamma p hp hA δ factorial_mul D f hf hfδ

end DividedPowers
