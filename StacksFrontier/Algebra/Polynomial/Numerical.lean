module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Numerical polynomials

A polynomial with rational coefficients is *numerical* when it takes an integer value at every
integer. The binomial polynomials `X (X - 1) ⋯ (X - k + 1) / k!` are the basic examples, and
Hilbert functions are eventually given by numerical polynomials.

A function on `ℤ ^ r` whose `r` first differences are all given by rational polynomials of total
degree at most `d` is itself given by a rational polynomial of total degree at most `d + 1`.

## Main definitions

* `Polynomial.IsNumerical`: the polynomial takes integer values at all integers.

## Main results

* `Polynomial.exists_antidifference`: every rational polynomial of degree at most `d` is the
  first difference of one of degree at most `d + 1` vanishing at `0`.
* `MvPolynomial.exists_antidifference_update`: the same in one chosen variable of a
  multivariate polynomial, the antidifference vanishing on the hyperplane where that variable
  is zero.
* `MvPolynomial.exists_eval_update_zero`: substituting `0` for one variable does not raise the
  total degree.
* `MvPolynomial.exists_totalDegree_le_of_forall_fwdDiff`: a function on `ℤ ^ r` whose first
  differences are given by rational polynomials of total degree at most `d` is given by one of
  total degree at most `d + 1`.
* `MvPolynomial.eq_of_eval_intCast_eq`: a rational multivariate polynomial in finitely many
  variables is determined by its values at integer points.
* `MvPolynomial.sum_neg_one_pow_mul_eval_indicator_eq_coeff_one`: for a polynomial in `d`
  variables of total degree at most `d`, the alternating sum of its values at the indicator
  functions of the subsets of `Fin d` is the coefficient of the squarefree monomial
  `n₁ ⋯ n_d`.
* `MvPolynomial.exists_int_coeff_one_of_totalDegree_le`: a numerical polynomial in `d` variables
  of total degree at most `d` has an integral coefficient of `n₁ ⋯ n_d`.

## References

* [Stacks Project, Tag 027X](https://stacks.math.columbia.edu/tag/027X)
* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
-/

namespace Polynomial

/-- A polynomial over `ℚ` is numerical if it takes an integer value at every integer. -/
@[stacks 027X]
public abbrev IsNumerical (f : Polynomial ℚ) : Prop :=
  ∀ n : ℤ, ∃ m : ℤ, f.eval (n : ℚ) = (m : ℚ)

/-- The first difference of the falling factorial of length `n + 1` is `n + 1` times the falling
factorial of length `n`. -/
public theorem eval_descPochhammer_succ_sub (n : ℕ) (x : ℚ) :
    (descPochhammer ℚ (n + 1)).eval (x + 1) - (descPochhammer ℚ (n + 1)).eval x
      = (n + 1) * (descPochhammer ℚ n).eval x := by
  have h1 : (descPochhammer ℚ (n + 1)).eval (x + 1) = (x + 1) * (descPochhammer ℚ n).eval x := by
    rw [descPochhammer_succ_left (R := ℚ) n]
    simp [eval_comp]
  rw [h1, descPochhammer_succ_eval]
  ring

/-- Every rational polynomial of degree at most `d` is the first difference of a rational
polynomial of degree at most `d + 1` which vanishes at `0`. -/
public theorem exists_antidifference (d : ℕ) : ∀ p : Polynomial ℚ, p.natDegree ≤ d →
    ∃ P : Polynomial ℚ, P.natDegree ≤ d + 1 ∧ P.eval 0 = 0 ∧
      ∀ x : ℚ, P.eval (x + 1) - P.eval x = p.eval x := by
  induction d with
  | zero =>
    intro p hp
    refine ⟨C (p.coeff 0) * X, ?_, by simp, fun x => ?_⟩
    · simpa using (natDegree_C_mul_le _ _).trans (by simp)
    · rw [eq_C_of_natDegree_le_zero hp]; simp; ring
  | succ d ih =>
    intro p hp
    set c : ℚ := p.coeff (d + 1) with hc
    have hd2 : ((d : ℚ) + 1 + 1) ≠ 0 := by positivity
    set γ : ℚ := c / ((d : ℚ) + 1 + 1) with hγdef
    have hγ : γ * ((d : ℚ) + 1 + 1) = c := div_mul_cancel₀ _ hd2
    set P₀ : Polynomial ℚ := C γ * descPochhammer ℚ (d + 2) with hP0
    set q : Polynomial ℚ := p - C c * descPochhammer ℚ (d + 1) with hq
    have hcoeff : (descPochhammer ℚ (d + 1)).coeff (d + 1) = 1 := by
      have := (monic_descPochhammer ℚ (d + 1)).leadingCoeff
      rwa [Polynomial.leadingCoeff, descPochhammer_natDegree] at this
    have hqdeg : q.natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm) with h | h
      · rw [hq]
        simp only [coeff_sub, coeff_C_mul, ← h, hcoeff, mul_one, hc, sub_self]
      · have h1 : p.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega))
        have h2 : (C c * descPochhammer ℚ (d + 1)).coeff m = 0 := by
          refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ (show d + 1 < m by omega))
          exact (natDegree_C_mul_le _ _).trans (by simp)
        rw [hq]; simp [h1, h2]
    obtain ⟨P₁, hP₁deg, hP₁zero, hP₁⟩ := ih q hqdeg
    refine ⟨P₀ + P₁, ?_, ?_, fun x => ?_⟩
    · refine (natDegree_add_le _ _).trans (max_le ?_ (by omega))
      exact (natDegree_C_mul_le _ _).trans (by simp)
    · simp [hP0, hP₁zero, descPochhammer_ne_zero_eval_zero]
    · have hdp := eval_descPochhammer_succ_sub (d + 1) x
      rw [show (d : ℕ) + 1 + 1 = d + 2 from by omega] at hdp
      push_cast at hdp
      have hD : P₀.eval (x + 1) - P₀.eval x = c * (descPochhammer ℚ (d + 1)).eval x := by
        rw [hP0]
        simp only [eval_mul, eval_C]
        rw [← mul_sub, hdp, ← mul_assoc, hγ]
      have hQ : q.eval x = p.eval x - c * (descPochhammer ℚ (d + 1)).eval x := by
        rw [hq]; simp
      simp only [eval_add]
      linarith [hD, hP₁ x, hQ]

end Polynomial

namespace MvPolynomial

variable {r : ℕ}

/-- Two functions on `ℤ` with the same first difference and the same value at `0` agree. -/
private theorem int_eq_of_fwdDiff_eq {g h : ℤ → ℚ} (h0 : g 0 = h 0)
    (hd : ∀ t : ℤ, g (t + 1) - g t = h (t + 1) - h t) (t : ℤ) : g t = h t := by
  induction t using Int.induction_on with
  | zero => exact h0
  | succ k ih => linarith [hd (k : ℤ)]
  | pred k ih =>
      have := hd (-(k : ℤ) - 1)
      rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) from by omega] at this
      linarith

/-- Casting an updated integer point to `ℚ` is updating the cast point. -/
private theorem intCast_update (n : Fin r → ℤ) (i : Fin r) (t : ℤ) :
    (fun j => ((Function.update n i t j : ℤ) : ℚ))
      = Function.update (fun j => (n j : ℚ)) i (t : ℚ) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

/-- Evaluating a one-variable polynomial substituted into the variable `i`. -/
private theorem eval_aeval_X {i : Fin r} (p : Polynomial ℚ) (v : Fin r → ℚ) :
    eval v (Polynomial.aeval (X i : MvPolynomial (Fin r) ℚ) p) = p.eval (v i) := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.eval_eq_sum_range]; simp

/-- A multivariate polynomial evaluates to the sum of the evaluations of its monomials. -/
private theorem eval_eq_sum_support_monomial (q : MvPolynomial (Fin r) ℚ) (v : Fin r → ℚ) :
    eval v q = ∑ a ∈ q.support, eval v (monomial a (coeff a q)) := by
  conv_lhs => rw [q.as_sum]
  rw [map_sum]

/-- Substituting a one-variable polynomial into a single variable does not raise the total
degree above the degree of that polynomial. -/
private theorem totalDegree_aeval_X_le {i : Fin r} (p : Polynomial ℚ) :
    (Polynomial.aeval (X i : MvPolynomial (Fin r) ℚ) p).totalDegree ≤ p.natDegree := by
  rw [Polynomial.aeval_eq_sum_range]
  refine (totalDegree_finsetSum _ _).trans ?_
  simp only [Finset.sup_le_iff, Finset.mem_range]
  intro j hj
  exact (totalDegree_smul_le _ _).trans (by rw [totalDegree_X_pow]; omega)

/-- Erasing one entry of an exponent vector lowers its total weight by that entry. -/
private theorem sum_erase_add_apply (i : Fin r) (a : Fin r →₀ ℕ) :
    (a.erase i).sum (fun _ e => e) + a i = a.sum (fun _ e => e) := by
  rw [add_comm]; exact Finsupp.add_sum_erase' a i (fun _ e => e) (fun _ => rfl)

/-- Splitting one variable off a monomial. -/
private theorem monomial_eq_X_pow_mul_erase (i : Fin r) (a : Fin r →₀ ℕ) (c : ℚ) :
    (monomial a c : MvPolynomial (Fin r) ℚ) = X i ^ a i * monomial (a.erase i) c := by
  rw [← Finsupp.single_add_erase i a, X_pow_eq_monomial, monomial_mul_monomial]; simp

/-- A monomial not involving the variable `i` does not see an update at `i`. -/
private theorem eval_update_monomial (i : Fin r) (b : Fin r →₀ ℕ) (c : ℚ) (hb : b i = 0)
    (v : Fin r → ℚ) (y : ℚ) :
    eval (Function.update v i y) (monomial b c) = eval v (monomial b c) := by
  simp only [eval_monomial]
  congr 1
  refine Finsupp.prod_congr fun j hj => ?_
  have : j ≠ i := by rintro rfl; simp [hb] at hj
  simp [Function.update_of_ne this]

/-- Every multivariate rational polynomial of total degree at most `d` is the first difference,
in any one chosen variable, of one of total degree at most `d + 1` which vanishes on the
hyperplane where that variable is zero. -/
public theorem exists_antidifference_update (i : Fin r) (d : ℕ) (q : MvPolynomial (Fin r) ℚ)
    (hq : q.totalDegree ≤ d) :
    ∃ G : MvPolynomial (Fin r) ℚ, G.totalDegree ≤ d + 1 ∧
      (∀ v : Fin r → ℚ, v i = 0 → eval v G = 0) ∧
      ∀ v : Fin r → ℚ, eval (Function.update v i (v i + 1)) G - eval v G = eval v q := by
  classical
  choose A hAdeg hAzero hAdiff using
    fun k : ℕ => Polynomial.exists_antidifference k (Polynomial.X ^ k) (by simp)
  refine ⟨∑ a ∈ q.support,
      Polynomial.aeval (X i : MvPolynomial (Fin r) ℚ) (A (a i)) *
        monomial (a.erase i) (coeff a q), ?_, ?_, ?_⟩
  · refine (totalDegree_finsetSum _ _).trans ?_
    simp only [Finset.sup_le_iff]
    intro a ha
    refine (totalDegree_mul _ _).trans ?_
    have h1 := (totalDegree_aeval_X_le (i := i) (A (a i))).trans (hAdeg (a i))
    have h2 : (monomial (a.erase i) (coeff a q) : MvPolynomial (Fin r) ℚ).totalDegree
        ≤ (a.erase i).sum (fun _ e => e) := totalDegree_monomial_le _ _
    have h3 : (a.sum fun _ e => e) ≤ d := (le_totalDegree ha).trans hq
    have h4 := sum_erase_add_apply i a
    omega
  · intro v hv
    rw [map_sum]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [map_mul, eval_aeval_X, hv, hAzero, zero_mul]
  · intro v
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib, eval_eq_sum_support_monomial q v]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [map_mul, map_mul, eval_aeval_X, eval_aeval_X, Function.update_self,
      eval_update_monomial i _ _ (by simp) v _, monomial_eq_X_pow_mul_erase i a (coeff a q),
      map_mul, map_pow, eval_X, ← sub_mul, hAdiff]
    simp

/-- Substituting `0` for one variable of a multivariate rational polynomial does not raise its
total degree. -/
public theorem exists_eval_update_zero (i₀ : Fin r) (p : MvPolynomial (Fin r) ℚ) :
    ∃ p' : MvPolynomial (Fin r) ℚ, p'.totalDegree ≤ p.totalDegree ∧
      ∀ v : Fin r → ℚ, eval v p' = eval (Function.update v i₀ 0) p := by
  classical
  refine ⟨∑ a ∈ p.support.filter (fun a => a i₀ = 0), monomial a (coeff a p), ?_, ?_⟩
  · refine (totalDegree_finsetSum _ _).trans ?_
    simp only [Finset.sup_le_iff, Finset.mem_filter]
    intro a ha
    exact (totalDegree_monomial_le a (coeff a p)).trans (le_totalDegree ha.1)
  · intro v
    rw [map_sum, eval_eq_sum_support_monomial p, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · exact (eval_update_monomial i₀ a _ h v 0).symm
    · rw [eval_monomial, Finsupp.prod,
        Finset.prod_eq_zero (Finsupp.mem_support_iff.2 h) (by simp [h]), mul_zero]

/-- A function depending only on the coordinates in `s`, whose first difference in each
direction of `s` is given by a polynomial of total degree at most `d`, is given by a polynomial
of total degree at most `d + 1`. -/
private theorem exists_aux (d : ℕ) :
    ∀ (s : Finset (Fin r)) (f : (Fin r → ℤ) → ℚ) (Q : Fin r → MvPolynomial (Fin r) ℚ),
      (∀ i, (Q i).totalDegree ≤ d) →
      (∀ i ∈ s, ∀ n : Fin r → ℤ, eval (fun j => (n j : ℚ)) (Q i)
          = f (Function.update n i (n i + 1)) - f n) →
      (∀ n m : Fin r → ℤ, (∀ i ∈ s, n i = m i) → f n = f m) →
      ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ d + 1 ∧
        ∀ n : Fin r → ℤ, eval (fun j => (n j : ℚ)) P = f n := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro f Q _ _ hdep
    exact ⟨C (f 0), by simp, fun n => by rw [eval_C]; exact hdep 0 n (by simp)⟩
  | insert i₀ s' hi₀ ih =>
    intro f Q hdeg hQ hdep
    obtain ⟨G, hGdeg, hGzero, hGdiff⟩ := exists_antidifference_update i₀ d (Q i₀) (hdeg i₀)
    choose R hRdeg hReval using fun i => exists_eval_update_zero i₀ (Q i)
    set φ : (Fin r → ℤ) → ℚ := fun n => f (Function.update n i₀ 0) with hφ
    have hcast0 : ∀ n : Fin r → ℤ, (fun j => ((Function.update n i₀ (0 : ℤ) j : ℤ) : ℚ))
        = Function.update (fun j => (n j : ℚ)) i₀ 0 := by
      intro n; rw [intCast_update]; norm_num
    have hφconst : ∀ (n : Fin r → ℤ) (t : ℤ), φ (Function.update n i₀ t) = φ n := fun n t => by
      simp only [hφ, Function.update_idem]
    have hne : ∀ i ∈ s', i ≠ i₀ := fun i hi h => hi₀ (h ▸ hi)
    have hRQ : ∀ i ∈ s', ∀ n : Fin r → ℤ, eval (fun j => (n j : ℚ)) (R i)
        = φ (Function.update n i (n i + 1)) - φ n := by
      intro i hi n
      simp only [hφ]
      rw [hReval, ← hcast0 n, hQ i (Finset.mem_insert_of_mem hi) (Function.update n i₀ 0),
        Function.update_of_ne (hne i hi), Function.update_comm (hne i hi)]
    have hφdep : ∀ n m : Fin r → ℤ, (∀ i ∈ s', n i = m i) → φ n = φ m := by
      intro n m hnm
      simp only [hφ]
      refine hdep _ _ fun i hi => ?_
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · simp
      · rw [Function.update_of_ne (hne i hi'), Function.update_of_ne (hne i hi')]
        exact hnm i hi'
    obtain ⟨Φ, hΦdeg, hΦ⟩ := ih φ R (fun i => (hRdeg i).trans (hdeg i)) hRQ hφdep
    refine ⟨G + Φ, (totalDegree_add _ _).trans (by omega), fun n => ?_⟩
    have h0 : eval (fun j => ((Function.update n i₀ (0 : ℤ) j : ℤ) : ℚ)) (G + Φ)
        = f (Function.update n i₀ (0 : ℤ)) := by
      simp only [map_add]
      rw [hGzero _ (by simp), hΦ, hφconst, hφ, zero_add]
    have hstep : ∀ t : ℤ,
        eval (fun j => ((Function.update n i₀ (t + 1) j : ℤ) : ℚ)) (G + Φ)
          - eval (fun j => ((Function.update n i₀ t j : ℤ) : ℚ)) (G + Φ)
          = f (Function.update n i₀ (t + 1)) - f (Function.update n i₀ t) := by
      intro t
      have hv : (fun j => ((Function.update n i₀ (t + 1) j : ℤ) : ℚ))
          = Function.update (fun j => ((Function.update n i₀ t j : ℤ) : ℚ)) i₀
            ((fun j => ((Function.update n i₀ t j : ℤ) : ℚ)) i₀ + 1) := by
        rw [intCast_update, intCast_update]
        simp
      have hG : eval (fun j => ((Function.update n i₀ (t + 1) j : ℤ) : ℚ)) G
          - eval (fun j => ((Function.update n i₀ t j : ℤ) : ℚ)) G
          = eval (fun j => ((Function.update n i₀ t j : ℤ) : ℚ)) (Q i₀) := by
        rw [hv]; exact hGdiff _
      have hQ0 : eval (fun j => ((Function.update n i₀ t j : ℤ) : ℚ)) (Q i₀)
          = f (Function.update n i₀ (t + 1)) - f (Function.update n i₀ t) := by
        rw [hQ i₀ (Finset.mem_insert_self _ _) (Function.update n i₀ t)]
        simp only [Function.update_self, Function.update_idem]
      have hΦ1 : eval (fun j => ((Function.update n i₀ (t + 1) j : ℤ) : ℚ)) Φ
          = eval (fun j => ((Function.update n i₀ t j : ℤ) : ℚ)) Φ := by
        rw [hΦ, hΦ, hφconst, hφconst]
      simp only [map_add]
      linarith
    simpa using int_eq_of_fwdDiff_eq
      (g := fun t : ℤ => eval (fun j => ((Function.update n i₀ t j : ℤ) : ℚ)) (G + Φ))
      (h := fun t : ℤ => f (Function.update n i₀ t)) h0 hstep (n i₀)

/-- If every first difference of a function
on `ℤ ^ r` is given by a rational polynomial of total degree at most `d`, then the function
itself is given by a rational polynomial of total degree at most `d + 1`. -/
public theorem exists_totalDegree_le_of_forall_fwdDiff (d : ℕ) (f : (Fin r → ℤ) → ℚ)
    (Q : Fin r → MvPolynomial (Fin r) ℚ) (hdeg : ∀ i, (Q i).totalDegree ≤ d)
    (hQ : ∀ (i : Fin r) (n : Fin r → ℤ), eval (fun j => (n j : ℚ)) (Q i)
      = f (Function.update n i (n i + 1)) - f n) :
    ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ d + 1 ∧
      ∀ n : Fin r → ℤ, eval (fun j => (n j : ℚ)) P = f n :=
  exists_aux d Finset.univ f Q hdeg (fun i _ => hQ i)
    fun _ _ h => congrArg f (_root_.funext fun i => h i (Finset.mem_univ i))

/-- A rational polynomial in finitely many variables is determined by its values at the integer
points. -/
@[sga "6 V 2.6" "partial"]
public theorem eq_of_eval_intCast_eq {P Q : MvPolynomial (Fin r) ℚ}
    (h : ∀ n : Fin r → ℤ, eval (fun j => (n j : ℚ)) P = eval (fun j => (n j : ℚ)) Q) : P = Q := by
  refine funext_set (fun _ => Set.range (Int.cast : ℤ → ℚ)) (fun _ => ?_) ?_
  · exact Set.infinite_range_of_injective fun a b hab => by exact_mod_cast hab
  · intro x hx
    choose n hn using fun j => hx j (Set.mem_univ j)
    obtain rfl : x = fun j => ((n j : ℤ) : ℚ) := _root_.funext fun j => (hn j).symm
    exact h n

/-- For a polynomial `P` in `d` variables of total degree at most `d`, the alternating sum
`∑_{S ⊆ Fin d} (-1)^{d - |S|} P(1_S)` of the values of `P` at the indicator functions of the
subsets of `Fin d` is the coefficient of the squarefree monomial `n₁ ⋯ n_d`. -/
public theorem sum_neg_one_pow_mul_eval_indicator_eq_coeff_one {d : ℕ}
    (P : MvPolynomial (Fin d) ℚ) (hP : P.totalDegree ≤ d) :
    ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        eval (fun j => if j ∈ S then (1 : ℚ) else 0) P =
      P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) := by
  classical
  have hprod : ∀ (S : Finset (Fin d)) (a : Fin d →₀ ℕ),
      (∏ j, (if j ∈ S then (1 : ℚ) else 0) ^ a j) = if a.support ⊆ S then 1 else 0 := by
    intro S a
    by_cases h : a.support ⊆ S
    · rw [ite_eq_left h]
      refine Finset.prod_eq_one fun j _ => ?_
      by_cases hj : j ∈ S
      · rw [ite_eq_left hj, one_pow]
      · rw [Finsupp.notMem_support_iff.mp fun h' => hj (h h'), pow_zero]
    · rw [ite_eq_right h]
      obtain ⟨j, hj, hjS⟩ := Finset.not_subset.1 h
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [ite_eq_right hjS, zero_pow (Finsupp.mem_support_iff.1 hj)]
  have hpow : ∀ T : Finset (Fin d),
      ∑ U ∈ T.powerset, (-1 : ℚ) ^ U.card = if T = ∅ then 1 else 0 := by
    intro T
    by_cases hT : T = ∅
    · subst hT; simp
    · rw [ite_eq_right hT]
      exact_mod_cast Finset.sum_powerset_neg_one_pow_card_of_nonempty
        (Finset.nonempty_iff_ne_empty.2 hT)
  have hinner : ∀ T : Finset (Fin d),
      ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) * (if T ⊆ S then 1 else 0) =
        if T = Finset.univ then 1 else 0 := by
    intro T
    have hstep : ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) * (if T ⊆ S then 1 else 0) =
        ∑ U : Finset (Fin d), (-1 : ℚ) ^ U.card * (if U ⊆ Tᶜ then 1 else 0) := by
      refine Fintype.sum_bijective (fun S : Finset (Fin d) => Sᶜ)
        (Function.Involutive.bijective fun S => compl_compl S) _ _ fun S => ?_
      have hcard : (Sᶜ).card = d - S.card := by
        rw [Finset.card_compl, Fintype.card_fin]
      simp only [hcard, Finset.compl_subset_compl]
    have hfilter : (Finset.univ.filter fun U : Finset (Fin d) => U ⊆ Tᶜ) = Tᶜ.powerset := by
      ext; simp
    calc ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) * (if T ⊆ S then 1 else 0)
        = ∑ U : Finset (Fin d), (-1 : ℚ) ^ U.card * (if U ⊆ Tᶜ then 1 else 0) := hstep
      _ = ∑ U ∈ Finset.univ.filter fun U : Finset (Fin d) => U ⊆ Tᶜ, (-1 : ℚ) ^ U.card := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun U _ => by split_ifs <;> simp
      _ = ∑ U ∈ Tᶜ.powerset, (-1 : ℚ) ^ U.card := by rw [hfilter]
      _ = if Tᶜ = ∅ then 1 else 0 := hpow _
      _ = if T = Finset.univ then 1 else 0 := by
          simp [Finset.compl_eq_empty_iff]
  have hsuppOne :
      (Finsupp.equivFunOnFinite.symm fun _ : Fin d => (1 : ℕ)).support = Finset.univ := by
    ext j
    simp
  have hone : ∀ a ∈ P.support, a.support = Finset.univ →
      a = Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1 := by
    intro a ha hsupp
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin d)), 1 ≤ a j := by
      intro j _
      have hj : j ∈ a.support := by rw [hsupp]; exact Finset.mem_univ j
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hj)
    have hsum : ∑ j : Fin d, a j ≤ d := by
      have h := (le_totalDegree ha).trans hP
      rwa [Finsupp.sum, hsupp] at h
    have hconst : ∑ _j : Fin d, (1 : ℕ) = d := by simp
    have key : ∀ j : Fin d, a j = 1 := by
      intro j
      rcases Nat.lt_or_ge (a j) 2 with h | h
      · have := hle j (Finset.mem_univ j)
        omega
      · exfalso
        have hlt : ∑ _j : Fin d, (1 : ℕ) < ∑ j : Fin d, a j :=
          Finset.sum_lt_sum hle ⟨j, Finset.mem_univ j, by omega⟩
        omega
    refine Finsupp.ext fun j => ?_
    rw [key j, Finsupp.coe_equivFunOnFinite_symm]
  calc ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
          eval (fun j => if j ∈ S then (1 : ℚ) else 0) P
      = ∑ S : Finset (Fin d), ∑ a ∈ P.support,
          P.coeff a * ((-1 : ℚ) ^ (d - S.card) * (if a.support ⊆ S then 1 else 0)) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [eval_eq', Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hprod S a]
        ring
    _ = ∑ a ∈ P.support, P.coeff a *
          ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) * (if a.support ⊆ S then 1 else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ a ∈ P.support, P.coeff a * (if a.support = Finset.univ then 1 else 0) :=
        Finset.sum_congr rfl fun a _ => by rw [hinner a.support]
    _ = ∑ a ∈ P.support,
          if a = Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1 then P.coeff a else 0 := by
        refine Finset.sum_congr rfl fun a ha => ?_
        by_cases hsupp : a.support = Finset.univ
        · rw [ite_eq_left hsupp, mul_one, ite_eq_left (hone a ha hsupp)]
        · have hne : a ≠ Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1 := fun hEq =>
            hsupp (by rw [hEq]; exact hsuppOne)
          rw [ite_eq_right hsupp, mul_zero, ite_eq_right hne]
    _ = P.coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1) := by
        rw [Finset.sum_ite_eq' P.support (Finsupp.equivFunOnFinite.symm fun _ : Fin d => 1)
          fun a => P.coeff a]
        by_cases hmem :
            (Finsupp.equivFunOnFinite.symm fun _ : Fin d => (1 : ℕ)) ∈ P.support
        · rw [ite_eq_left hmem]
        · rw [ite_eq_right hmem, notMem_support_iff.mp hmem]

/-- If a rational polynomial `P` in `d` variables of total degree at most `d` takes an integer
value at every integer point, then its coefficient of the squarefree monomial `n₁ ⋯ n_d` is an
integer. -/
public theorem exists_int_coeff_one_of_totalDegree_le {d : ℕ} (P : MvPolynomial (Fin d) ℚ)
    (hdeg : P.totalDegree ≤ d)
    (hint : ∀ n : Fin d → ℤ, ∃ m : ℤ, eval (fun j => (n j : ℚ)) P = (m : ℚ)) :
    ∃ m : ℤ, P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) = (m : ℚ) := by
  classical
  choose m hm using hint
  refine ⟨∑ S : Finset (Fin d), (-1 : ℤ) ^ (d - S.card) *
    m fun j => if j ∈ S then 1 else 0, ?_⟩
  rw [← sum_neg_one_pow_mul_eval_indicator_eq_coeff_one P hdeg]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  have h := hm fun j => if j ∈ S then (1 : ℤ) else 0
  rw [show (fun j : Fin d => (((if j ∈ S then (1 : ℤ) else 0) : ℤ) : ℚ)) =
      fun j : Fin d => if j ∈ S then (1 : ℚ) else 0 from
    _root_.funext fun j => by split_ifs <;> simp] at h
  rw [h]

end MvPolynomial
