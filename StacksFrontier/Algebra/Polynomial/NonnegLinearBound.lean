module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Instances.Rat

/-!
# Nonnegative polynomials with a linear bound on the negative axis vanish

A polynomial which is nonnegative at every integer, vanishes at `0`, and satisfies a linear
upper bound `P(-n) ≤ c * n` on the negative integers is zero.

This is the final, purely algebraic step of Stacks Tag 0F2B. There `P` records the Euler
characteristics `P(n) = χ(n)` of the twists of a coherent triple: the geometry supplies
nonnegativity at every integer, the vanishing at `0`, and the linear bound on the negative
axis, and this file turns those three facts into `P = 0`.

The argument runs on `T(X) = P(-X)`, so that both hypotheses become statements about the
values of a polynomial at the natural numbers: `0 ≤ T(n)` and `T(n) ≤ c * n`. A polynomial of
positive degree whose values at the naturals are all nonnegative must have positive leading
coefficient, since otherwise it tends to `-∞` along `atTop`. Applying that to `T` gives
`0 < T.leadingCoeff`, and applying it to `C c * X - T` — nonnegative at the naturals by the
linear bound — would give `0 < -T.leadingCoeff` as soon as `2 ≤ T.natDegree`, because then the
subtracted `C c * X` is of strictly smaller degree and cannot change the leading term. Hence
`T`, and so `P`, is of degree at most one; the two remaining coefficients are pinned down by
the values of `P` at `0`, `1` and `-1`.

## Main results

* `Stacks.Polynomial.leadingCoeff_pos_of_degree_pos_of_forall_eval_natCast_nonneg`: a
  polynomial of positive degree over an archimedean ordered normed field whose values at the
  natural numbers are all nonnegative has positive leading coefficient.
* `Stacks.Polynomial.natDegree_le_one_of_nonneg_of_neg_linear_bound`: a rational polynomial
  which is nonnegative at every integer and bounded by `c * n` at `-n` has degree at most one.
* `Stacks.Polynomial.eq_zero_of_nonneg_of_eval_zero_of_neg_linear_bound`: adding the vanishing
  at `0` to those hypotheses forces the polynomial to be zero.

## Implementation notes

The hypotheses are phrased as `∀ n : ℤ, 0 ≤ P.eval (n : ℚ)` and `∀ n : ℕ, P.eval (-(n : ℚ)) ≤
c * n` rather than through a predicate, because that is the form in which the geometric input of
Tag 0F2B arrives.

The limit lemma `Polynomial.tendsto_atBot_of_leadingCoeff_nonpos` is available over any ordered
normed field with the order topology, so
`leadingCoeff_pos_of_degree_pos_of_forall_eval_natCast_nonneg` is stated at that generality; the
`Archimedean` hypothesis is what lets the naturals exhaust `atTop`. No transfer of `P` to `ℝ` is
needed: `ℚ` carries all four instances.

The reflection `X ↦ -X` is realized as `P.comp (-X)` rather than as a ring automorphism, since
only `Polynomial.eval_comp` and `Polynomial.natDegree_comp` are used. The difference
`C c * X - T` is written as the sum `C c * X + -T`, which is the shape in which
`Polynomial.degree_add_eq_right_of_degree_lt` and `Polynomial.leadingCoeff_add_of_degree_lt`
apply.

## References

* [Stacks Project, Tag 0F2B](https://stacks.math.columbia.edu/tag/0F2B)
-/

@[expose] public section

namespace Stacks.Polynomial

open Filter _root_.Polynomial

/-- A polynomial of positive degree whose values at all the natural numbers are nonnegative has
positive leading coefficient: were the leading coefficient nonpositive, the polynomial would
tend to `-∞` along `atTop`, and the naturals are unbounded. -/
theorem leadingCoeff_pos_of_degree_pos_of_forall_eval_natCast_nonneg {𝕜 : Type*} [NormedField 𝕜]
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜]
    {P : Polynomial 𝕜} (hdeg : 0 < P.degree) (hnonneg : ∀ n : ℕ, 0 ≤ P.eval (n : 𝕜)) :
    0 < P.leadingCoeff := by
  by_contra hlc
  rw [not_lt] at hlc
  have htend : Tendsto (fun n : ℕ => P.eval (n : 𝕜)) atTop atBot :=
    (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hlc).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn⟩ := (htend.eventually (eventually_lt_atBot (0 : 𝕜))).exists
  exact absurd (hnonneg n) (not_le.2 hn)

/-- A rational polynomial which is nonnegative at every integer and satisfies the linear upper
bound `P(-n) ≤ c * n` at every natural number has degree at most one.

Both hypotheses are transported to the reflection `T(X) = P(-X)`, whose values at the naturals
are therefore squeezed between `0` and `c * n`. If `T` had degree at least two, then the leading
coefficients of `T` and of `C c * X - T` — both positive by
`leadingCoeff_pos_of_degree_pos_of_forall_eval_natCast_nonneg` — would be negatives of each
other. -/
theorem natDegree_le_one_of_nonneg_of_neg_linear_bound {P : Polynomial ℚ}
    (hnonneg : ∀ n : ℤ, 0 ≤ P.eval (n : ℚ)) {c : ℚ}
    (hbound : ∀ n : ℕ, P.eval (-(n : ℚ)) ≤ c * n) :
    P.natDegree ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  set T : Polynomial ℚ := P.comp (-X) with hTdef
  have hTeval : ∀ x : ℚ, T.eval x = P.eval (-x) := by
    intro x
    rw [hTdef, eval_comp, eval_neg, eval_X]
  have hTnatDegree : T.natDegree = P.natDegree := by
    rw [hTdef, natDegree_comp, natDegree_neg, natDegree_X, mul_one]
  have hTnonneg : ∀ n : ℕ, 0 ≤ T.eval (n : ℚ) := by
    intro n
    rw [hTeval]
    have := hnonneg (-(n : ℤ))
    push_cast at this
    exact this
  have hTdeg : 0 < T.degree := natDegree_pos_iff_degree_pos.1 (by omega)
  have hTlc : 0 < T.leadingCoeff :=
    leadingCoeff_pos_of_degree_pos_of_forall_eval_natCast_nonneg hTdeg hTnonneg
  have hlt : (C c * X : Polynomial ℚ).degree < (-T).degree := by
    refine degree_lt_degree ?_
    have h1 : (C c * X : Polynomial ℚ).natDegree ≤ 1 :=
      (natDegree_C_mul_le c X).trans (by rw [natDegree_X])
    rw [natDegree_neg]
    omega
  have hUdeg : 0 < (C c * X + -T).degree := by
    rw [degree_add_eq_right_of_degree_lt hlt, degree_neg]
    exact hTdeg
  have hUlc : (C c * X + -T).leadingCoeff = -T.leadingCoeff := by
    rw [leadingCoeff_add_of_degree_lt hlt, leadingCoeff_neg]
  have hUnonneg : ∀ n : ℕ, 0 ≤ (C c * X + -T).eval (n : ℚ) := by
    intro n
    have hb := hbound n
    rw [← hTeval] at hb
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_neg]
    linarith
  have := leadingCoeff_pos_of_degree_pos_of_forall_eval_natCast_nonneg hUdeg hUnonneg
  rw [hUlc] at this
  linarith

/-- **The final step of Stacks Tag 0F2B.** A rational polynomial which is nonnegative at every
integer, vanishes at `0`, and satisfies a linear upper bound `P(-n) ≤ c * n` on the negative
integers is zero.

By `natDegree_le_one_of_nonneg_of_neg_linear_bound` the polynomial is `C a * X + C b`. Then
`b = P(0) = 0`, while `0 ≤ P(1) = a` and `0 ≤ P(-1) = -a` force `a = 0`. -/
theorem eq_zero_of_nonneg_of_eval_zero_of_neg_linear_bound
    {P : Polynomial ℚ} (hnonneg : ∀ n : ℤ, 0 ≤ P.eval (n : ℚ))
    (hzero : P.eval 0 = 0) {c : ℚ}
    (hbound : ∀ n : ℕ, P.eval (-(n : ℚ)) ≤ c * n) :
    P = 0 := by
  obtain ⟨a, b, rfl⟩ :=
    exists_eq_X_add_C_of_natDegree_le_one
      (natDegree_le_one_of_nonneg_of_neg_linear_bound hnonneg hbound)
  have hb : b = 0 := by simpa using hzero
  have h1 := hnonneg 1
  have h2 := hnonneg (-1)
  simp only [Int.cast_one, Int.cast_neg, eval_add, eval_mul, eval_C, eval_X, mul_one,
    mul_neg] at h1 h2
  have ha : a = 0 := by linarith
  rw [ha, hb, map_zero, zero_mul, add_zero]

end Stacks.Polynomial
