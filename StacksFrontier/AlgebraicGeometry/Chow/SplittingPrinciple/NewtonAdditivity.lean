module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.NewtonPowerSum

/-!
# Newton's recursion as a logarithmic derivative

Let `R` be a ring and let `σ = 1 + c_1 t + c_2 t^2 + ⋯` be a power series over `R`. Newton's
recursion of Stacks 0F9B, `AlgebraicGeometry.newtonPowerSum`, applied to the coefficients of `σ`
with degree-zero term `0`, gives the power sums `P_p(σ)`:

  `P_{p+1} = ∑_{j=0}^{p-1} (-1)^j c_{j+1} P_{p-j} + (-1)^p (p+1) c_{p+1}`.

With the Euler operator `D(∑ a_n t^n) = ∑ n a_n t^n` and `Q(σ) = ∑_{p ≥ 1} (-1)^{p-1} P_p(σ) t^p`,
this recursion says exactly `σ · Q(σ) = D(σ)`: the series `Q(σ)` is the logarithmic derivative
`D(σ)/σ`. This is the form in which the logarithm of a total Chern class is computed
(Stacks 0FAD).

## Main definitions

* `Stacks.Chow.eulerOperator` — `∑ a_n t^n ↦ ∑ n a_n t^n`.
* `Stacks.Chow.newtonSeries` — `Q(σ) = ∑_{p ≥ 1} (-1)^{p-1} P_p(σ) t^p`.

## Main results

* `Stacks.Chow.newtonPowerSum_succ_zsmul` — Newton's recursion with its signs and coefficients
  written as integer multiples.
* `Stacks.Chow.newtonPowerSum_eq_pow_of_rankOne` — for a single Chern root `x` the power sums are
  the powers `x^p`.
* `Stacks.Chow.eulerOperator_mul` — `D` is a derivation.
* `Stacks.Chow.mul_newtonSeries` — `σ · Q(σ) = D(σ)`.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0FAD](https://stacks.math.columbia.edu/tag/0FAD)
-/

@[expose] public noncomputable section

open Finset PowerSeries

namespace Stacks.Chow

/-! ### Newton's recursion with integer multiples -/

section Newton

variable {R : Type*} [Ring R]

/-- **Newton's recursion with integer multiples**: the recursion
`AlgebraicGeometry.newtonPowerSum_succ`, the signs `(-1)^j` and the coefficient `(-1)^p (p + 1)`
being read as integer multiples. -/
theorem newtonPowerSum_succ_zsmul (r : R) (c : ℕ+ → R) (p : ℕ) :
    AlgebraicGeometry.newtonPowerSum r c (p + 1) =
      ∑ j ∈ range p, ((-1 : ℤ) ^ j) •
          (c (Nat.succPNat j) * AlgebraicGeometry.newtonPowerSum r c (p - j)) +
        ((-1 : ℤ) ^ p * (p + 1 : ℤ)) • c (Nat.succPNat p) := by
  rw [AlgebraicGeometry.newtonPowerSum_succ]
  congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, mul_assoc]
  · rw [zsmul_eq_mul]
    push_cast
    rfl

/-- Newton's recursion of the zero family, with degree-zero term `0`, vanishes. -/
theorem newtonPowerSum_zero_family (p : ℕ) :
    AlgebraicGeometry.newtonPowerSum (0 : R) (0 : ℕ+ → R) p = 0 := by
  rcases p with _ | p
  · exact AlgebraicGeometry.newtonPowerSum_zero _ _
  · rw [AlgebraicGeometry.newtonPowerSum_succ]
    simp

/-- Newton's recursion for a single Chern root: if `c₁ = x` and `c_i = 0` for `i ≥ 2`, the
positive power sums are the powers `x^p`. -/
theorem newtonPowerSum_eq_pow_of_rankOne (r x : R) (c : ℕ+ → R)
    (h1 : c 1 = x) (h2 : ∀ i : ℕ+, 2 ≤ (i : ℕ) → c i = 0) :
    ∀ p : ℕ, 0 < p → AlgebraicGeometry.newtonPowerSum r c p = x ^ p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [AlgebraicGeometry.newtonPowerSum_succ]
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp [show Nat.succPNat 0 = 1 from rfl, h1]
    · rw [Finset.sum_eq_single 0, h2 (Nat.succPNat q) (by rw [Nat.succPNat_coe]; omega), mul_zero,
        add_zero, pow_zero, one_mul, show Nat.succPNat 0 = 1 from rfl, h1, Nat.sub_zero,
        ih q (by omega) hq, ← pow_succ']
      · intro j hj hj0
        rw [h2 (Nat.succPNat j) (by rw [Nat.succPNat_coe]; omega), mul_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_range.mpr hq) h

end Newton

/-! ### Coefficientwise commutation of power series -/

section Commute

variable {R : Type*} [Ring R]

/-- An element commuting with every coefficient of `f` and of `g` commutes with every
coefficient of `f * g`. -/
theorem commute_coeff_mul {f g : R⟦X⟧} {x : R} (hf : ∀ i, Commute (coeff i f) x)
    (hg : ∀ i, Commute (coeff i g) x) (n : ℕ) : Commute (coeff n (f * g)) x := by
  rw [coeff_mul]
  exact Commute.sum_left _ _ _ fun y _ ↦ (hf y.1).mul_left (hg y.2)

/-- If `f g = 1` and `f` has constant coefficient `1`, an element commuting with the coefficients
of `f` commutes with those of `g`. -/
theorem commute_coeff_of_mul_eq_one {f g : R⟦X⟧} (hf : constantCoeff f = 1) (hfg : f * g = 1)
    {x : R} (h : ∀ i, Commute (coeff i f) x) (n : ℕ) : Commute (coeff n g) x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := congrArg (coeff n) hfg
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ',
      coeff_zero_eq_constantCoeff_apply, hf, one_mul] at hn
    have hgn : coeff n g = coeff n (1 : R⟦X⟧) -
        ∑ i ∈ range n, coeff (i + 1) f * coeff (n - (i + 1)) g := by
      rw [← hn]; abel
    rw [hgn]
    refine Commute.sub_left ?_ (Commute.sum_left _ _ _ fun i hi ↦ ?_)
    · rw [coeff_one]; split_ifs
      · exact Commute.one_left x
      · exact Commute.zero_left x
    · exact (h _).mul_left (ih _ (by have := mem_range.mp hi; omega))

end Commute

/-! ### The logarithmic derivative -/

section Log

variable {R : Type*} [Ring R]

/-- **The Euler operator** `∑ a_n t^n ↦ ∑ n a_n t^n`. -/
def eulerOperator (f : R⟦X⟧) : R⟦X⟧ := mk fun n ↦ n • coeff n f

/-- The `n`-th coefficient of `eulerOperator f` is `n` times the `n`-th coefficient of `f`. -/
theorem coeff_eulerOperator (f : R⟦X⟧) (n : ℕ) : coeff n (eulerOperator f) = n • coeff n f :=
  coeff_mk _ _

/-- **The Euler operator is a derivation.** -/
theorem eulerOperator_mul (f g : R⟦X⟧) :
    eulerOperator (f * g) = eulerOperator f * g + f * eulerOperator g := by
  ext n
  rw [map_add, coeff_eulerOperator, coeff_mul, coeff_mul, coeff_mul, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [coeff_eulerOperator, coeff_eulerOperator, smul_mul_assoc, mul_smul_comm, ← add_smul, hx]

/-- **The power-sum series** `Q(σ) = ∑_{p ≥ 1} (-1)^{p-1} P_p(σ) t^p` of a power series, the
power sums being taken of its coefficients in positive degree. -/
def newtonSeries (f : R⟦X⟧) : R⟦X⟧ :=
  mk fun m ↦
    ((-1 : ℤ) ^ (m + 1)) • AlgebraicGeometry.newtonPowerSum 0 (fun i : ℕ+ ↦ coeff (i : ℕ) f) m

/-- The `m`-th coefficient of `newtonSeries f` is `(-1)^(m+1)` times the `m`-th Newton power sum
`AlgebraicGeometry.newtonPowerSum 0` of the positive-degree coefficients of `f`. -/
theorem coeff_newtonSeries (f : R⟦X⟧) (m : ℕ) :
    coeff m (newtonSeries f) =
      ((-1 : ℤ) ^ (m + 1)) •
        AlgebraicGeometry.newtonPowerSum 0 (fun i : ℕ+ ↦ coeff (i : ℕ) f) m :=
  coeff_mk _ _

private theorem neg_one_pow_add_neg_one_pow {p j : ℕ} (hj : j < p) :
    (-1 : ℤ) ^ (p + 1 + 1) * (-1) ^ j + (-1) ^ (p - j + 1) = 0 := by
  have h1 : (-1 : ℤ) ^ (p + 1 + 1) * (-1) ^ j = (-1) ^ (p + j) := by
    rw [← pow_add, show p + 1 + 1 + j = p + j + 2 by omega, pow_add]; simp
  have h2 : (-1 : ℤ) ^ (p + j) * (-1) ^ (p - j + 1) = -1 := by
    rw [← pow_add, show p + j + (p - j + 1) = 2 * p + 1 by omega, pow_succ, pow_mul]; simp
  rw [h1]
  rcases neg_one_pow_eq_or ℤ (p + j) with h | h <;> rw [h] at h2 ⊢ <;> linarith

/-- **Newton's recurrence is the logarithmic derivative**: for `σ` with constant coefficient `1`,
`σ · Q(σ) = D(σ)`. -/
theorem mul_newtonSeries {f : R⟦X⟧} (hf : constantCoeff f = 1) :
    f * newtonSeries f = eulerOperator f := by
  ext m
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_eulerOperator]
  dsimp only
  rcases m with _ | p
  · simp [coeff_newtonSeries]
  · simp_rw [coeff_newtonSeries]
    rw [Finset.sum_range_succ, Finset.sum_range_succ', Nat.sub_self,
      AlgebraicGeometry.newtonPowerSum_zero, smul_zero, mul_zero, add_zero,
      coeff_zero_eq_constantCoeff_apply, hf, one_mul, Nat.sub_zero, newtonPowerSum_succ_zsmul,
      smul_add, Finset.smul_sum]
    have hterm : ∀ i ∈ range p, coeff (i + 1) f * (((-1 : ℤ) ^ (p + 1 - (i + 1) + 1)) •
        AlgebraicGeometry.newtonPowerSum 0 (fun i : ℕ+ ↦ coeff (i : ℕ) f) (p + 1 - (i + 1))) +
        ((-1 : ℤ) ^ (p + 1 + 1)) • (((-1 : ℤ) ^ i) • (coeff (Nat.succPNat i : ℕ) f *
          AlgebraicGeometry.newtonPowerSum 0 (fun i : ℕ+ ↦ coeff (i : ℕ) f) (p - i))) = 0 := by
      intro i hi
      have hip := mem_range.mp hi
      rw [show p + 1 - (i + 1) = p - i by omega, Nat.succPNat_coe, mul_smul_comm, smul_smul,
        ← add_smul, add_comm, neg_one_pow_add_neg_one_pow hip, zero_smul]
    rw [← add_assoc, ← Finset.sum_add_distrib, Finset.sum_eq_zero hterm, zero_add, smul_smul,
      Nat.succPNat_coe, show (-1 : ℤ) ^ (p + 1 + 1) * ((-1) ^ p * (p + 1 : ℤ)) = (p + 1 : ℕ) by
        rw [pow_succ, pow_succ]; push_cast; ring_nf; rw [mul_comm p 2, pow_mul, neg_one_sq,
            one_pow]; ring]
    exact natCast_zsmul _ _

end Log

end Stacks.Chow

end
