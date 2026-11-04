module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernRootPowerSums

/-!
# Newton's recursion of Stacks 0F9B evaluated in a ring that is not commutative

The universal power-sum polynomials `P_p` of [Stacks, Tag 0F9B] are
`AlgebraicGeometry.powerSumPolynomial`, and `AlgebraicGeometry.powerSumOfChernClasses` evaluates
them at a rank and a family of Chern classes in a commutative ring. In an arbitrary ring `A`,
given a degree-zero term `r` and a family `c` indexed by the positive integers,
`AlgebraicGeometry.newtonPowerSum` is the family defined by `P_0 = r` and Newton's recursion

  `P_{p+1} = ∑_{j < p} (-1)^j c_{j+1} P_{p-j} + (-1)^p (p + 1) c_{p+1}`,

in which every product has a Chern class on the left. Over a commutative ring, with `r` the image
of the rank, it agrees with `AlgebraicGeometry.powerSumOfChernClasses` in every degree.

## Main definitions

* `AlgebraicGeometry.newtonPowerSum`: Newton's recursion of Stacks 0F9B in an arbitrary ring.

## Main results

* `AlgebraicGeometry.newtonPowerSum_zero`, `AlgebraicGeometry.newtonPowerSum_succ`: the
  degree-zero term and the recursion.
* `AlgebraicGeometry.newtonPowerSum_eq_of_pos`: in positive degrees the degree-zero term does
  not enter.
* `AlgebraicGeometry.newtonPowerSum_eq_chernClassEval`: in positive degrees, and over a
  commutative ring, the recursion computes the evaluation of `P_p` at the Chern classes; the
  degree-zero term does not enter.
* `AlgebraicGeometry.map_newtonPowerSum`: a ring homomorphism commutes with the recursion.
* `AlgebraicGeometry.newtonPowerSum_eq_powerSumOfChernClasses`: over a commutative ring the
  recursion is `AlgebraicGeometry.powerSumOfChernClasses`, in every degree.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open MvPolynomial

/-- **Newton's recursion of Stacks 0F9B, read in an arbitrary ring.** Given a degree-zero term
`r` — the rank variable of Stacks 0F9B — and a family `c` of Chern classes indexed by the
positive integers, this is the family `P_p` defined by `P_0 = r` and

  `P_{p+1} = ∑_{j < p} (-1)^j c_{j+1} P_{p-j} + (-1)^p (p + 1) c_{p+1}`. -/
def newtonPowerSum {A : Type*} [Ring A] (r : A) (c : ℕ+ → A) : ℕ → A
  | 0 => r
  | p + 1 =>
      (∑ j ∈ Finset.range p,
          (-1 : A) ^ j * c (Nat.succPNat j) * newtonPowerSum r c (p - j)) +
        (-1 : A) ^ p * ((p : A) + 1) * c (Nat.succPNat p)
termination_by p => p
decreasing_by all_goals exact Nat.lt_succ_of_le (Nat.sub_le _ _)

variable {A : Type*}

/-- The degree-zero member of the family is the given degree-zero term, the rank variable of
Stacks 0F9B. -/
@[simp]
theorem newtonPowerSum_zero [Ring A] (r : A) (c : ℕ+ → A) : newtonPowerSum r c 0 = r := by
  rw [newtonPowerSum]

/-- Newton's recursion for `AlgebraicGeometry.newtonPowerSum`. -/
theorem newtonPowerSum_succ [Ring A] (r : A) (c : ℕ+ → A) (p : ℕ) :
    newtonPowerSum r c (p + 1) =
      (∑ j ∈ Finset.range p,
          (-1 : A) ^ j * c (Nat.succPNat j) * newtonPowerSum r c (p - j)) +
        (-1 : A) ^ p * ((p : A) + 1) * c (Nat.succPNat p) := by
  rw [newtonPowerSum]

/-- **In positive degrees the degree-zero term does not enter the recursion.** -/
theorem newtonPowerSum_eq_of_pos [Ring A] (r r' : A) (c : ℕ+ → A) :
    ∀ p : ℕ, 0 < p → newtonPowerSum r c p = newtonPowerSum r' c p := by
  intro p
  induction p using Nat.case_strong_induction_on with
  | hz => intro hp; omega
  | hi p ih =>
      intro _
      rw [newtonPowerSum_succ, newtonPowerSum_succ]
      congr 1
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjp : j < p := Finset.mem_range.mp hj
      rw [ih (p - j) (by omega) (by omega)]

/-- **In positive degrees the recursion computes the universal power sum of Stacks 0F9B.** Over a
commutative ring, `newtonPowerSum r c p` for `p > 0` is the evaluation at `c` of the power-sum
polynomial `P_p` of Stacks 0F9B, whatever the degree-zero term `r`. -/
theorem newtonPowerSum_eq_chernClassEval [CommRing A] (r : A) (c : ℕ+ → A) :
    ∀ p : ℕ, 0 < p →
      newtonPowerSum r c p = chernClassEval c (powerSumPolynomial p : MvPolynomial ℕ+ ℤ) := by
  intro p
  induction p using Nat.case_strong_induction_on with
  | hz => intro hp; omega
  | hi p ih =>
      intro _
      rw [newtonPowerSum_succ, coe_powerSumPolynomial_succ, map_add, map_sum]
      have hCX (z : ℤ) (i : ℕ+) : chernClassEval c (C z * X i) = z * c i := by
        rw [map_mul, chernClassEval, eval₂Hom_C, eval₂Hom_X']
        rfl
      congr 1
      · refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hjp : j < p := Finset.mem_range.mp hj
        rw [ih (p - j) (by omega) (by omega), map_mul, hCX]
        push_cast
        rfl
      · rw [hCX]
        push_cast
        ring

/-- **A ring homomorphism carries the recursion to the recursion.** -/
theorem map_newtonPowerSum {B : Type*} [Ring A] [Ring B] (φ : A →+* B) (r : A) (c : ℕ+ → A) :
    ∀ p : ℕ, φ (newtonPowerSum r c p) = newtonPowerSum (φ r) (fun i ↦ φ (c i)) p := by
  intro p
  induction p using Nat.case_strong_induction_on with
  | hz => rw [newtonPowerSum_zero, newtonPowerSum_zero]
  | hi p ih =>
      rw [newtonPowerSum_succ, newtonPowerSum_succ, map_add, map_sum]
      simp only [map_mul, map_pow, map_neg, map_one, map_add, map_natCast]
      congr 1
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjp : j < p := Finset.mem_range.mp hj
      rw [ih (p - j) (by omega)]

/-- **The recursion is the power sum of Stacks 0F9B.** Over a commutative ring, with the
degree-zero term the image of the rank, `AlgebraicGeometry.newtonPowerSum` agrees with
`AlgebraicGeometry.powerSumOfChernClasses` in every degree. -/
theorem newtonPowerSum_eq_powerSumOfChernClasses [CommRing A] (r : ℕ) (c : ℕ+ → A) (p : ℕ) :
    newtonPowerSum (r : A) c p = powerSumOfChernClasses r c p := by
  cases p with
  | zero => rw [newtonPowerSum_zero, powerSumOfChernClasses, coe_powerSumChernPolynomial_zero,
      degreeZeroPowerSum, chernEval_X_none]
  | succ p =>
      rw [newtonPowerSum_eq_chernClassEval (r : A) c (p + 1) (Nat.succ_pos p),
        powerSumOfChernClasses, coe_powerSumChernPolynomial_succ, chernEval_rename_some]

end AlgebraicGeometry

end
