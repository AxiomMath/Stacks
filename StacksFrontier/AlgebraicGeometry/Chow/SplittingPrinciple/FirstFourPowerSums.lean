module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.PowerSumPolynomials
public import StacksCore.Tactic.StacksAttribute

/-!
# The first four power-sum polynomials

The first four universal power-sum polynomials are expressed in terms of the Chern-class
variables by the familiar Newton identities.

## Main results

* `AlgebraicGeometry.coe_powerSumPolynomial_one` computes `P₁`.
* `AlgebraicGeometry.coe_powerSumPolynomial_two` computes `P₂`.
* `AlgebraicGeometry.coe_powerSumPolynomial_three` computes `P₃`.
* `AlgebraicGeometry.coe_powerSumPolynomial_four` computes `P₄`.

## Implementation notes

Each displayed equality in the source is stated separately. The Chern-class variable `cᵢ` is
represented by `MvPolynomial.X (i : ℕ+)`, and the subtype-valued power-sum polynomial is
coerced to the ambient polynomial ring `MvPolynomial ℕ+ ℤ`.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open MvPolynomial

/-- The first power-sum polynomial is `c₁`. -/
@[stacks 0F9B "first_four_power_sums"]
theorem coe_powerSumPolynomial_one :
    (powerSumPolynomial 1 : MvPolynomial ℕ+ ℤ) = X (1 : ℕ+) := by
  simp [coe_powerSumPolynomial_succ, Nat.succPNat]

/-- The second power-sum polynomial is `c₁² - 2c₂`. -/
@[stacks 0F9B "first_four_power_sums"]
theorem coe_powerSumPolynomial_two :
    (powerSumPolynomial 2 : MvPolynomial ℕ+ ℤ) =
      X (1 : ℕ+) ^ 2 - 2 * X (2 : ℕ+) := by
  simp [coe_powerSumPolynomial_succ, Nat.succPNat]
  ring

/-- The third power-sum polynomial is `c₁³ - 3c₁c₂ + 3c₃`. -/
@[stacks 0F9B "first_four_power_sums"]
theorem coe_powerSumPolynomial_three :
    (powerSumPolynomial 3 : MvPolynomial ℕ+ ℤ) =
      X (1 : ℕ+) ^ 3 - 3 * X (1 : ℕ+) * X (2 : ℕ+) + 3 * X (3 : ℕ+) := by
  norm_num [coe_powerSumPolynomial_succ, Finset.sum_range_succ, Nat.succPNat]
  ring

/-- The fourth power-sum polynomial is `c₁⁴ - 4c₁²c₂ + 4c₁c₃ + 2c₂² - 4c₄`. -/
@[stacks 0F9B "first_four_power_sums"]
theorem coe_powerSumPolynomial_four :
    (powerSumPolynomial 4 : MvPolynomial ℕ+ ℤ) =
      X (1 : ℕ+) ^ 4 - 4 * X (1 : ℕ+) ^ 2 * X (2 : ℕ+) +
        4 * X (1 : ℕ+) * X (3 : ℕ+) + 2 * X (2 : ℕ+) ^ 2 - 4 * X (4 : ℕ+) := by
  norm_num [coe_powerSumPolynomial_succ, Finset.sum_range_succ, Nat.succPNat]
  ring

end AlgebraicGeometry
