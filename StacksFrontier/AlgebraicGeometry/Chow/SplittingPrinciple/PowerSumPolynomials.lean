module

public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import StacksCore.Tactic.StacksAttribute

/-!
# Power-sum polynomials

The universal power-sum polynomials are integral polynomials in variables `cᵢ`, indexed by
positive natural numbers. They are defined recursively by Newton's formula, with `cᵢ` assigned
weight `i`. Applied to the Chern classes of a vector bundle, they give the power sums of its
"roots", which is what makes them the building blocks of the splitting principle.

## Main definitions

* `AlgebraicGeometry.powerSumPolynomial` is the universal polynomial `Pₚ`, packaged together
  with its weighted homogeneity.

## Main results

* `AlgebraicGeometry.coe_powerSumPolynomial_zero` gives the degree-zero extension.
* `AlgebraicGeometry.coe_powerSumPolynomial_succ` is Newton's recurrence in the ambient
  polynomial ring.
* `AlgebraicGeometry.isWeightedHomogeneous_powerSumPolynomial` records the prescribed
  homogeneity.

## Implementation notes

The polynomial ring `ℤ[c₁, c₂, …]` is represented by `MvPolynomial ℕ+ ℤ`. The codomain of
`powerSumPolynomial p` is the weighted-homogeneous submodule of degree `p`, for the weight
function sending the variable `cᵢ` to `i`. Although only positive `p` occurs in the source,
the definition is extended canonically to `p = 0` by setting `P₀ = 0`; this makes the family
easy to index by natural numbers and does not enter the recursive formula at positive degrees.
The two coercion lemmas let polynomial evaluations rewrite the recursion without unfolding the
subtype-valued definition. The named homogeneity theorem gives downstream users the grading
property without unfolding the construction.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open MvPolynomial

/-- The universal power-sum polynomial `Pₚ` in the Chern-class variables `cᵢ`.

The variable indexed by `i : ℕ+` has weight `i`. Thus the value is packaged as a
weighted-homogeneous polynomial of degree `p`. For `p + 1`, the displayed recursion is
Newton's formula
`Pₚ₊₁ = ∑ᵢ₌₁ᵖ (-1)ⁱ⁻¹ cᵢ Pₚ₊₁₋ᵢ + (-1)ᵖ (p + 1) cₚ₊₁`.
-/
@[stacks 0F9B "power_sum_polynomials"]
noncomputable def powerSumPolynomial (p : ℕ) :
    weightedHomogeneousSubmodule ℤ (fun i : ℕ+ => (i : ℕ)) p :=
  match p with
  | 0 => 0
  | p + 1 =>
      ⟨∑ j ∈ Finset.range p,
          C ((-1 : ℤ) ^ j) * X (Nat.succPNat j) *
            (powerSumPolynomial (p - j) : MvPolynomial ℕ+ ℤ) +
        C ((-1 : ℤ) ^ p * (p + 1)) * X (Nat.succPNat p), by
        apply IsWeightedHomogeneous.add
        · apply IsWeightedHomogeneous.sum
          intro j hj
          have hX : IsWeightedHomogeneous (fun i : ℕ+ => (i : ℕ))
              (X (Nat.succPNat j) : MvPolynomial ℕ+ ℤ) (j + 1) := by
            simpa using isWeightedHomogeneous_X (R := ℤ) (fun i : ℕ+ => (i : ℕ))
              (Nat.succPNat j)
          convert ((hX.C_mul ((-1 : ℤ) ^ j)).mul (powerSumPolynomial (p - j)).property) using 1
          have := Finset.mem_range.mp hj
          omega
        · simpa using (isWeightedHomogeneous_X (R := ℤ)
            (fun i : ℕ+ => (i : ℕ)) (Nat.succPNat p)).C_mul ((-1 : ℤ) ^ p * (p + 1))⟩
termination_by p
decreasing_by all_goals exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- The auxiliary degree-zero value of `powerSumPolynomial` is zero in the ambient polynomial
ring. -/
@[simp]
theorem coe_powerSumPolynomial_zero :
    (powerSumPolynomial 0 : MvPolynomial ℕ+ ℤ) = 0 := by simp [powerSumPolynomial]

/-- Newton's recurrence for `powerSumPolynomial`, stated in the ambient polynomial ring so that
polynomial evaluations and ring homomorphisms can rewrite with it directly. -/
@[simp]
theorem coe_powerSumPolynomial_succ (p : ℕ) :
    (powerSumPolynomial (p + 1) : MvPolynomial ℕ+ ℤ) =
      ∑ j ∈ Finset.range p,
          C ((-1 : ℤ) ^ j) * X (Nat.succPNat j) *
            (powerSumPolynomial (p - j) : MvPolynomial ℕ+ ℤ) +
        C ((-1 : ℤ) ^ p * (p + 1)) * X (Nat.succPNat p) := by rw [powerSumPolynomial]

/-- The polynomial `Pₚ` is weighted homogeneous of degree `p` when `cᵢ` has weight `i`. -/
theorem isWeightedHomogeneous_powerSumPolynomial (p : ℕ) :
    IsWeightedHomogeneous (fun i : ℕ+ => (i : ℕ))
      (powerSumPolynomial p : MvPolynomial ℕ+ ℤ) p :=
  (powerSumPolynomial p).property

end AlgebraicGeometry
