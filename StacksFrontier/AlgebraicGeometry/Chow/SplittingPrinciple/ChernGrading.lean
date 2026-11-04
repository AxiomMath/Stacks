module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern grading and the degree-zero power sum

We model the universal polynomial ring in a rank variable and the positive Chern-class
variables, with the rank variable assigned weight zero and the variable for the `i`-th Chern
class assigned weight `i`. Its degree-zero power-sum polynomial is the rank variable.

## Main definitions

* `AlgebraicGeometry.ChernPolynomial` is the polynomial ring over the integers in a rank
  variable and variables indexed by the positive integers.
* `AlgebraicGeometry.chernPolynomialWeight` gives these variables their Chern degrees.
* `AlgebraicGeometry.ChernPolynomial.homogeneousSubmodule` is the resulting grading.
* `AlgebraicGeometry.degreeZeroPowerSum` is the degree-zero power-sum polynomial.

## Main results

* `AlgebraicGeometry.degreeZeroPowerSum_mem_homogeneousSubmodule` records that the polynomial
  has degree zero.

## Implementation notes

The variable index `none` represents `r`, while `some i` represents `c_i`; using positive
natural numbers prevents an extraneous variable `c_0`. The grading is the weighted grading
provided by `MvPolynomial.weightedHomogeneousSubmodule` for `chernPolynomialWeight`. The
zeroth power sum is an abbreviation for `MvPolynomial.X none`, so the standard API for
evaluating a polynomial variable applies directly.

This ambient ring is deliberately distinct from the ring `MvPolynomial ℕ+ ℤ` used for the
positive-degree power-sum polynomials: only the degree-zero statement needs the rank variable,
and adding it to the ring where Newton's recurrence lives would introduce a weight-zero
variable that the weighted grading there must not see.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
-/

@[expose] public section

namespace AlgebraicGeometry

/-- The universal polynomial ring `ℤ[r, c₁, c₂, …]`. The index `none` denotes the rank
variable, and `some i` denotes the `i`-th Chern-class variable. -/
abbrev ChernPolynomial := MvPolynomial (Option ℕ+) ℤ

/-- The weight defining the Chern grading on `ChernPolynomial`: the rank variable has degree
zero, and `c_i` has degree `i`. -/
def chernPolynomialWeight : Option ℕ+ → ℕ
  | none => 0
  | some i => i

/-- The degree-`p` piece of the universal Chern polynomial ring. -/
abbrev ChernPolynomial.homogeneousSubmodule (p : ℕ) : Submodule ℤ ChernPolynomial :=
  MvPolynomial.weightedHomogeneousSubmodule ℤ chernPolynomialWeight p

/-- The universal Chern polynomial ring, graded by Chern degree. -/
noncomputable instance ChernPolynomial.instGradedAlgebra :
    GradedAlgebra ChernPolynomial.homogeneousSubmodule :=
  MvPolynomial.weightedGradedAlgebra ℤ chernPolynomialWeight

/-- The zeroth power-sum polynomial is the rank variable `r`. -/
@[stacks 0F9B "degree_zero_power_sum"]
noncomputable abbrev degreeZeroPowerSum : ChernPolynomial := MvPolynomial.X none

/-- The zeroth power-sum polynomial belongs to the degree-zero piece of the Chern grading. -/
theorem degreeZeroPowerSum_mem_homogeneousSubmodule :
    degreeZeroPowerSum ∈ ChernPolynomial.homogeneousSubmodule 0 :=
  MvPolynomial.isWeightedHomogeneous_X ℤ chernPolynomialWeight none

end AlgebraicGeometry
