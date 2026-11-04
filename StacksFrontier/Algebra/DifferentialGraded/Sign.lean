module

public import Mathlib.Algebra.Ring.NegOnePow

/-!
# The Koszul sign as a scalar

Graded constructions over a commutative ring repeatedly need the sign `(-1)^n` for an *integer*
exponent `n`, viewed as an element of the ring rather than as a unit of `ℤ`. Mathlib's
`Int.negOnePow` provides `(-1)^n : ℤˣ`; this file records its image in a ring and the three
identities (value at zero, additivity, and the successor rule) that the graded Leibniz
computations use.

## Main definitions

* `DifferentialGraded.gradedSign`: the sign `(-1)^n` for `n : ℤ`, as an element of a ring.

## Main results

* `DifferentialGraded.gradedSign_zero`, `DifferentialGraded.gradedSign_add` and
  `DifferentialGraded.gradedSign_succ`: the sign is multiplicative in the degree.
* `DifferentialGraded.intCast_negOnePow`: the sign is the image of `Int.negOnePow`, which is how
  it meets the statements phrased with `Int.negOnePow`.

## Implementation notes

The definition is `(-1) ^ n.natAbs`, matching the form in which the sign appears in the
differential of a Hom complex, rather than the cast of `Int.negOnePow`; the two agree by
`intCast_negOnePow`, which is proved from Mathlib's `Int.coe_negOnePow`.
-/

@[expose] public section

namespace DifferentialGraded

universe u

/-- The sign `(-1)^n` for an integer exponent `n`, as an element of a ring. -/
def gradedSign (R : Type u) [Ring R] (n : ℤ) : R := (-1 : R) ^ n.natAbs

variable {R : Type u} [Ring R]

/-- The image of `Int.negOnePow n` in a ring `R` is `gradedSign R n`. -/
@[simp] theorem intCast_negOnePow (n : ℤ) : ((n.negOnePow : ℤ) : R) = gradedSign R n :=
  Int.coe_negOnePow R n

/-- The sign with exponent zero is `1`. -/
@[simp] theorem gradedSign_zero : gradedSign R 0 = 1 := by simp [gradedSign]

/-- The sign of a sum of exponents is the product of the signs: `(-1)^(m+n) = (-1)^m (-1)^n`. -/
theorem gradedSign_add (m n : ℤ) :
    gradedSign R (m + n) = gradedSign R m * gradedSign R n := by
  simp only [← intCast_negOnePow, Int.negOnePow_add, Units.val_mul, Int.cast_mul]

/-- Increasing the exponent by one negates the sign: `(-1)^(n+1) = -(-1)^n`. -/
theorem gradedSign_succ (n : ℤ) : gradedSign R (n + 1) = -gradedSign R n := by
  rw [gradedSign_add]; simp [gradedSign]

end DifferentialGraded
