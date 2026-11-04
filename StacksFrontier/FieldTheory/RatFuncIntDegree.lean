module

public import Mathlib.FieldTheory.RatFunc.Degree

/-!
# The integer degree of a power of a rational function

The integer degree `RatFunc.intDegree`, the difference between the degrees of the numerator and
the denominator, is additive on products, hence multiplies by `n` on `n`-th powers. Mathlib has
the product form `RatFunc.intDegree_mul`, which needs both factors nonzero; the power form needs
no hypothesis, because the zero function has integer degree zero and so does each of its powers.

## Main results

* `Stacks.ratFunc_intDegree_pow` — `(x ^ n).intDegree = n * x.intDegree`.
-/

@[expose] public section

namespace Stacks

/-- The integer degree of a rational function multiplies by `n` on `n`-th powers. -/
theorem ratFunc_intDegree_pow {k : Type*} [Field k] (x : RatFunc k) (n : ℕ) :
    (x ^ n).intDegree = n * x.intDegree := by
  rcases eq_or_ne x 0 with rfl | hx
  · cases n <;> simp
  · induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ hx) hx, ih]
      push_cast
      ring

end Stacks

end
