module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Finite.Basic

/-!
# Polynomials agreeing at the multiples of an integer

Over a field of characteristic zero, a polynomial is determined by its values at the multiples
`n m` (`m ∈ ℤ`) of a fixed nonzero integer `n`, these forming an infinite set. This is the
arithmetic which lets a numerical polynomial be recovered from its values on `n ℤ`, as in the
reindexing `P'(t) = P(n t)` of Stacks 0DP8.

## Main results

* `Polynomial.eq_of_eval_intCast_mul_eq`: two polynomials over a field of characteristic zero
  which agree at every `n m`, `m ∈ ℤ`, for a fixed `n ≠ 0`, are equal.

## References

* [Stacks Project, Tag 0DP8](https://stacks.math.columbia.edu/tag/0DP8)
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [Field R] [CharZero R]

/-- Two polynomials over a field of characteristic zero which agree at all the integral
multiples `n m` of a nonzero integer `n` are equal: those multiples form an infinite set. -/
theorem eq_of_eval_intCast_mul_eq {p q : R[X]} {n : ℤ} (hn : n ≠ 0)
    (h : ∀ m : ℤ, p.eval ((n * m : ℤ) : R) = q.eval ((n * m : ℤ) : R)) : p = q :=
  eq_of_infinite_eval_eq p q <|
    Set.infinite_of_injective_forall_mem (f := fun m : ℤ => ((n * m : ℤ) : R))
      (fun a b hab => by simpa [hn] using hab) h

end Polynomial

end
