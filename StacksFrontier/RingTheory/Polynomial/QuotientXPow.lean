module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The truncated polynomial ring `R[X]/(Xⁿ)`

This file records the elementary arithmetic of the quotient `R[X]/(Xⁿ)`: the class of `X` is
nilpotent of exact order `n`, and a scalar multiple of one of its powers below `n` vanishes only
if the scalar does. These are the facts used when `R[X]/(Xⁿ)` is used as a test ring to detect a
nonzero vector in a fibre.

## Main definitions

* `Polynomial.QuotientXPow R n`: the ring `R[X]/(Xⁿ)`.
* `Polynomial.QuotientXPow.gen`: the class of `X` in `R[X]/(Xⁿ)`.

## Main results

* `Polynomial.QuotientXPow.gen_pow_self`: the `n`-th power of the generator vanishes.
* `Polynomial.QuotientXPow.gen_pow_ne_zero`: the powers below `n` do not vanish.
* `Polynomial.QuotientXPow.eq_zero_of_algebraMap_mul_gen_pow_eq_zero`: if `a · Xʲ = 0` in
  `R[X]/(Xⁿ)` with `j < n`, then `a = 0`. In particular `1, X, …, Xⁿ⁻¹` are `R`-linearly
  independent.

## Implementation notes

The quotient is an `abbrev`, so that goals stated with the explicit quotient of
`Ideal.span {X ^ n}` and goals stated with `QuotientXPow` are interchangeable.

## References

* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
-/

@[expose] public section

namespace Polynomial

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The truncated polynomial ring `R[X]/(Xⁿ)`. -/
public abbrev QuotientXPow : Type _ :=
  Polynomial R ⧸ Ideal.span {(Polynomial.X : Polynomial R) ^ n}

namespace QuotientXPow

/-- The class of `X` in `R[X]/(Xⁿ)`. -/
public noncomputable def gen : QuotientXPow R n :=
  Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial R) ^ n}) Polynomial.X

/-- The generator of `R[X]/(Xⁿ)` is nilpotent of order dividing `n`. -/
public theorem gen_pow_self : (gen R n) ^ n = 0 := by
  rw [gen, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- A polynomial vanishes in `R[X]/(Xⁿ)` iff its coefficients below `n` vanish. -/
private theorem mk_eq_zero_iff_coeff_eq_zero (p : Polynomial R) :
    Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial R) ^ n}) p = 0 ↔
      ∀ k < n, p.coeff k = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]

/-- Below the exponent `n` the powers of the generator of `R[X]/(Xⁿ)` are nonzero. -/
public theorem gen_pow_ne_zero [Nontrivial R] {j : ℕ} (hj : j < n) : (gen R n) ^ j ≠ 0 := by
  intro h
  rw [gen, ← map_pow, mk_eq_zero_iff_coeff_eq_zero] at h
  simpa using h j hj

/-- A scalar multiple of a power of the generator below the exponent `n` vanishes in `R[X]/(Xⁿ)`
only if the scalar does. -/
public theorem eq_zero_of_algebraMap_mul_gen_pow_eq_zero {j : ℕ} (hj : j < n) {a : R}
    (h : algebraMap R (QuotientXPow R n) a * (gen R n) ^ j = 0) : a = 0 := by
  have hq : Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial R) ^ n})
      (Polynomial.C a * (Polynomial.X : Polynomial R) ^ j) = 0 := by
    rw [map_mul, map_pow]
    simpa [gen, Polynomial.C_eq_algebraMap, Ideal.Quotient.mk_algebraMap] using h
  simpa [Polynomial.coeff_C_mul_X_pow] using
    (mk_eq_zero_iff_coeff_eq_zero R n _).mp hq j hj

end QuotientXPow

end Polynomial

end
