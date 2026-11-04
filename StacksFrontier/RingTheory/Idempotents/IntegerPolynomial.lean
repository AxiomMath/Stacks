module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Idempotents

/-!
# Idempotents as integer polynomials in an approximate idempotent

Let `A` be a possibly noncommutative ring and let `e ∈ A` be such that `x = e ^ 2 - e` is
nilpotent. Then there is an idempotent of the form `e' = e + x * (∑ a i j • e ^ i * x ^ j)` with
integer coefficients `a i j`.

The source reduces to the universal case `ℤ[e]/((e ^ 2 - e) ^ n)` and lifts idempotents there.
We instead write the lift down explicitly: if `(e ^ 2 - e) ^ n = 0` with `n ≥ 1`, then
`1 - (1 - e ^ n) ^ n` is idempotent (`isIdempotentElem_one_sub_one_sub_pow_pow`), and the integer
polynomial `1 - (1 - X ^ n) ^ n - X` vanishes at `0` and `1`, so it is a multiple of `X ^ 2 - X`.

## Main results

* `Polynomial.sq_sub_X_dvd_one_sub_one_sub_X_pow_pow_sub_X`: `X ^ 2 - X` divides
  `1 - (1 - X ^ n) ^ n - X` for `n ≠ 0`.
* `exists_isIdempotentElem_add_sq_sub_mul_aeval`: if `e ^ 2 - e` is nilpotent then
  `e + (e ^ 2 - e) * q(e)` is idempotent for some `q ∈ ℤ[X]`.
* `exists_isIdempotentElem_add_sq_sub_mul_sum`: the same, with the correction term written as a
  finite sum `∑ a i j • (e ^ i * (e ^ 2 - e) ^ j)` with `a i j ∈ ℤ`, as in the source.

## References

* [Stacks Project, Tag 05BU](https://stacks.math.columbia.edu/tag/05BU)
-/

@[expose] public section

open Polynomial

namespace Polynomial

/-- For `n ≠ 0` the polynomial `1 - (1 - X ^ n) ^ n - X` is a multiple of `X ^ 2 - X`, since it
vanishes at `0` and at `1`. -/
theorem sq_sub_X_dvd_one_sub_one_sub_X_pow_pow_sub_X {R : Type*} [CommRing R] {n : ℕ}
    (hn : n ≠ 0) : (X ^ 2 - X : R[X]) ∣ 1 - (1 - X ^ n) ^ n - X := by
  rw [show (X ^ 2 - X : R[X]) = (X - C 0) * (X - C 1) by simp [sq, mul_sub]]
  refine IsCoprime.mul_dvd ⟨1, -1, by simp⟩ ?_ ?_ <;> rw [dvd_iff_isRoot] <;> simp [hn]

end Polynomial

variable {A : Type*} [Ring A]

/-- If `e ^ 2 - e` is nilpotent in a (possibly noncommutative) ring, then some
`e + (e ^ 2 - e) * q(e)` with `q ∈ ℤ[X]` is idempotent. -/
theorem exists_isIdempotentElem_add_sq_sub_mul_aeval {e : A} (he : IsNilpotent (e ^ 2 - e)) :
    ∃ q : ℤ[X], IsIdempotentElem (e + (e ^ 2 - e) * aeval e q) := by
  obtain ⟨n, hn⟩ := he
  obtain ⟨q, hq⟩ := sq_sub_X_dvd_one_sub_one_sub_X_pow_pow_sub_X (R := ℤ) n.succ_ne_zero
  refine ⟨q, ?_⟩
  have h := congrArg (aeval e) hq
  simp only [map_sub, map_one, map_pow, aeval_X, map_mul] at h
  have key : e + (e ^ 2 - e) * aeval e q = 1 - (1 - e ^ (n + 1)) ^ (n + 1) := by
    rw [← h]
    abel
  rw [key]
  refine isIdempotentElem_one_sub_one_sub_pow_pow e (n + 1) ?_
  rw [show e - e ^ 2 = -(e ^ 2 - e) by abel, neg_pow, pow_succ (e ^ 2 - e), hn, zero_mul,
    mul_zero]

/-- Let `A` be a possibly noncommutative ring and let `e ∈ A` be such that `x = e ^ 2 - e` is
nilpotent. Then there is an idempotent of the form `e + x * (∑ a i j • (e ^ i * x ^ j))` with
integer coefficients `a i j`. -/
@[stacks 05BU]
theorem exists_isIdempotentElem_add_sq_sub_mul_sum {e : A} (he : IsNilpotent (e ^ 2 - e)) :
    ∃ (N : ℕ) (a : ℕ → ℕ → ℤ), IsIdempotentElem (e + (e ^ 2 - e) *
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, a i j • (e ^ i * (e ^ 2 - e) ^ j)) := by
  obtain ⟨q, hq⟩ := exists_isIdempotentElem_add_sq_sub_mul_aeval he
  refine ⟨q.natDegree + 1, fun i j ↦ if j = 0 then q.coeff i else 0, ?_⟩
  convert hq using 3
  rw [aeval_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [ite_smul]
