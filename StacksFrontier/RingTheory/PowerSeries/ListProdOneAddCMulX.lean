module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Products of the power series `1 + x X` over a noncommutative ring

Let `R` be a ring, not necessarily commutative, and `x_1, …, x_r ∈ R`. The product

  `(1 + x_1 X) (1 + x_2 X) ⋯ (1 + x_r X)`

in `R⟦X⟧` has no coefficients in degrees above `r`, and the sum of its coefficients is the
product `(1 + x_1) (1 + x_2) ⋯ (1 + x_r)` in `R`: the variable `X` is central, so evaluating at
`X = 1` is multiplicative on series of bounded degree. Multiplication by `1 + x X` is the
recursion `a_{n+1} = b_{n+1} + x b_n`, `a_0 = b_0`, on coefficients.

This is the bookkeeping behind identities `c(ℰ) = ∏ (1 + x_i)` between total Chern classes,
where the Chern classes `c_n` are the coefficients and the degree is recorded by `X`.

## Main results

* `PowerSeries.mk_eq_one_add_C_mul_X_mul`: a coefficient recursion `a_{n+1} = b_{n+1} + x b_n`
  is the identity `a = (1 + x X) b`.
* `PowerSeries.coeff_list_prod_one_add_C_mul_X_of_length_lt`: the product of `r` factors
  `1 + x_i X` has no coefficients in degrees above `r`.
* `PowerSeries.sum_coeff_list_prod_one_add_C_mul_X`: the sum of its coefficients is
  `∏ (1 + x_i)`.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [Ring R]

/-- The coefficient of `X ^ (n + 1)` in `(1 + x X) φ`. -/
private theorem coeff_succ_one_add_C_mul_X_mul (x : R) (φ : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) ((1 + C x * X) * φ) = coeff (n + 1) φ + x * coeff n φ := by
  rw [add_mul, one_mul, mul_assoc, map_add, coeff_C_mul, coeff_succ_X_mul]

/-- **Multiplication by `1 + x X` on coefficients.** If `a 0 = b 0` and
`a (n + 1) = b (n + 1) + x * b n` for all `n`, then `a = (1 + x X) b` as power series. -/
theorem mk_eq_one_add_C_mul_X_mul {a b : ℕ → R} {x : R} (h0 : a 0 = b 0)
    (h : ∀ n, a (n + 1) = b (n + 1) + x * b n) :
    PowerSeries.mk a = (1 + C x * X) * PowerSeries.mk b := by
  ext n
  cases n with
  | zero => simp [h0]
  | succ n => rw [coeff_succ_one_add_C_mul_X_mul, coeff_mk, coeff_mk, coeff_mk, h]

/-- The coefficients of `(1 + x X) φ`. -/
theorem coeff_one_add_C_mul_X_mul (x : R) (φ : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) ((1 + C x * X) * φ) = coeff (n + 1) φ + x * coeff n φ :=
  coeff_succ_one_add_C_mul_X_mul x φ n

/-- **A product of `r` factors `1 + x_i X` has no coefficients in degrees above `r`.** -/
theorem coeff_list_prod_one_add_C_mul_X_of_length_lt :
    ∀ (l : List R) {n : ℕ}, l.length < n → coeff n (l.map fun x ↦ 1 + C x * X).prod = 0
  | [], n, hn => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
      simp [coeff_one]
  | x :: l, n, hn => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
      simp only [List.map_cons, List.prod_cons]
      rw [coeff_one_add_C_mul_X_mul,
        coeff_list_prod_one_add_C_mul_X_of_length_lt l (by simp at hn; omega),
        coeff_list_prod_one_add_C_mul_X_of_length_lt l (by simp at hn; omega), mul_zero, add_zero]

/-- **The sum of the coefficients of `∏ (1 + x_i X)` is `∏ (1 + x_i)`.** For a list
`x_1, …, x_r` of elements of a ring, `∑_{n ≤ r} coeff n ((1 + x_1 X) ⋯ (1 + x_r X))` equals
`(1 + x_1) ⋯ (1 + x_r)`. -/
theorem sum_coeff_list_prod_one_add_C_mul_X :
    ∀ l : List R, ∑ n ∈ Finset.range (l.length + 1), coeff n (l.map fun x ↦ 1 + C x * X).prod =
      (l.map fun x ↦ 1 + x).prod
  | [] => by simp [coeff_one]
  | x :: l => by
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      have ih := sum_coeff_list_prod_one_add_C_mul_X l
      have hz := coeff_list_prod_one_add_C_mul_X_of_length_lt l (Nat.lt_succ_self _)
      set p := (l.map fun x ↦ 1 + C x * X).prod
      have hS : ∑ n ∈ Finset.range (l.length + 1), coeff n p =
          ∑ k ∈ Finset.range l.length, coeff (k + 1) p + constantCoeff p := by
        rw [Finset.sum_range_succ', coeff_zero_eq_constantCoeff_apply]
      have h₀ : constantCoeff (1 + C x * X : R⟦X⟧) = 1 := by simp
      rw [Finset.sum_range_succ', coeff_zero_eq_constantCoeff_apply, map_mul, h₀, one_mul]
      simp only [coeff_one_add_C_mul_X_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_succ (fun k ↦ coeff (k + 1) p),
        hz, add_zero, add_assoc, add_left_comm, ← hS, ih, add_mul, one_mul, add_comm]

end PowerSeries

end
