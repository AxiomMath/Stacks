module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# The twist of a total Chern class by a line bundle, as an operation on power series

Let `R` be a commutative ring, `x ∈ R` and `r ∈ ℤ`. For a power series
`c = c₀ + c₁ t + c₂ t² + ⋯` over `R` put

  `T_{r,x}(c)_i = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j} x^j`,

where `binom(n, j)` is the generalized binomial coefficient `Ring.choose n j`, meaningful for
every `n ∈ ℤ`. For a finite locally free module `ℰ` of rank `r` and an invertible module `ℒ`,
[Stacks, Tag 02UD] says `c(ℰ ⊗ ℒ) = T_{r,x}(c(ℰ))` with `x = c₁(ℒ)`, and
[Stacks, Tag 0FAF] says the same for a perfect object of constant rank `r`. The proof of the
second from the first is "a formal computation", and this file is that computation.

In terms of generating functions `T_{r,x}(c) = ∑_k c_k t^k (1 + x t)^{r - k}`, that is,
`(1 + x t)^r c(t / (1 + x t))`. The two facts that make the computation formal are:

* `T` is multiplicative in `c` and additive in `r`:
  `T_{r+s,x}(c d) = T_{r,x}(c) T_{s,x}(d)` (`Stacks.Chow.twistSeries_mul`);
* `T_{0,x}(1) = 1` (`Stacks.Chow.twistSeries_zero_one`).

Hence for a bounded complex `ℰ^•` with `c(ℰ^•) = ∏_n c(ℰ^n)^{(-1)^n}` and rank
`r = ∑_n (-1)^n r_n`, the twists of the terms assemble into the twist of the complex
(`Stacks.Chow.twistSeries_prod`, `Stacks.Chow.twistSeries_inv`).

## Main definitions

* `Stacks.Chow.twistBinomial` — the power series `(1 + x t)^m`, for `m ∈ ℤ`.
* `Stacks.Chow.twistSeries` — the operation `T_{r,x}`.
* `Stacks.Chow.twistSeriesHom` — `(r, c) ↦ T_{r,x}(c)` as a monoid homomorphism
  `Multiplicative ℤ × R⟦X⟧ →* R⟦X⟧`.

## Main results

* `Stacks.Chow.coeff_twistSeries_eq_sum_choose` — the coefficients in the indexing of the source.
* `Stacks.Chow.twistSeries_mul`, `Stacks.Chow.twistSeries_zero_one` — the two facts above.
* `Stacks.Chow.twistSeries_inv` — the twist of a formal inverse is the inverse of the twist, at
  the opposite rank.
* `Stacks.Chow.twistSeries_prod` — the twist of a finite product.
* `Stacks.Chow.twistSeries_one_add_monomial` — the twist of `1 + y t` at rank one is
  `1 + (x + y) t`, the case of an invertible module.

## References

* [Stacks Project, Tag 0FAF](https://stacks.math.columbia.edu/tag/0FAF)
* [Stacks Project, Tag 02UD](https://stacks.math.columbia.edu/tag/02UD)
-/

@[expose] public noncomputable section

open PowerSeries Finset

namespace Stacks.Chow

variable {R : Type*} [CommRing R]

/-! ### The binomial series `(1 + x t)^m` -/

/-- The power series `(1 + x t)^m` for `m ∈ ℤ`, whose `j`-th coefficient is
`binom(m, j) x^j`. -/
def twistBinomial (x : R) (m : ℤ) : R⟦X⟧ :=
  rescale x (binomialSeries R m)

/-- The `j`-th coefficient of `(1 + x t)^m` is `binom(m, j) x^j`. -/
theorem coeff_twistBinomial (x : R) (m : ℤ) (j : ℕ) :
    coeff j (twistBinomial x m) = ((Ring.choose m j : ℤ) : R) * x ^ j := by
  simp [twistBinomial, coeff_rescale, mul_comm]

/-- `(1 + x t)^(m + n) = (1 + x t)^m (1 + x t)^n`. -/
theorem twistBinomial_add (x : R) (m n : ℤ) :
    twistBinomial x (m + n) = twistBinomial x m * twistBinomial x n := by
  simp [twistBinomial]

/-- `(1 + x t)^0 = 1`. -/
theorem twistBinomial_zero (x : R) : twistBinomial x 0 = 1 := by
  ext j
  rw [coeff_twistBinomial, coeff_one]
  rcases j with _ | j
  · simp
  · simp [Ring.choose_zero_succ]

/-! ### The twist -/

/-- The twist `T_{r,x}(c)` of a power series `c`: its `i`-th coefficient is
`∑_{k ≤ i} c_k binom(r - k, i - k) x^{i-k}`, the coefficient of `t^i` in
`∑_k c_k t^k (1 + x t)^{r - k}`. -/
def twistSeries (r : ℤ) (x : R) (c : R⟦X⟧) : R⟦X⟧ :=
  mk fun i => ∑ k ∈ range (i + 1), coeff k c * coeff (i - k) (twistBinomial x (r - k))

/-- The `i`-th coefficient of `T_{r,x}(c)` is the coefficient of `t^i` in
`∑_k c_k t^k (1 + x t)^{r - k}`. -/
theorem coeff_twistSeries (r : ℤ) (x : R) (c : R⟦X⟧) (i : ℕ) :
    coeff i (twistSeries r x c) =
      ∑ k ∈ range (i + 1), coeff k c * coeff (i - k) (twistBinomial x (r - k)) :=
  coeff_mk _ _

/-- **The coefficients of the twist, in the indexing of Stacks 0FAF:**
`T_{r,x}(c)_i = ∑_{j=0}^{i} binom(r - i + j, j) c_{i-j} x^j`. -/
theorem coeff_twistSeries_eq_sum_choose (r : ℤ) (x : R) (c : R⟦X⟧) (i : ℕ) :
    coeff i (twistSeries r x c) =
      ∑ j ∈ range (i + 1), ((Ring.choose (r - i + j) j : ℤ) : R) * coeff (i - j) c * x ^ j := by
  rw [coeff_twistSeries, ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj : j ≤ i := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show i + 1 - 1 - j = i - j by omega, show i - (i - j) = j by omega, coeff_twistBinomial,
    show r - ((i - j : ℕ) : ℤ) = r - i + j by push_cast [hj]; ring]
  ring

/-- The twist `T_{r,x}` is additive in the series. -/
theorem twistSeries_add (r : ℤ) (x : R) (c d : R⟦X⟧) :
    twistSeries r x (c + d) = twistSeries r x c + twistSeries r x d := by
  ext i
  simp only [coeff_twistSeries, map_add, add_mul, sum_add_distrib]

/-- The `i`-th coefficient of a twist only depends on the coefficients of degree `≤ i`. -/
theorem coeff_twistSeries_congr {r : ℤ} {x : R} {c d : R⟦X⟧} {i : ℕ}
    (h : ∀ k ≤ i, coeff k c = coeff k d) :
    coeff i (twistSeries r x c) = coeff i (twistSeries r x d) := by
  simp only [coeff_twistSeries]
  exact sum_congr rfl fun k hk => by rw [h k (Nat.lt_succ_iff.mp (mem_range.mp hk))]

/-- The `n`-th coefficient of a product only depends on the coefficients of degree `≤ n` of the
two factors. -/
theorem coeff_mul_congr {f f' g g' : R⟦X⟧} {n : ℕ} (hf : ∀ k ≤ n, coeff k f = coeff k f')
    (hg : ∀ k ≤ n, coeff k g = coeff k g') : coeff n (f * g) = coeff n (f' * g') := by
  simp only [coeff_mul]
  refine sum_congr rfl fun ab hab => ?_
  have h := mem_antidiagonal.mp hab
  rw [hf ab.1 (by omega), hg ab.2 (by omega)]

/-- The coefficients of a product with a monomial. -/
theorem coeff_monomial_mul' (k i : ℕ) (a : R) (f : R⟦X⟧) :
    coeff i (monomial k a * f) = if k ≤ i then a * coeff (i - k) f else 0 := by
  rw [show monomial k a = C a * X ^ k by
      rw [X_pow_eq, ← monomial_zero_eq_C, monomial_mul_monomial]; simp,
    mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

/-- The twist of a monomial `a t^k` is `a t^k (1 + x t)^{r - k}`. -/
theorem twistSeries_monomial (r : ℤ) (x : R) (k : ℕ) (a : R) :
    twistSeries r x (monomial k a) = monomial k a * twistBinomial x (r - k) := by
  ext i
  rw [coeff_twistSeries, coeff_monomial_mul']
  split_ifs with hk
  · rw [sum_eq_single k]
    · simp
    · intro b _ hb
      simp [coeff_monomial, hb]
    · intro hk'
      exact absurd (mem_range.mpr (Nat.lt_succ_of_le hk)) hk'
  · refine sum_eq_zero fun b hb => ?_
    have : b ≠ k := by
      have := Nat.lt_succ_iff.mp (mem_range.mp hb)
      omega
    simp [coeff_monomial, this]

/-- For polynomials `p` and `q`, `T_{r+s,x}(p q) = T_{r,x}(p) T_{s,x}(q)`. -/
theorem twistSeries_mul_coe (r s : ℤ) (x : R) (p q : Polynomial R) :
    twistSeries (r + s) x ((p : R⟦X⟧) * q) = twistSeries r x p * twistSeries s x q := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ =>
    rw [Polynomial.coe_add, add_mul, twistSeries_add, h₁, h₂, twistSeries_add, add_mul]
  | monomial k a =>
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ =>
      rw [Polynomial.coe_add, mul_add, twistSeries_add, h₁, h₂, twistSeries_add, mul_add]
    | monomial l b =>
      rw [Polynomial.coe_monomial, Polynomial.coe_monomial, monomial_mul_monomial,
        twistSeries_monomial, twistSeries_monomial, twistSeries_monomial,
        ← monomial_mul_monomial,
        show r + s - ((k + l : ℕ) : ℤ) = (r - k) + (s - l) by push_cast; ring,
        twistBinomial_add]
      ring

/-- **The twist is multiplicative in the series and additive in the rank:**
`T_{r+s,x}(c d) = T_{r,x}(c) T_{s,x}(d)`. -/
theorem twistSeries_mul (r s : ℤ) (x : R) (c d : R⟦X⟧) :
    twistSeries (r + s) x (c * d) = twistSeries r x c * twistSeries s x d := by
  ext n
  have ht (f : R⟦X⟧) : ∀ k ≤ n, coeff k f = coeff k (trunc (n + 1) f : R⟦X⟧) := fun k hk =>
    (coeff_coe_trunc_of_lt (Nat.lt_succ_of_le hk)).symm
  calc coeff n (twistSeries (r + s) x (c * d))
      = coeff n (twistSeries (r + s) x
          ((trunc (n + 1) c : R⟦X⟧) * (trunc (n + 1) d : R⟦X⟧))) :=
        coeff_twistSeries_congr fun k hk =>
          coeff_mul_congr (fun m hm => ht c m (hm.trans hk)) (fun m hm => ht d m (hm.trans hk))
    _ = coeff n (twistSeries r x (trunc (n + 1) c : R⟦X⟧) *
          twistSeries s x (trunc (n + 1) d : R⟦X⟧)) := by rw [twistSeries_mul_coe]
    _ = coeff n (twistSeries r x c * twistSeries s x d) :=
        coeff_mul_congr
          (fun k hk => coeff_twistSeries_congr fun m hm => (ht c m (hm.trans hk)).symm)
          (fun k hk => coeff_twistSeries_congr fun m hm => (ht d m (hm.trans hk)).symm)

/-- The unit power series is the constant monomial `1`. -/
theorem one_eq_monomial_zero : (1 : R⟦X⟧) = monomial 0 1 := by
  ext n
  simp [coeff_one]

/-- The twist of the unit series at rank zero is the unit series. -/
theorem twistSeries_zero_one (x : R) : twistSeries 0 x 1 = 1 := by
  rw [one_eq_monomial_zero, twistSeries_monomial]
  simp [twistBinomial_zero]

/-- **The twist of a formal inverse:** if `c' c = 1` then `T_{-r,x}(c') T_{r,x}(c) = 1`. -/
theorem twistSeries_inv (r : ℤ) (x : R) {c c' : R⟦X⟧} (h : c' * c = 1) :
    twistSeries (-r) x c' * twistSeries r x c = 1 := by
  rw [← twistSeries_mul, neg_add_cancel, h, twistSeries_zero_one]

/-- The pair `(r, c) ↦ T_{r,x}(c)` as a monoid homomorphism from `Multiplicative ℤ × R⟦X⟧`. -/
def twistSeriesHom (x : R) : Multiplicative ℤ × R⟦X⟧ →* R⟦X⟧ where
  toFun rc := twistSeries (Multiplicative.toAdd rc.1) x rc.2
  map_one' := twistSeries_zero_one x
  map_mul' _ _ := twistSeries_mul _ _ x _ _

/-- **The twist of a finite product:** `T_{∑ r_n, x}(∏ c_n) = ∏ T_{r_n, x}(c_n)`. -/
theorem twistSeries_prod {ι : Type*} (s : Finset ι) (r : ι → ℤ) (x : R) (c : ι → R⟦X⟧) :
    twistSeries (∑ n ∈ s, r n) x (∏ n ∈ s, c n) = ∏ n ∈ s, twistSeries (r n) x (c n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using twistSeries_zero_one x
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, prod_insert ha, twistSeries_mul, ih]

/-- The twist of `1 + y t` at rank one is `1 + (x + y) t`: the case of an invertible module,
`c(ℒ' ⊗ ℒ) = 1 + c₁(ℒ') + c₁(ℒ)`. -/
theorem twistSeries_one_add_monomial (x y : R) :
    twistSeries 1 x (1 + monomial 1 y) = 1 + monomial 1 (x + y) := by
  rw [twistSeries_add, one_eq_monomial_zero, twistSeries_monomial, twistSeries_monomial]
  have h2 : ∀ n : ℕ, Ring.choose (1 : ℤ) (n + 2) = 0 := fun n => by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, Ring.choose_natCast]
    simp [Nat.choose_eq_zero_of_lt]
  ext n
  rw [map_add, map_add, coeff_monomial_mul', coeff_monomial_mul', coeff_monomial,
    coeff_monomial]
  rcases n with _ | _ | n
  · simp [coeff_twistBinomial]
  · simp [coeff_twistBinomial]
  · simp [coeff_twistBinomial, h2, Ring.choose_zero_succ]

end Stacks.Chow

end
