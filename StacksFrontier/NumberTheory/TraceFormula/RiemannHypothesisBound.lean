module

public import StacksFrontier.NumberTheory.TraceFormula.EigenvalueAbsoluteBound

/-!
# The Riemann hypothesis from a square-root bound on point counts

Let `α_1, …, α_r` be complex numbers and `B > 0`. If the power sums satisfy
`‖∑_i α_i^m‖ ≤ C · B^m` for all large `m` in an arithmetic progression `d ℕ`, then every `α_i`
has `‖α_i‖ ≤ B`. This is the passage, in the elementary proof of the Riemann hypothesis for a
curve over a finite field with `q` elements, from the Bombieri–Stepanov estimate
`|#X(k_m) - q^m - 1| ≤ C · q^{m/2}` to the eigenvalue bound `‖α_i‖ ≤ √q`. The point counts are
`#X(k_m) = 1 - ∑_i α_i^m + q^m` (Tag 03V8, part (3)), so the estimate bounds the power sums.

The argument is the sector argument of Exercise 03V9, as in part (4) of Tag 03V8. There are
arbitrarily large exponents `m` at which every `α_i^{d m}` lies in a narrow sector about the
positive real axis. At such an exponent the real part of the power sum dominates
`(3/4) ∑_i ‖α_i‖^{d m}`, so no cancellation can hide an eigenvalue of absolute value above `B`.

The opposite inequality comes from the functional equation. The eigenvalues are permuted by
`α ↦ q / α`, so every `α_i` has a partner `α_j` with `α_i α_j = q`. Then `‖α_i‖ ≥ √q` follows from
`‖α_j‖ ≤ √q`.

## Main results

* `Stacks.TraceFormula.norm_le_of_norm_sum_pow_le` — power sums bounded by `C · B^m` along `d ℕ`
  force `‖α_i‖ ≤ B`.
* `Stacks.TraceFormula.norm_le_sqrt_of_pointCount` — a point count `1 - ∑ α_i^m + q^m` within
  `C · √q^m` of `q^m + 1` forces `‖α_i‖ ≤ √q`.
* `Stacks.TraceFormula.norm_eq_sqrt_of_pointCount` — with the pairing `α_i α_j = q` of the
  functional equation, `‖α_i‖ = √q`: the Riemann hypothesis.
* `Stacks.TraceFormula.norm_eq_sqrt_of_upper_lower` — the same from the two one-sided bounds.
* `Stacks.TraceFormula.pow_ne_one_of_norm_eq_sqrt` and
  `Stacks.TraceFormula.pow_ne_one_of_pairing_of_norm_lt` — no power of an eigenvalue is `1`. The
  first follows from the Riemann hypothesis. The second needs only the pairing and the bound
  `‖α‖ < q` of Tag 03V8, part (4).

## References

* [Stacks Project, Tag 03V8](https://stacks.math.columbia.edu/tag/03V8), parts (3) and (4).
* [Stacks Project, Tag 03V9](https://stacks.math.columbia.edu/tag/03V9), the sector lemma.
* E. Bombieri, *Counting points on curves over finite fields (d'après S. A. Stepanov)*,
  Séminaire Bourbaki 430 (1973).
-/

@[expose] public noncomputable section

namespace Stacks.TraceFormula

open Complex Finset

variable {ι : Type*} [Fintype ι]

/-- **Power sums control the eigenvalues.** If `‖∑_i α_i^m‖ ≤ C · B^m` for every `m ≥ m₀`
divisible by `d ≠ 0`, then `‖α_i‖ ≤ B` for every `i`. The sector lemma, applied to the family
`α_i^d`, gives arbitrarily large exponents at which the real part of the power sum is at least
`3/4` of `∑_i ‖α_i‖^{d m}`. -/
public theorem norm_le_of_norm_sum_pow_le (α : ι → ℂ) {B C : ℝ} (hB : 0 < B) {d : ℕ}
    (hd : d ≠ 0) (m₀ : ℕ) (h : ∀ m : ℕ, m₀ ≤ m → d ∣ m → ‖∑ i, α i ^ m‖ ≤ C * B ^ m)
    (i : ι) : ‖α i‖ ≤ B := by
  have hBd : 0 < B ^ d := pow_pos hB d
  have hle : ‖α i‖ ^ d ≤ B ^ d := by
    refine le_of_forall_exists_pow_le hBd (C := 4 / 3 * C) fun n => ?_
    obtain ⟨m, hm, -, hsec⟩ := exists_even_le_sum_pow_re (fun j => α j ^ d) Finset.univ
      (max n m₀)
    refine ⟨m, by omega, ?_⟩
    have hdm : m₀ ≤ d * m := by
      have : m ≤ d * m := Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hd)
      omega
    have hbound := h (d * m) hdm (dvd_mul_right d m)
    have hpow : ∀ j, (α j ^ d) ^ m = α j ^ (d * m) := fun j => (pow_mul _ _ _).symm
    simp only [hpow] at hsec
    have hre : (∑ j, α j ^ (d * m)).re ≤ ‖∑ j, α j ^ (d * m)‖ := Complex.re_le_norm _
    have hsingle : ‖α i ^ d‖ ^ m ≤ ∑ j, ‖α j ^ d‖ ^ m :=
      Finset.single_le_sum (f := fun j => ‖α j ^ d‖ ^ m) (fun j _ => by positivity)
        (Finset.mem_univ i)
    rw [norm_pow] at hsingle
    rw [← pow_mul B]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB.le hd).1 hle

/-- **The eigenvalue bound from a square-root estimate on point counts.** Let `q > 0` and
`N m = 1 - ∑_i α_i^m + q^m` for `m ≥ 1`. If `|N m - q^m - 1| ≤ C · √q^m` for every `m ≥ m₀`
divisible by `d ≠ 0`, then `‖α_i‖ ≤ √q`. -/
public theorem norm_le_sqrt_of_pointCount (α : ι → ℂ) {q : ℕ} (hq : 0 < q) (N : ℕ → ℕ)
    (hN : ∀ m : ℕ, m ≠ 0 → (N m : ℂ) = 1 - (∑ i, α i ^ m) + (q : ℂ) ^ m) {C : ℝ} {d : ℕ}
    (hd : d ≠ 0) (m₀ : ℕ)
    (hbound : ∀ m : ℕ, m₀ ≤ m → d ∣ m →
      |(N m : ℝ) - (q : ℝ) ^ m - 1| ≤ C * Real.sqrt q ^ m) (i : ι) :
    ‖α i‖ ≤ Real.sqrt q := by
  refine norm_le_of_norm_sum_pow_le α (C := C) (Real.sqrt_pos.2 (by exact_mod_cast hq)) hd
    (m₀ + 1)
    (fun m hm hdm => ?_) i
  have hm0 : m ≠ 0 := by omega
  have hsum : (∑ j, α j ^ m) = (((q : ℝ) ^ m + 1 - N m : ℝ) : ℂ) := by
    push_cast
    linear_combination hN m hm0
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have := hbound m (by omega) hdm
  calc |(N m : ℝ) - ((q : ℝ) ^ m + 1)| = |(N m : ℝ) - (q : ℝ) ^ m - 1| := by ring_nf
    _ ≤ C * Real.sqrt q ^ m := this

/-- **The Riemann hypothesis from the point-count estimate and the functional equation.** Let
`q > 0` and `N m = 1 - ∑_i α_i^m + q^m` for `m ≥ 1`. Suppose `|N m - q^m - 1| ≤ C · √q^m` for
every `m ≥ m₀` divisible by `d ≠ 0`. Suppose also that every `α_i` has a partner `α_j` with
`α_i α_j = q`, as the functional equation of the zeta function provides. Then `‖α_i‖ = √q`. -/
public theorem norm_eq_sqrt_of_pointCount (α : ι → ℂ) {q : ℕ} (hq : 0 < q) (N : ℕ → ℕ)
    (hN : ∀ m : ℕ, m ≠ 0 → (N m : ℂ) = 1 - (∑ i, α i ^ m) + (q : ℂ) ^ m) {C : ℝ} {d : ℕ}
    (hd : d ≠ 0) (m₀ : ℕ)
    (hbound : ∀ m : ℕ, m₀ ≤ m → d ∣ m →
      |(N m : ℝ) - (q : ℝ) ^ m - 1| ≤ C * Real.sqrt q ^ m)
    (hpair : ∀ i, ∃ j, α i * α j = q) (i : ι) : ‖α i‖ = Real.sqrt q := by
  have hle := norm_le_sqrt_of_pointCount α hq N hN hd m₀ hbound
  refine le_antisymm (hle i) ?_
  obtain ⟨j, hj⟩ := hpair i
  have hprod : ‖α i‖ * ‖α j‖ = Real.sqrt q * Real.sqrt q := by
    rw [← norm_mul, hj, Complex.norm_natCast, Real.mul_self_sqrt (Nat.cast_nonneg q)]
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq)
  by_contra hlt
  rw [not_le] at hlt
  nlinarith [hle j, norm_nonneg (α i), norm_nonneg (α j)]

/-- Under the Riemann hypothesis `‖α‖ = √q` with `q ≥ 2`, no positive power of `α` is `1`: the
eigenvalues of Frobenius on `H¹` of a curve are not roots of unity. -/
public theorem pow_ne_one_of_norm_eq_sqrt {α : ℂ} {q : ℕ} (hq : 1 < q)
    (hα : ‖α‖ = Real.sqrt q) {m : ℕ} (hm : m ≠ 0) : α ^ m ≠ 1 := by
  intro h
  rw [norm_eq_one_of_pow_eq_one h hm] at hα
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have : (1 : ℝ) < Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one hq1
  linarith

omit [Fintype ι] in
/-- **No root-of-unity eigenvalue without the Riemann hypothesis.** Let every `α_i` have a
partner `α_j` with `α_i α_j = q`, and let `‖α_j‖ < q` for every `j` (Tag 03V8, part (4)). Then
no positive power of any `α_i` is `1`. If `α_i` were a root of unity, its partner would have
absolute value `q`. -/
public theorem pow_ne_one_of_pairing_of_norm_lt (α : ι → ℂ) {q : ℕ}
    (hpair : ∀ i, ∃ j, α i * α j = q) (hlt : ∀ j, ‖α j‖ < q) (i : ι) {m : ℕ} (hm : m ≠ 0) :
    α i ^ m ≠ 1 := by
  intro h
  have hn := norm_eq_one_of_pow_eq_one h hm
  obtain ⟨j, hj⟩ := hpair i
  have : ‖α j‖ = q := by
    have := congrArg norm hj
    rwa [norm_mul, hn, one_mul, Complex.norm_natCast] at this
  exact (lt_irrefl _ (this ▸ hlt j))

/-- **The Riemann hypothesis from one-sided bounds.** Let `q > 0` and
`N m = 1 - ∑_i α_i^m + q^m` for `m ≥ 1`. Suppose that, for all `m ≥ m₀` divisible by `d ≠ 0`,
the upper bound `N m ≤ q^m + C · √q^m` (Bombieri–Stepanov) and the lower bound
`q^m ≤ N m + C · √q^m` hold. Suppose also the pairing `α_i α_j = q`. Then `‖α_i‖ = √q`. The two
one-sided bounds combine into the two-sided estimate of `norm_eq_sqrt_of_pointCount`; the
constant absorbs the `1`. -/
public theorem norm_eq_sqrt_of_upper_lower (α : ι → ℂ) {q : ℕ} (hq : 0 < q) (N : ℕ → ℕ)
    (hN : ∀ m : ℕ, m ≠ 0 → (N m : ℂ) = 1 - (∑ i, α i ^ m) + (q : ℂ) ^ m) {C : ℝ} {d : ℕ}
    (hd : d ≠ 0) (m₀ : ℕ)
    (hupper : ∀ m : ℕ, m₀ ≤ m → d ∣ m → (N m : ℝ) ≤ (q : ℝ) ^ m + C * Real.sqrt q ^ m)
    (hlower : ∀ m : ℕ, m₀ ≤ m → d ∣ m → (q : ℝ) ^ m ≤ N m + C * Real.sqrt q ^ m)
    (hpair : ∀ i, ∃ j, α i * α j = q) (i : ι) : ‖α i‖ = Real.sqrt q := by
  refine norm_eq_sqrt_of_pointCount α hq N hN (C := C + 1) hd m₀ (fun m hm hdm => ?_) hpair i
  have hs : 1 ≤ Real.sqrt q ^ m := one_le_pow₀ (by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq))
  have h1 := hupper m hm hdm
  have h2 := hlower m hm hdm
  rw [abs_le]
  constructor <;> nlinarith

end Stacks.TraceFormula

end
