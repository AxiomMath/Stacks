module

public import StacksFrontier.NumberTheory.TraceFormula.SimultaneousPowersSector
public import StacksFrontier.RingTheory.Polynomial.ReciprocalIntegral
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The archimedean bound on Frobenius eigenvalues from point counts

Let `α_1, …, α_n` be complex numbers, let `q ≥ 2`, and let `N : ℕ → ℕ` satisfy

`N m = 1 - ∑_i α_i^m + q^m` for every `m ≥ 1`.

If the `N m` are nondecreasing along divisibility and unbounded, and the family `α` is stable
under complex conjugation, then `‖α_i‖ < q` for every `i`.  This is the archimedean half of
Tag 03V8: the `N m` are the numbers of rational points of a curve over the extensions of the
ground field, the `α_i` are the eigenvalues of geometric Frobenius on the first cohomology, and
the three extra properties hold for a reason the geometry supplies — the point counts are
nonnegative integers, `X(k_m) ⊆ X(k_{mn})`, the curve has more and more points, and the
characteristic polynomial has integer coefficients.

The argument is the one the source indicates.  Simultaneous Dirichlet approximation
(Exercise 03V9, `Stacks.TraceFormula.exists_le_pow_mem_sector`) produces arbitrarily large `m`
for which *every* `α_i^m` lies in a narrow sector about the positive real axis, so that the real
part of `∑_i α_i^m` is bounded below by a positive multiple of `∑_i ‖α_i‖^m`.  Against the upper
bound `∑_i α_i^m ≤ 1 + q^m` coming from `N m ≥ 0` this forces `‖α_i‖ ≤ q`, and then forces at
most one `α_i` to have `‖α_i‖ = q`.  Conjugation stability makes that one real, hence `± q`, and
then the same sector estimate applied to the other eigenvalues makes them all of absolute value
at most `1`, so the point counts over the extensions of even degree are bounded — which
monotonicity spreads to all degrees, contradicting unboundedness.

## Main results

* `Stacks.TraceFormula.mul_norm_le_re_of_abs_arg_le`: a complex number with argument of absolute
  value at most `π / 6` has real part at least `3 / 4` of its modulus.
* `Stacks.TraceFormula.exists_even_le_sum_pow_re`: for arbitrarily large even `m` the real part
  of `∑_{i ∈ s} α_i^m` is at least `3 / 4 * ∑_{i ∈ s} ‖α_i‖^m`.
* `Stacks.TraceFormula.le_of_forall_exists_pow_le`: a real `x` with `x ^ m ≤ C * q ^ m` for
  arbitrarily large `m` satisfies `x ≤ q`.
* `Stacks.TraceFormula.exists_conj_eq_of_monic_map_eq_prod`: the roots of a monic integral
  polynomial are stable under complex conjugation.
* `Stacks.TraceFormula.norm_lt_of_pointCount`: the bound `‖α_i‖ < q`.

## References

* [Stacks Project, Tag 03V8](https://stacks.math.columbia.edu/tag/03V8), part (4).
* [Stacks Project, Tag 03V9](https://stacks.math.columbia.edu/tag/03V9), the sector lemma the
  source tells us to use.
-/

@[expose] public noncomputable section

namespace Stacks.TraceFormula

open Complex Finset Polynomial

/-! ### A sector bound on the real part -/

/-- A complex number whose argument has absolute value at most `π / 6` has real part at least
`3 / 4` of its modulus.  The constant is `cos (π / 6) = √3 / 2 ≥ 3 / 4`. -/
public theorem mul_norm_le_re_of_abs_arg_le {z : ℂ} (h : |z.arg| ≤ Real.pi / 6) :
    3 / 4 * ‖z‖ ≤ z.re := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hsqrt : (3 : ℝ) / 2 ≤ Real.sqrt 3 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hcos : (3 : ℝ) / 4 ≤ Real.cos z.arg := by
    refine le_trans ?_ (Real.cos_abs z.arg ▸
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) h)
    rw [Real.cos_pi_div_six]
    linarith
  have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  rw [Complex.cos_arg hz, le_div_iff₀ hn] at hcos
  linarith

/-- For arbitrarily large **even** exponents `m`, the real part of `∑_{i ∈ s} α_i^m` is at least
`3 / 4` of `∑_{i ∈ s} ‖α_i‖^m`: the sector lemma puts every `α_i^m` simultaneously into the
sector of half-angle `π / 6`, where the real part dominates the modulus. -/
public theorem exists_even_le_sum_pow_re {ι : Type*} [Finite ι] (α : ι → ℂ) (s : Finset ι)
    (n : ℕ) :
    ∃ m : ℕ, n + 1 ≤ m ∧ Even m ∧
      3 / 4 * ∑ i ∈ s, ‖α i‖ ^ m ≤ (∑ i ∈ s, α i ^ m).re := by
  obtain ⟨k, hk, hsector⟩ :=
    exists_le_pow_mem_sector (fun i => α i ^ 2) (by positivity : (0 : ℝ) < Real.pi / 6) n
  refine ⟨2 * k, by omega, even_two_mul k, ?_⟩
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have harg : |(α i ^ (2 * k)).arg| ≤ Real.pi / 6 := by
    rw [pow_mul]
    exact le_of_lt (hsector i)
  simpa [norm_pow] using mul_norm_le_re_of_abs_arg_le harg

/-! ### Growth -/

/-- If `x ^ m ≤ C * q ^ m` for arbitrarily large `m`, then `x ≤ q`. -/
public theorem le_of_forall_exists_pow_le {x q C : ℝ} (hq : 0 < q)
    (h : ∀ n : ℕ, ∃ m : ℕ, n + 1 ≤ m ∧ x ^ m ≤ C * q ^ m) : x ≤ q := by
  by_contra hlt
  rw [not_le] at hlt
  have hratio : 1 < x / q := (one_lt_div hq).2 hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hratio
  obtain ⟨m, hm, hle⟩ := h n
  have hmono : (x / q) ^ n ≤ (x / q) ^ m :=
    pow_le_pow_right₀ (le_of_lt hratio) (by omega)
  have hdiv : (x / q) ^ m ≤ C := by
    rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < q ^ m)]
    exact hle
  linarith

/-! ### Conjugation stability of integral roots -/

/-- The roots of a monic polynomial with integer coefficients are stable under complex
conjugation: if `∏_j (T - α_j)` is the image of such a polynomial, then the conjugate of each
`α_i` is again one of the `α_j`. -/
public theorem exists_conj_eq_of_monic_map_eq_prod {ι : Type*} [Fintype ι] (α : ι → ℂ)
    {Q : ℤ[X]} (hmonic : Q.Monic)
    (hmap : Q.map (Int.castRingHom ℂ) = ∏ j, (X - C (α j))) (i : ι) :
    ∃ i', α i' = (starRingEnd ℂ) (α i) := by
  classical
  have hzero : eval (α i) (Q.map (Int.castRingHom ℂ)) = 0 := by
    rw [hmap, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hconjzero : eval ((starRingEnd ℂ) (α i)) (Q.map (Int.castRingHom ℂ)) = 0 := by
    have hcomp : (starRingEnd ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ :=
      RingHom.ext_int _ _
    have h := Polynomial.hom_eval₂ Q (Int.castRingHom ℂ) (starRingEnd ℂ) (α i)
    rw [hcomp] at h
    rw [eval_map, ← h, ← eval_map, hzero, map_zero]
  have hprod : (∏ j, (X - C (α j))) = (Multiset.map (fun a : ℂ => X - C a)
      (Multiset.map α Finset.univ.val)).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  have hne : (∏ j, (X - C (α j))) ≠ 0 := by
    rw [← hmap]
    exact hmonic.map (Int.castRingHom ℂ) |>.ne_zero
  have hmem : (starRingEnd ℂ) (α i) ∈ (∏ j, (X - C (α j))).roots := by
    rw [Polynomial.mem_roots hne]
    rw [← hmap]
    exact hconjzero
  rw [hprod, Polynomial.roots_multiset_prod_X_sub_C] at hmem
  obtain ⟨i', -, hi'⟩ := Multiset.mem_map.1 hmem
  exact ⟨i', hi'⟩

/-! ### The bound -/

/-- **Tag 03V8, part (4), as a statement about the point counts.**  Let `α : ι → ℂ` be a finite
family, `q ≥ 2`, and `N : ℕ → ℕ` with `N m = 1 - ∑_i α_i^m + q^m` for `m ≥ 1`.  If the `N m`
are nondecreasing along divisibility and unbounded, and the family `α` is stable under complex
conjugation, then `‖α i‖ < q` for every `i`. -/
public theorem norm_lt_of_pointCount {ι : Type*} [Fintype ι] (α : ι → ℂ) {q : ℕ} (hq : 1 < q)
    (N : ℕ → ℕ)
    (hN : ∀ m : ℕ, m ≠ 0 → (N m : ℂ) = 1 - (∑ i, α i ^ m) + (q : ℂ) ^ m)
    (hmono : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → N m ≤ N (m * n))
    (hunbdd : ∀ C : ℕ, ∃ m : ℕ, m ≠ 0 ∧ C < N m)
    (hconj : ∀ i, ∃ i', α i' = (starRingEnd ℂ) (α i)) (i : ι) : ‖α i‖ < (q : ℝ) := by
  classical
  have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.le
  have hqre : ∀ m : ℕ, ((q : ℂ) ^ m).re = (q : ℝ) ^ m := fun m => by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
  -- The sum of `m`-th powers is the real number `1 + q ^ m - N m`.
  have hsum : ∀ m : ℕ, m ≠ 0 → (∑ i, α i ^ m).re = 1 + (q : ℝ) ^ m - N m := by
    intro m hm
    have h : (∑ i, α i ^ m) = 1 + (q : ℂ) ^ m - (N m : ℂ) := by
      linear_combination hN m hm
    rw [h, Complex.sub_re, Complex.add_re, hqre, Complex.one_re, Complex.natCast_re]
  have hsingle : ∀ (u : Finset ι) (m : ℕ), ∀ j ∈ u, ‖α j‖ ^ m ≤ ∑ i ∈ u, ‖α i‖ ^ m :=
    fun u m j hj => Finset.single_le_sum (f := fun i => ‖α i‖ ^ m) (fun i _ => by positivity) hj
  have hsumle : ∀ m : ℕ, m ≠ 0 → (∑ i, α i ^ m).re ≤ 1 + (q : ℝ) ^ m := by
    intro m hm
    rw [hsum m hm]
    have : (0 : ℝ) ≤ N m := Nat.cast_nonneg _
    linarith
  -- Step 1: every eigenvalue has absolute value at most `q`.
  have hstep1 : ∀ j, ‖α j‖ ≤ (q : ℝ) := by
    intro j
    refine le_of_forall_exists_pow_le hq0 (C := 8 / 3) fun n => ?_
    obtain ⟨m, hm, -, hle⟩ := exists_even_le_sum_pow_re α Finset.univ n
    refine ⟨m, hm, ?_⟩
    have hone : (1 : ℝ) ≤ (q : ℝ) ^ m := one_le_pow₀ hq1
    have := hsumle m (by omega)
    nlinarith [hle, hsingle Finset.univ m j (Finset.mem_univ j), hone]
  -- Step 2: at most one eigenvalue has absolute value exactly `q`.
  set s : Finset ι := Finset.univ.filter fun j => ‖α j‖ = (q : ℝ) with hs
  have hcard : s.card ≤ 1 := by
    by_contra hc
    rw [not_le] at hc
    obtain ⟨m, hm, -, hle⟩ := exists_even_le_sum_pow_re α Finset.univ 2
    have hsub : ∑ j ∈ s, ‖α j‖ ^ m ≤ ∑ j, ‖α j‖ ^ m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun j _ _ => by positivity
    have heq : ∑ j ∈ s, ‖α j‖ ^ m = s.card * (q : ℝ) ^ m := by
      rw [Finset.sum_congr rfl fun j hj => by
        rw [(Finset.mem_filter.1 hj).2], Finset.sum_const, nsmul_eq_mul]
    have hcard2 : (2 : ℝ) ≤ s.card := by exact_mod_cast hc
    have hqm : (4 : ℝ) ≤ (q : ℝ) ^ m := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ (q : ℝ) ^ 2 := by
            have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
            nlinarith
        _ ≤ (q : ℝ) ^ m := pow_le_pow_right₀ hq1 (by omega)
    have := hsumle m (by omega)
    nlinarith [hle, hsub, heq, hcard2, hqm]
  -- Step 3: if some eigenvalue has absolute value `q`, that one is real, hence `± q`.
  rcases lt_or_eq_of_le (hstep1 i) with hlt | heq
  · exact hlt
  exfalso
  have hmemi : i ∈ s := Finset.mem_filter.2 ⟨Finset.mem_univ i, heq⟩
  obtain ⟨i', hi'⟩ := hconj i
  have hmemi' : i' ∈ s := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ i', ?_⟩
    rw [hi', Complex.norm_conj, heq]
  have hii' : i' = i := Finset.card_le_one.1 hcard i' hmemi' i hmemi
  have hreal : (starRingEnd ℂ) (α i) = α i := by rw [← hi', hii']
  have hsq : α i ^ 2 = (q : ℂ) ^ 2 := by
    have h1 : α i * (starRingEnd ℂ) (α i) = (‖α i‖ : ℂ) ^ 2 := Complex.mul_conj' (α i)
    rw [hreal] at h1
    rw [sq, h1, heq]
    push_cast
    ring
  have hpow : ∀ m : ℕ, Even m → α i ^ m = (q : ℂ) ^ m := by
    intro m hm
    obtain ⟨c, rfl⟩ := hm
    rw [show c + c = 2 * c by omega, pow_mul, pow_mul, hsq]
  -- Step 4: the remaining eigenvalues then have absolute value at most one.
  set t : Finset ι := Finset.univ.erase i with ht
  have hsplit : ∀ m : ℕ, m ≠ 0 → Even m → (∑ j ∈ t, α j ^ m).re = 1 - N m := by
    intro m hm hev
    have hadd : α i ^ m + ∑ j ∈ t, α j ^ m = ∑ j, α j ^ m :=
      Finset.add_sum_erase Finset.univ (fun j => α j ^ m) (Finset.mem_univ i)
    have hre : (∑ j ∈ t, α j ^ m).re = (∑ j, α j ^ m).re - (α i ^ m).re := by
      rw [← hadd]
      simp
    rw [hre, hsum m hm, hpow m hev, hqre]
    ring
  have hstep4 : ∀ j ∈ t, ‖α j‖ ≤ 1 := by
    intro j hj
    refine le_of_forall_exists_pow_le one_pos (C := 4 / 3) fun n => ?_
    obtain ⟨m, hm, hev, hle⟩ := exists_even_le_sum_pow_re α t n
    refine ⟨m, hm, ?_⟩
    have hb := hsplit m (by omega) hev
    have hNnn : (0 : ℝ) ≤ N m := Nat.cast_nonneg _
    rw [hb] at hle
    simp only [one_pow, mul_one]
    nlinarith [hle, hsingle t m j hj, hNnn]
  -- Step 5: hence the point counts over the even-degree extensions are bounded.
  have hbound : ∀ m : ℕ, m ≠ 0 → Even m → (N m : ℝ) ≤ 1 + Fintype.card ι := by
    intro m hm hev
    have hb := hsplit m hm hev
    have h1 : |(∑ j ∈ t, α j ^ m).re| ≤ ‖∑ j ∈ t, α j ^ m‖ := Complex.abs_re_le_norm _
    have h2 : ‖∑ j ∈ t, α j ^ m‖ ≤ ∑ j ∈ t, ‖α j ^ m‖ := norm_sum_le _ _
    have h3 : ∑ j ∈ t, ‖α j ^ m‖ ≤ ∑ _j ∈ t, (1 : ℝ) :=
      Finset.sum_le_sum fun j hj => by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (hstep4 j hj)
    have h4 : ∑ _j ∈ t, (1 : ℝ) = (t.card : ℝ) := by simp
    have h5 : t.card ≤ Fintype.card ι := by
      rw [ht, ← Finset.card_univ]
      exact Finset.card_erase_le
    have h5' : (t.card : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast h5
    have habs : |(∑ j ∈ t, α j ^ m).re| ≤ (Fintype.card ι : ℝ) := by linarith
    rw [hb] at habs
    have := abs_le.1 habs
    linarith [this.1]
  -- Step 6: monotonicity spreads the bound to all degrees, contradicting unboundedness.
  obtain ⟨m, hm, hlt⟩ := hunbdd (1 + Fintype.card ι)
  have h2m : N m ≤ N (m * 2) := hmono m 2 hm two_ne_zero
  have hev : Even (m * 2) := by exact ⟨m, by ring⟩
  have hb := hbound (m * 2) (by positivity) hev
  have : ((1 + Fintype.card ι : ℕ) : ℝ) < N m := by exact_mod_cast hlt
  have hcast : (N m : ℝ) ≤ (N (m * 2) : ℝ) := by exact_mod_cast h2m
  push_cast at this
  linarith

end Stacks.TraceFormula

end
