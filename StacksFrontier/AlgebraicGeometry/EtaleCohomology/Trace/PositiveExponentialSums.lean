module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Multiset.Fintype
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Exponential sums with a sign

If `a` and `b` are finite families of complex numbers, every `a i` has absolute value at most
`R`, and the real part of `∑ i, a i ^ n - ∑ k, b k ^ n` is eventually nonnegative, then every
`b k` has absolute value at most `R`. This is the statement about exponential sums behind
Deligne's positivity argument in Weil II (Lemme 1.5.2, the analogue of Rankin's squaring trick).

## Main results

* `Stacks.EtaleCohomology.exists_pow_near_one`: finitely many complex numbers of absolute value
  `1` have, for arbitrarily large `n`, their `n`-th powers simultaneously within `ε` of `1`.
* `Stacks.EtaleCohomology.norm_le_of_eventually_re_sum_pow_sub_sum_pow_nonneg`: the bound
  above.
* `Stacks.EtaleCohomology.norm_le_pow_of_eventually_re_sum_pow_sub_sum_pow_ge`: the form used in
  Rankin's lemma, where the sum in degree `d * n` dominates `d` times a power sum in degree `n`
  (one closed point of degree `d`).
* `Stacks.EtaleCohomology.norm_le_of_forall_rankin`: Deligne's Lemme 1.5.2 for exponential sums:
  if for every `i ≥ 1` a difference of power sums in degree `d n`, whose first family is bounded
  by `q ^ (1 + i w)`, dominates `d` times the `2i`-th power of `∑ j, α j ^ n`, then
  `|α| ≤ q ^ (d w / 2)`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), Lemme 1.5.2.
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open Filter Topology

namespace Stacks.EtaleCohomology

/-- **Simultaneous recurrence on the torus.**  For finitely many complex numbers `z i` of
absolute value `1`, every `ε > 0` and every `N₀`, there is `n ≥ N₀` such that every `z i ^ n` is
within `ε` of `1`. -/
public theorem exists_pow_near_one {ι : Type*} [Finite ι] {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) (N₀ : ℕ) : ∃ n ≥ N₀, ∀ i, ‖z i ^ n - 1‖ < ε := by
  have := Fintype.ofFinite ι
  let x : ℕ → (ι → ℂ) := fun n i => z i ^ n
  have hx : ∀ n, x n ∈ Metric.closedBall (0 : ι → ℂ) 1 := fun n => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    simp [x, norm_pow, hz]
  obtain ⟨p, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ι → ℂ) 1).tendsto_subseq hx
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (half_pos hε)
  have h1 := hK K le_rfl
  have h2 := hK (N₀ + K) (Nat.le_add_left _ _)
  have hle : N₀ + φ K ≤ φ (N₀ + K) := hφ.add_le_nat N₀ K
  refine ⟨φ (N₀ + K) - φ K, by omega, fun i => ?_⟩
  have hd : dist (x (φ (N₀ + K))) (x (φ K)) < ε := by
    calc dist (x (φ (N₀ + K))) (x (φ K))
        ≤ dist (x (φ (N₀ + K))) p + dist (x (φ K)) p := dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h2 h1
      _ = ε := add_halves ε
  have hdi : ‖z i ^ φ (N₀ + K) - z i ^ φ K‖ < ε := by
    have := (dist_le_pi_dist (x (φ (N₀ + K))) (x (φ K)) i).trans_lt hd
    simpa [x, dist_eq_norm] using this
  have hsplit : z i ^ φ (N₀ + K) = z i ^ (φ (N₀ + K) - φ K) * z i ^ φ K := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have hfac : z i ^ φ (N₀ + K) - z i ^ φ K = (z i ^ (φ (N₀ + K) - φ K) - 1) * z i ^ φ K := by
    rw [hsplit]
    ring
  rwa [hfac, norm_mul, norm_pow, hz i, one_pow, mul_one] at hdi

/-- **A sign condition bounds the subtracted terms.**  Let `a` and `b` be finite families of
complex numbers and `0 ≤ R`.  If every `a i` has absolute value at most `R` and the real part of
`∑ i, a i ^ n - ∑ k, b k ^ n` is nonnegative for all large `n`, then every `b k` has absolute
value at most `R`. -/
public theorem norm_le_of_eventually_re_sum_pow_sub_sum_pow_nonneg {ι κ : Type*} [Fintype ι]
    [Fintype κ] {a : ι → ℂ} {b : κ → ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : ∀ i, ‖a i‖ ≤ R)
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ (∑ i, a i ^ n - ∑ k, b k ^ n).re) (k : κ) : ‖b k‖ ≤ R := by
  classical
  by_contra hk
  push Not at hk
  have : Nonempty κ := ⟨k⟩
  obtain ⟨k₀, hk₀⟩ := Finite.exists_max fun k => ‖b k‖
  set ρ := ‖b k₀‖ with hρdef
  have hRρ : R < ρ := hk.trans_le (hk₀ k)
  have hρ : 0 < ρ := hR.trans_lt hRρ
  let T := {k : κ // ‖b k‖ = ρ}
  let z : T → ℂ := fun t => b t.1 / ρ
  have hz : ∀ t, ‖z t‖ = 1 := fun t => by
    simp only [z, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, t.2,
      div_self hρ.ne']
  let c : ℕ → ℝ := fun n => Fintype.card ι * (R / ρ) ^ n +
    ∑ k, if ‖b k‖ < ρ then (‖b k‖ / ρ) ^ n else 0
  have hc : Tendsto c atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (Fintype.card ι : ℝ) * (R / ρ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR hρ.le)
        ((div_lt_one hρ).2 hRρ)).const_mul (Fintype.card ι : ℝ)
    have h2 : Tendsto (fun n : ℕ => ∑ k, if ‖b k‖ < ρ then (‖b k‖ / ρ) ^ n else 0) atTop
        (𝓝 0) := by
      have hterm : ∀ k ∈ (Finset.univ : Finset κ), Tendsto
          (fun n : ℕ => if ‖b k‖ < ρ then (‖b k‖ / ρ) ^ n else 0) atTop (𝓝 0) := by
        intro k _
        by_cases hk : ‖b k‖ < ρ
        · simp only [hk, ite_true]
          exact tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg (norm_nonneg _) hρ.le)
            ((div_lt_one hρ).2 hk)
        · simp only [hk, ite_false]
          exact tendsto_const_nhds
      simpa using tendsto_finsetSum _ hterm
    simpa using h1.add h2
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    ((hc.eventually (eventually_lt_nhds (half_pos one_pos : (0 : ℝ) < 1 / 2))).and h)
  obtain ⟨n, hn, hnear⟩ := exists_pow_near_one hz (half_pos one_pos) N₀
  obtain ⟨hcn, hsign⟩ := hN₀ n hn
  have hρn : 0 < ρ ^ n := pow_pos hρ n
  have hA : (∑ i, a i ^ n).re ≤ Fintype.card ι * R ^ n := by
    rw [Complex.re_sum]
    calc ∑ i, (a i ^ n).re ≤ ∑ _i : ι, R ^ n := Finset.sum_le_sum fun i _ =>
          (Complex.re_le_norm _).trans
            (by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (ha i) n)
      _ = Fintype.card ι * R ^ n := by simp
  have hT : ∀ k, ‖b k‖ = ρ → ρ ^ n / 2 < (b k ^ n).re := fun k hk => by
    have hnk := hnear ⟨k, hk⟩
    have hbk : b k ^ n = (ρ : ℂ) ^ n * z ⟨k, hk⟩ ^ n := by
      simp only [z, div_pow]
      rw [mul_div_cancel₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.2 hρ.ne'))]
    have hre : (b k ^ n).re = ρ ^ n * (z ⟨k, hk⟩ ^ n).re := by
      rw [hbk, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    have hzre : 1 / 2 < (z ⟨k, hk⟩ ^ n).re := by
      have h1 : |(z ⟨k, hk⟩ ^ n - 1).re| < 1 / 2 := (Complex.abs_re_le_norm _).trans_lt hnk
      rw [Complex.sub_re, Complex.one_re] at h1
      linarith [(abs_lt.1 h1).1]
    rw [hre]
    nlinarith
  let e : κ → ℝ := fun k => -(b k ^ n).re - ρ ^ n * if ‖b k‖ < ρ then (‖b k‖ / ρ) ^ n else 0
  have he : ∀ k, e k ≤ 0 := fun k => by
    by_cases hk : ‖b k‖ < ρ
    · simp only [e, hk, ite_true, div_pow, mul_div_cancel₀ _ hρn.ne']
      have := neg_abs_le (b k ^ n).re
      have h2 := Complex.abs_re_le_norm (b k ^ n)
      rw [norm_pow] at h2
      linarith
    · have hkρ : ‖b k‖ = ρ := le_antisymm (hk₀ k) (not_lt.1 hk)
      simp only [e, hk, ite_false, mul_zero, sub_zero]
      linarith [hT k hkρ]
  have hek₀ : e k₀ < -(ρ ^ n / 2) := by
    have hk₀' : ¬ ‖b k₀‖ < ρ := lt_irrefl _
    simp only [e, hk₀', ite_false, mul_zero, sub_zero]
    linarith [hT k₀ rfl]
  have hsume : ∑ k, e k ≤ e k₀ := by
    have := Finset.single_le_sum (f := fun k => -e k) (fun k _ => neg_nonneg.2 (he k))
      (Finset.mem_univ k₀)
    simp only [Finset.sum_neg_distrib] at this
    linarith
  have hB : -(∑ k, b k ^ n).re = ∑ k, e k +
      ρ ^ n * ∑ k, if ‖b k‖ < ρ then (‖b k‖ / ρ) ^ n else 0 := by
    rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [e]; ring
  have hcn' : ρ ^ n * c n < ρ ^ n * (1 / 2) := mul_lt_mul_of_pos_left hcn hρn
  have hRn : (Fintype.card ι : ℝ) * R ^ n = ρ ^ n * (Fintype.card ι * (R / ρ) ^ n) := by
    rw [div_pow]
    field_simp
  rw [Complex.sub_re] at hsign
  simp only [c, mul_add] at hcn'
  linarith

/-- **Deligne's form of Rankin's lemma, for exponential sums.**  Let `a`, `b`, `g` be finite
families of complex numbers, `0 ≤ R`, every `a i` of absolute value at most `R`, and `0 < d`.
If for all large `n` the real part of `∑ i, a i ^ (d * n) - ∑ k, b k ^ (d * n)` dominates
`d` times that of `∑ m, g m ^ n`, then every `g m` (and every `b k ^ d`) has absolute value at
most `R ^ d`. -/
public theorem norm_le_pow_of_eventually_re_sum_pow_sub_sum_pow_ge {ι κ μ : Type*} [Fintype ι]
    [Fintype κ] [Fintype μ] {a : ι → ℂ} {b : κ → ℂ} {g : μ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (ha : ∀ i, ‖a i‖ ≤ R) {d : ℕ} (hd : 0 < d)
    (h : ∀ᶠ n : ℕ in atTop,
      (d : ℝ) * (∑ m, g m ^ n).re ≤ (∑ i, a i ^ (d * n) - ∑ k, b k ^ (d * n)).re) :
    (∀ m, ‖g m‖ ≤ R ^ d) ∧ ∀ k, ‖b k ^ d‖ ≤ R ^ d := by
  let b' : κ ⊕ (Fin d × μ) → ℂ := Sum.elim (fun k => b k ^ d) fun p => g p.2
  have ha' : ∀ i, ‖a i ^ d‖ ≤ R ^ d := fun i => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (ha i) d
  have h' : ∀ᶠ n : ℕ in atTop, 0 ≤ (∑ i, (a i ^ d) ^ n - ∑ k, b' k ^ n).re := by
    filter_upwards [h] with n hn
    have hsum : ∑ k, b' k ^ n = ∑ k, b k ^ (d * n) + (d : ℂ) * ∑ m, g m ^ n := by
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [b', Sum.elim_inl, Sum.elim_inr, ← pow_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hre : ((d : ℂ) * ∑ m, g m ^ n).re = (d : ℝ) * (∑ m, g m ^ n).re := by
      rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    simp only [← pow_mul] at hn ⊢
    rw [hsum, sub_add_eq_sub_sub, Complex.sub_re, hre]
    linarith
  have hb' := norm_le_of_eventually_re_sum_pow_sub_sum_pow_nonneg (pow_nonneg hR d) ha' h'
  refine ⟨fun m => ?_, fun k => hb' (Sum.inl k)⟩
  exact hb' (Sum.inr (⟨0, hd⟩, m))

/-- **Deligne's Lemme 1.5.2, for exponential sums.** Let `α` be a finite family of complex
numbers, `0 < d`, `1 ≤ q` and `w` real. Suppose that for every `i ≥ 1` there are finite families
`A i` and `B i`, every element of `A i` of absolute value at most `q ^ (1 + i w)`, such that for
all large `n` the real part of `∑ (A i) ^ (d n) - ∑ (B i) ^ (d n)` dominates
`d · ((∑ α ^ n) ^ (2 i))`. Then every `α j` has absolute value at most `q ^ (d w / 2)`. -/
public theorem norm_le_of_forall_rankin {r : Type*} [Fintype r] {α : r → ℂ} {d : ℕ}
    (hd : 0 < d) {q : ℝ} (hq : 1 ≤ q) {w : ℝ} (A B : ℕ → Multiset ℂ)
    (hA : ∀ i, ∀ a ∈ A i, ‖a‖ ≤ q ^ (1 + i * w))
    (h : ∀ i, 0 < i → ∀ᶠ n : ℕ in atTop, (d : ℝ) * ((∑ j, α j ^ n) ^ (2 * i)).re ≤
      (((A i).map (· ^ (d * n))).sum - ((B i).map (· ^ (d * n))).sum).re) (j : r) :
    ‖α j‖ ≤ q ^ (d * w / 2) := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hsum : ∀ (C : Multiset ℂ) (n : ℕ), (C.map (· ^ n)).sum = ∑ x : C, (x : ℂ) ^ n :=
    fun C n => by
      rw [Finset.sum_eq_multiset_sum]
      exact (congrArg Multiset.sum (Multiset.map_univ C (· ^ n))).symm
  have hi : ∀ i : ℕ, 0 < i → ‖α j‖ ^ (2 * i) ≤ (q ^ (1 + i * w)) ^ d := by
    intro i hi
    let g : (Fin (2 * i) → r) → ℂ := fun f => ∏ l, α (f l)
    have hg : ∀ n : ℕ, ∑ f, g f ^ n = (∑ j, α j ^ n) ^ (2 * i) := fun n => by
      simp only [g, ← Finset.prod_pow]
      rw [← Fin.prod_const, Finset.prod_univ_sum]
      rfl
    have := (norm_le_pow_of_eventually_re_sum_pow_sub_sum_pow_ge (a := fun x : A i => (x : ℂ))
      (b := fun y : B i => (y : ℂ)) (g := g) (Real.rpow_nonneg hq0.le _)
      (fun x => hA i _ Multiset.coe_mem) hd (by
        filter_upwards [h i hi] with n hn
        simpa only [hg, hsum] using hn)).1 (fun _ => j)
    simpa [g, Finset.prod_const, norm_pow] using this
  by_contra hlt
  push Not at hlt
  set c := ‖α j‖ / q ^ (d * w / 2) with hc
  have hqw : 0 < q ^ (d * w / 2) := Real.rpow_pos_of_pos hq0 _
  have hc1 : 1 < c := (one_lt_div hqw).2 hlt
  have hlim : Tendsto (fun i : ℕ => q ^ ((d : ℝ) / (2 * i))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun i : ℕ => (d : ℝ) / (2 * i)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat ((d : ℝ) / 2))
      refine this.congr fun i => ?_
      ring
    have := (Real.continuousAt_const_rpow (b := 0) hq0.ne').tendsto.comp h0
    simpa [Function.comp_def] using this
  obtain ⟨i, hilt, hi1⟩ := ((hlim.eventually (eventually_lt_nhds hc1)).and
    (eventually_gt_atTop 0)).exists
  have hbound := hi i hi1
  have hαpos : 0 < ‖α j‖ := hqw.trans hlt
  have hroot : ‖α j‖ ≤ q ^ ((d : ℝ) * (1 + i * w) / (2 * i)) := by
    have h2i : ((2 * i : ℕ) : ℝ) ≠ 0 := by positivity
    have := Real.rpow_le_rpow (by positivity) hbound (inv_nonneg.2 (Nat.cast_nonneg (2 * i)))
    rw [Real.pow_rpow_inv_natCast (norm_nonneg _) (by omega), ← Real.rpow_natCast,
      ← Real.rpow_mul hq0.le, ← Real.rpow_mul hq0.le] at this
    convert this using 2
    push_cast
    field_simp
  have hsplit : q ^ ((d : ℝ) * (1 + i * w) / (2 * i)) =
      q ^ (d * w / 2) * q ^ ((d : ℝ) / (2 * i)) := by
    rw [← Real.rpow_add hq0]
    congr 1
    have : (i : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hsplit] at hroot
  have : c ≤ q ^ ((d : ℝ) / (2 * i)) := by
    rw [hc, div_le_iff₀ hqw]
    linarith
  linarith

end Stacks.EtaleCohomology

end
