module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Sequences
import StacksCore.Tactic.StacksAttribute

/-!
# Simultaneous powers of finitely many complex numbers in a sector

Given finitely many complex numbers `α i` and a conic sector `C_ε = {z | |arg z| < ε}` about the
positive real axis, some common power `α i ^ k` with `k ≥ 1` lies in `C_ε` for every `i`, and the
exponent `k` may be taken arbitrarily large.

The argument is simultaneous Dirichlet approximation in its topological form. Rescaling each `α i`
to modulus one changes no argument of a power, and the sequence `k ↦ (α i ^ k)_i` then lives in the
compact product of unit circles, so it has a convergent, hence Cauchy, subsequence: two terms
`φ m, φ l` of it are closer than `δ`, and dividing the later by the earlier puts every coordinate
of `(α i ^ (φ l - φ m))_i` within `δ` of `1`. Continuity of `arg` at `1` turns `δ` into `ε`, and
taking `φ l` far along the subsequence makes the exponent as large as desired.

## Main results

* `Stacks.TraceFormula.exists_pow_dist_one_lt_of_norm_eq_one` — for unit-modulus `u i` and any
  `δ > 0` there are arbitrarily large `k` with every `u i ^ k` within `δ` of `1`.
* `Stacks.TraceFormula.exists_le_pow_mem_sector` — for arbitrary `α i` and any `ε > 0` there are
  arbitrarily large `k ≥ 1` with every `α i ^ k` in the sector `{z | |arg z| < ε}`.
* `Stacks.TraceFormula.exists_pow_mem_sector` — Exercise 03V9: some `k ≥ 1` has every `α i ^ k`
  in the sector.

## Implementation notes

`Complex.arg 0 = 0`, so a vanishing `α i` lies in every sector `C_ε` and needs no hypothesis; the
unit-modulus rescaling sends it to `1`.

## References

* [Stacks Project, Tag 03V9](https://stacks.math.columbia.edu/tag/03V9)
-/

@[expose] public noncomputable section

namespace Stacks.TraceFormula

open Complex Filter Metric

variable {ι : Type*} [Fintype ι]

/-- Continuity of `arg` at `1`: complex numbers near `1` have argument of small absolute value. -/
theorem exists_abs_arg_lt_of_dist_one_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℂ, dist z 1 < δ → |z.arg| < ε := by
  have h : ContinuousAt Complex.arg 1 := Complex.continuousAt_arg one_mem_slitPlane
  rw [Metric.continuousAt_iff] at h
  obtain ⟨δ, hδ, hz⟩ := h ε hε
  exact ⟨δ, hδ, fun _ h => by simpa [Real.dist_eq] using hz h⟩

/-- Every complex number has a unit-modulus companion with the same arguments of all its
positive powers, namely `z / ‖z‖` (and `1` for `z = 0`, since `arg 0 = 0`). -/
theorem exists_norm_eq_one_arg_pow_eq (z : ℂ) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ k : ℕ, k ≠ 0 → (z ^ k).arg = (u ^ k).arg := by
  rcases eq_or_ne z 0 with rfl | h
  · exact ⟨1, norm_one, fun k hk => by simp [zero_pow hk]⟩
  have hz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr h
  refine ⟨z / (‖z‖ : ℂ), ?_, fun k _ => ?_⟩
  · rw [norm_div, norm_real, Real.norm_of_nonneg hz.le, div_self hz.ne']
  · have hzc : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
    have hpow : z ^ k = ((‖z‖ ^ k : ℝ) : ℂ) * (z / (‖z‖ : ℂ)) ^ k := by
      rw [div_pow, Complex.ofReal_pow, mul_div_cancel₀ _ (pow_ne_zero k hzc)]
    rw [hpow, arg_real_mul _ (pow_pos hz k)]

omit [Fintype ι] in
/-- Simultaneous Dirichlet approximation: for finitely many complex numbers of modulus one there
are arbitrarily large exponents `k` with every `u i ^ k` within `δ` of `1`. -/
theorem exists_pow_dist_one_lt_of_norm_eq_one [Finite ι] {u : ι → ℂ} (hu : ∀ i, ‖u i‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) (N : ℕ) : ∃ k : ℕ, N + 1 ≤ k ∧ ∀ i, dist (u i ^ k) 1 < δ := by
  have := Fintype.ofFinite ι
  have hs : IsCompact (Set.univ.pi fun _ : ι => sphere (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_sphere _ _
  have hx : ∀ k : ℕ, (fun i => u i ^ k) ∈ Set.univ.pi fun _ : ι => sphere (0 : ℂ) 1 := by
    intro k i _
    simp [mem_sphere_iff_norm, norm_pow, hu i]
  obtain ⟨a, -, φ, hφ, hlim⟩ := hs.tendsto_subseq hx
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq δ hδ
  have hle : φ M + N + 1 ≤ φ (M + N + φ M + 1) := le_trans (by omega) hφ.le_apply
  refine ⟨φ (M + N + φ M + 1) - φ M, by omega, fun i => ?_⟩
  have hd : dist (u i ^ φ M) (u i ^ φ (M + N + φ M + 1)) < δ :=
    (dist_pi_lt_iff hδ).1 (hM M le_rfl (M + N + φ M + 1) (by omega)) i
  have hsplit : u i ^ φ M - u i ^ φ (M + N + φ M + 1) =
      u i ^ φ M * (1 - u i ^ (φ (M + N + φ M + 1) - φ M)) := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have hnorm : ‖u i ^ φ M‖ = 1 := by rw [norm_pow, hu i, one_pow]
  rwa [dist_eq_norm, hsplit, norm_mul, hnorm, one_mul, norm_sub_rev, ← dist_eq_norm] at hd

omit [Fintype ι] in
/-- For finitely many complex numbers `α i` and any `ε > 0` there are arbitrarily large exponents
`k ≥ 1` carrying all the `α i ^ k` simultaneously into the sector `{z | |arg z| < ε}`. -/
theorem exists_le_pow_mem_sector [Finite ι] (α : ι → ℂ) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ k : ℕ, N + 1 ≤ k ∧ ∀ i, α i ^ k ∈ {z : ℂ | |z.arg| < ε} := by
  obtain ⟨δ, hδ, hδz⟩ := exists_abs_arg_lt_of_dist_one_lt hε
  choose u hu harg using fun i => exists_norm_eq_one_arg_pow_eq (α i)
  obtain ⟨k, hk, hball⟩ := exists_pow_dist_one_lt_of_norm_eq_one hu hδ N
  refine ⟨k, hk, fun i => ?_⟩
  simp only [Set.mem_setOf_eq, harg i k (by omega)]
  exact hδz _ (hball i)

/-- **Exercise 03V9.** For complex numbers `α 1, …, α n` and a conic sector
`C_ε = {z | |arg z| < ε}` with `ε > 0` about the positive real axis, there is an integer `k ≥ 1`
with `α 1 ^ k, …, α n ^ k` all in `C_ε`. -/
@[stacks 03V9]
theorem exists_pow_mem_sector (α : ι → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ i, α i ^ k ∈ {z : ℂ | |z.arg| < ε} := by
  obtain ⟨k, hk, h⟩ := exists_le_pow_mem_sector α hε 0
  exact ⟨k, by omega, h⟩

end Stacks.TraceFormula

end
