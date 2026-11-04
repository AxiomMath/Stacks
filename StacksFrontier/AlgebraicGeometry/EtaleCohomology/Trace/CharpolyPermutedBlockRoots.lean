module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyBlockRoots
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Characteristic roots of an endomorphism permuting blocks

Let `V` be finite dimensional, decomposed by idempotents `inc_i ∘ pr_i` (`i` in a finite type),
and let `g` carry block `i` into block `σ i` for a permutation `σ`. If, for every `i` and every
`d > 0` with `σ^d i = i`, the characteristic roots of the diagonal block `pr_i ∘ g^d ∘ inc_i`
along `ι : K →+* ℂ` have absolute values `q ^ (d a w / 2)` with integers `w ≤ b`, then the
characteristic roots of `g` have absolute values `q ^ (a w / 2)` with `w ≤ b`.

## Main results

* `Stacks.EtaleCohomology.pow_comp_inc_comp_pr_eq`: `g ^ n` carries block `i` into `σ ^ n i`.
* `Stacks.EtaleCohomology.norm_eq_of_permutedBlocks`: the transfer of the absolute values.
* `Stacks.EtaleCohomology.trace_pow_eq_sum_of_permutedBlocks`: the trace of `g ^ m` is the sum
  of the traces of the diagonal blocks of `g ^ m` over the blocks fixed by `σ ^ m`.
-/

@[expose] public section

open Polynomial

namespace Stacks.EtaleCohomology

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {ιB : Type*} {W : ιB → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
  [∀ i, FiniteDimensional K (W i)]

omit [FiniteDimensional K V] [∀ i, FiniteDimensional K (W i)] in
/-- If `g` carries the block `i` into the block `σ i`, then `g ^ n` carries it into `σ ^ n i`. -/
public theorem pow_comp_inc_comp_pr_eq (pr : ∀ i, V →ₗ[K] W i) (inc : ∀ i, W i →ₗ[K] V)
    (σ : Equiv.Perm ιB) (g : Module.End K V)
    (hg : ∀ i, g ∘ₗ inc i ∘ₗ pr i = inc (σ i) ∘ₗ pr (σ i) ∘ₗ g) (n : ℕ) (i : ιB) :
    (g ^ n) ∘ₗ inc i ∘ₗ pr i = inc ((σ ^ n) i) ∘ₗ pr ((σ ^ n) i) ∘ₗ (g ^ n) := by
  induction n generalizing i with
  | zero => rw [pow_zero, pow_zero, Equiv.Perm.one_apply]; rfl
  | succ n ih =>
    refine LinearMap.ext fun v => ?_
    have h1 := congrArg (fun φ => φ v) (hg i)
    have h2 := congrArg (fun φ => φ (g v)) (ih (σ i))
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [pow_succ, Module.End.mul_apply, h1, h2, pow_succ, Equiv.Perm.mul_apply,
      Module.End.mul_apply]

/-- **Absolute values of the characteristic roots of an endomorphism permuting blocks.** If `g`
carries block `i` into block `σ i`, and for every `i` and `d > 0` with `σ ^ d i = i` the
characteristic roots of `pr_i ∘ g ^ d ∘ inc_i` along `ι` have absolute values
`q ^ (d a w / 2)` with `w ≤ b`, then those of `g` have absolute values `q ^ (a w / 2)` with
`w ≤ b`. -/
public theorem norm_eq_of_permutedBlocks [Fintype ιB] (ι : K →+* ℂ) (pr : ∀ i, V →ₗ[K] W i)
    (inc : ∀ i, W i →ₗ[K] V) (hsum : ∑ i, inc i ∘ₗ pr i = LinearMap.id)
    (hpi : ∀ i, pr i ∘ₗ inc i = LinearMap.id) (σ : Equiv.Perm ιB) (g : Module.End K V)
    (hg : ∀ i, g ∘ₗ inc i ∘ₗ pr i = inc (σ i) ∘ₗ pr (σ i) ∘ₗ g) {q a : ℕ} {b : ℤ}
    (h : ∀ (i : ιB) (d : ℕ), 0 < d → (σ ^ d) i = i → ∀ w : ℂ,
      ((pr i ∘ₗ (g ^ d) ∘ₗ inc i).charpoly.map ι).IsRoot w →
        ∃ w' : ℤ, w' ≤ b ∧ ‖w‖ = (q : ℝ) ^ (((d * a : ℕ) : ℝ) * w' / 2))
    {z : ℂ} (hz : (g.charpoly.map ι).IsRoot z) :
    ∃ w' : ℤ, w' ≤ b ∧ ‖z‖ = (q : ℝ) ^ ((a : ℝ) * w' / 2) := by
  classical
  set N := orderOf σ with hNdef
  have hN0 : 0 < N := orderOf_pos σ
  have hfix : ∀ i, (σ ^ N) i = i := fun i => by rw [hNdef, pow_orderOf_eq_one]; rfl
  have hcomm : ∀ i ∈ (Finset.univ : Finset ιB),
      (g ^ N) ∘ₗ inc i ∘ₗ pr i = inc i ∘ₗ pr i ∘ₗ (g ^ N) := fun i _ => by
    rw [pow_comp_inc_comp_pr_eq pr inc σ g hg, hfix]
  have hzN : (((g ^ N).charpoly).map ι).IsRoot (z ^ N) := by
    let := ι.toAlgebra
    rw [isRoot_charpoly_map_iff_hasEigenvalue_baseChange] at hz ⊢
    rw [LinearMap.baseChange_pow]
    exact hz.pow N
  obtain ⟨i, -, hzi⟩ := exists_isRoot_charpoly_map_block ι Finset.univ pr inc hsum hpi (g ^ N)
    hcomm hzN
  obtain ⟨w', hw', hnorm⟩ := h i N hN0 (hfix i) (z ^ N) hzi
  refine ⟨w', hw', ?_⟩
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [norm_pow] at hnorm
  have hrw : ((N * a : ℕ) : ℝ) * w' / 2 = ((a : ℝ) * w' / 2) * N := by push_cast; ring
  rw [hrw, Real.rpow_mul_natCast hq] at hnorm
  exact (pow_left_inj₀ (norm_nonneg z) (Real.rpow_nonneg hq _) hN0.ne').1 hnorm

/-- **The trace of a power of an endomorphism permuting blocks** is the sum of the traces of the
diagonal blocks of that power over the blocks it fixes: the blocks moved contribute nothing. -/
public theorem trace_pow_eq_sum_of_permutedBlocks [Fintype ιB] [DecidableEq ιB]
    (pr : ∀ i, V →ₗ[K] W i) (inc : ∀ i, W i →ₗ[K] V) (hsum : ∑ i, inc i ∘ₗ pr i = LinearMap.id)
    (hpi : ∀ i, pr i ∘ₗ inc i = LinearMap.id) (horth : ∀ i j, i ≠ j → pr i ∘ₗ inc j = 0)
    (σ : Equiv.Perm ιB) (g : Module.End K V)
    (hg : ∀ i, g ∘ₗ inc i ∘ₗ pr i = inc (σ i) ∘ₗ pr (σ i) ∘ₗ g) (m : ℕ) :
    LinearMap.trace K V (g ^ m) =
      ∑ i ∈ Finset.univ.filter (fun i => (σ ^ m) i = i),
        LinearMap.trace K (W i) (pr i ∘ₗ (g ^ m) ∘ₗ inc i) := by
  have h1 : LinearMap.trace K V (g ^ m) =
      ∑ i, LinearMap.trace K (W i) (pr i ∘ₗ (g ^ m) ∘ₗ inc i) := by
    conv_lhs => rw [← mul_one (g ^ m), Module.End.one_eq_id, ← hsum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  rw [h1, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rfl
  · have : pr i ∘ₗ (g ^ m) ∘ₗ inc i = 0 := by
      have h2 : (g ^ m) ∘ₗ inc i = inc ((σ ^ m) i) ∘ₗ pr ((σ ^ m) i) ∘ₗ (g ^ m) ∘ₗ inc i := by
        simpa only [LinearMap.comp_assoc, hpi, LinearMap.comp_id] using
          congrArg (· ∘ₗ inc i) (pow_comp_inc_comp_pr_eq pr inc σ g hg m i)
      rw [h2, ← LinearMap.comp_assoc, horth i _ (Ne.symm hi), LinearMap.zero_comp]
    rw [this, map_zero]

end Stacks.EtaleCohomology
