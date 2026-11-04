module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Nonnegative solutions of `Q v = -d` for a negative definite Z-matrix

Let `Q` be a square matrix over `ℚ` with nonnegative off-diagonal entries whose quadratic form is
negative definite: `vᵀ Q v ≥ 0` only for `v = 0`. For every nonnegative vector `d` the system
`Q v = -d` has a (unique) solution, and that solution is nonnegative.

Existence: `Q v = 0` gives `vᵀ Q v = 0`, so `v = 0`; an injective endomorphism of a
finite-dimensional space is surjective. Nonnegativity: put `u = min(v, 0)`. For `i` with
`vᵢ < 0` we have `(Q u)ᵢ = (Q v)ᵢ - ∑_{j ≠ i} Q_{ij} max(vⱼ, 0) ≤ (Q v)ᵢ = -dᵢ ≤ 0`, so every
term `uᵢ (Q u)ᵢ` is nonnegative, `uᵀ Q u ≥ 0`, and `u = 0`.

Clearing denominators, an integer matrix of this kind and a nonnegative integer vector `d` admit
a positive integer `a` and a natural vector `n` with `Q n = -a d`. The last form restricts all of
this to the entries indexed by a finite subset of a larger index type, which is the shape in which
the intersection matrix of the special fibre of a model enters.

## Main results

* `Matrix.exists_nonneg_mulVec_eq_neg_of_negDef`.
* `Matrix.exists_pos_nat_sum_mul_eq_neg_of_negDef`.
* `Matrix.exists_pos_nat_finsetSum_mul_eq_neg_of_negDef`.
-/

@[expose] public noncomputable section

open Finset

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- **A negative definite matrix with nonnegative off-diagonal entries has a nonnegative solution
of `Q v = -d` for every `d ≥ 0`.** Negative definiteness is phrased as: `∑ᵢ ∑ⱼ vᵢ vⱼ Q_{ij} ≥ 0`
only for `v = 0`. -/
theorem exists_nonneg_mulVec_eq_neg_of_negDef [DecidableEq ι] (Q : Matrix ι ι ℚ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (hdef : ∀ v : ι → ℚ, 0 ≤ ∑ i, ∑ j, v i * v j * Q i j → v = 0)
    (d : ι → ℚ) (hd : ∀ i, 0 ≤ d i) :
    ∃ v : ι → ℚ, (∀ i, 0 ≤ v i) ∧ ∀ i, ∑ j, Q i j * v j = -d i := by
  have hform : ∀ v : ι → ℚ, ∑ i, ∑ j, v i * v j * Q i j = ∑ i, v i * (Q *ᵥ v) i := by
    intro v
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hinj : Function.Injective (Q *ᵥ ·) := by
    intro v w hvw
    have h0 : Q *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hvw
    have := hdef (v - w) (by rw [hform, h0]; simp)
    exact sub_eq_zero.1 this
  obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.2
    (Matrix.mulVec_injective_iff_isUnit.1 hinj)) (-d)
  have hQv : ∀ i, ∑ j, Q i j * v j = -d i := fun i => by
    simpa [Matrix.mulVec, dotProduct] using congrFun hv i
  refine ⟨v, ?_, hQv⟩
  set u : ι → ℚ := fun i => min (v i) 0 with hu
  have hterm : ∀ i, 0 ≤ u i * (Q *ᵥ u) i := by
    intro i
    by_cases hvi : 0 ≤ v i
    · simp [hu, min_eq_right hvi]
    · push Not at hvi
      have hui : u i = v i := min_eq_left hvi.le
      have hle : (Q *ᵥ u) i ≤ (Q *ᵥ v) i := by
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hji : j = i
        · subst hji; rw [show u j = v j from hui]
        · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (hoff i j (Ne.symm hji))
      have hQvi : (Q *ᵥ v) i = -d i := congrFun hv i
      have : (Q *ᵥ u) i ≤ 0 := by linarith [hd i]
      rw [hui]
      exact mul_nonneg_of_nonpos_of_nonpos hvi.le this
  have hu0 : u = 0 := hdef u (by rw [hform]; exact Finset.sum_nonneg fun i _ => hterm i)
  intro i
  have h := congrFun hu0 i
  simp only [hu, Pi.zero_apply] at h
  by_contra hneg
  push Not at hneg
  rw [min_eq_left hneg.le] at h
  exact hneg.ne h

/-- **Integer form, after clearing denominators.** For an integer matrix with nonnegative
off-diagonal entries and negative definite quadratic form, and a nonnegative integer vector `d`,
there are a positive integer `a` and a natural vector `n` with `∑ⱼ nⱼ Q_{ij} = -a dᵢ` for all
`i`. -/
theorem exists_pos_nat_sum_mul_eq_neg_of_negDef [DecidableEq ι] (Q : ι → ι → ℤ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (hdef : ∀ v : ι → ℚ, 0 ≤ ∑ i, ∑ j, v i * v j * (Q i j : ℚ) → v = 0)
    (d : ι → ℤ) (hd : ∀ i, 0 ≤ d i) :
    ∃ a : ℕ, 0 < a ∧ ∃ n : ι → ℕ, ∀ i, ∑ j, (n j : ℤ) * Q i j = -((a : ℤ) * d i) := by
  obtain ⟨v, hv0, hv⟩ := exists_nonneg_mulVec_eq_neg_of_negDef (Matrix.of fun i j => (Q i j : ℚ))
    (fun i j h => by simpa using hoff i j h) (fun v h => hdef v (by simpa using h))
    (fun i => (d i : ℚ)) (fun i => by exact_mod_cast hd i)
  set a : ℕ := ∏ i, (v i).den with ha
  have hapos : 0 < a := Finset.prod_pos fun i _ => (v i).den_pos
  have hdvd : ∀ i, (v i).den ∣ a := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set n : ι → ℕ := fun i => (v i).num.toNat * (a / (v i).den) with hn
  have hnq : ∀ i, ((n i : ℕ) : ℚ) = a * v i := by
    intro i
    have hnum : (0 : ℤ) ≤ (v i).num := Rat.num_nonneg.2 (hv0 i)
    obtain ⟨c, hc⟩ := hdvd i
    simp only [hn]
    rw [hc, Nat.mul_div_cancel_left _ (v i).den_pos]
    push_cast
    have hcast : (((v i).num.toNat : ℕ) : ℚ) = ((v i).num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum
    rw [hcast, ← Rat.mul_den_eq_num]
    ring
  refine ⟨a, hapos, n, fun i => ?_⟩
  have h := hv i
  simp only [Matrix.of_apply] at h
  exact_mod_cast
    calc ∑ j, ((n j : ℕ) : ℚ) * (Q i j : ℚ) = (a : ℚ) * ∑ j, (Q i j : ℚ) * v j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hnq j]; ring
      _ = -((a : ℚ) * d i) := by rw [h]; ring

/-- **The integer form on the entries indexed by a finite subset.** Let `Q` be an integer matrix
on `ι` with nonnegative off-diagonal entries, negative semidefinite, whose quadratic form vanishes
on a vector supported in `s` only when the vector is zero. For every `d` nonnegative on `s` there
are a positive integer `a` and a natural vector `n` vanishing off `s` with
`∑_{j ∈ s} nⱼ Q_{ij} = -a dᵢ` for every `i ∈ s`. -/
theorem exists_pos_nat_finsetSum_mul_eq_neg_of_negDef [DecidableEq ι] (Q : ι → ι → ℤ)
    (s : Finset ι) (hoff : ∀ i j, i ≠ j → 0 ≤ Q i j)
    (hnonpos : ∀ v : ι → ℚ, ∑ i, ∑ j, v i * v j * (Q i j : ℚ) ≤ 0)
    (hzero : ∀ v : ι → ℚ, (∀ i ∉ s, v i = 0) →
      ∑ i, ∑ j, v i * v j * (Q i j : ℚ) = 0 → v = 0)
    (d : ι → ℤ) (hd : ∀ i ∈ s, 0 ≤ d i) :
    ∃ a : ℕ, 0 < a ∧ ∃ n : ι → ℕ, (∀ i ∉ s, n i = 0) ∧
      ∀ i ∈ s, ∑ j ∈ s, (n j : ℤ) * Q i j = -((a : ℤ) * d i) := by
  -- extension by zero of a vector on `s`
  let ext : (s → ℚ) → ι → ℚ := fun v i => if h : i ∈ s then v ⟨i, h⟩ else 0
  have hext : ∀ v : s → ℚ, ∑ i, ∑ j, ext v i * ext v j * (Q i j : ℚ) =
      ∑ i : s, ∑ j : s, v i * v j * (Q i j : ℚ) := by
    intro v
    have hsupp : ∀ i ∉ s, ext v i = 0 := fun i hi => dif_neg hi
    rw [← Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by simp [hsupp i hi],
      ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_subset (Finset.subset_univ s) fun j _ hj => by simp [hsupp j hj],
      ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [ext]
  obtain ⟨a, hapos, n, hn⟩ := exists_pos_nat_sum_mul_eq_neg_of_negDef
    (fun i j : s => Q i j) (fun i j h => hoff i j fun e => h (Subtype.ext e))
    (fun v hv => by
      have hle := hnonpos (ext v)
      rw [hext] at hle
      have h0 := hzero (ext v) (fun i hi => dif_neg hi) (by rw [hext]; linarith)
      funext i
      have := congrFun h0 i
      simpa [ext, i.2] using this)
    (fun i : s => d i) (fun i => hd i i.2)
  refine ⟨a, hapos, fun i => if h : i ∈ s then n ⟨i, h⟩ else 0, fun i hi => dif_neg hi,
    fun i hi => ?_⟩
  have := hn ⟨i, hi⟩
  rw [← Finset.sum_coe_sort s]
  simpa using this

end Matrix

end
