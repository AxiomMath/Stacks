module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Families with the same products `∏ (1 - x_j^m)`

Let `α_1, …, α_n` be complex numbers of absolute value `s > 1` and `b_1, …, b_n` complex numbers
with `∏_j (1 - b_j^m) = ∏_i (1 - α_i^m)` for every `m ≥ 1`. Then `{b_j} = {α_i}` as multisets
(`Stacks.PowerProduct.multiset_eq_of_prod_one_sub_pow_eq`). In the proof of Weil's theorem
through the zeta function (Tag 03U1), the `α_i` are the reciprocal roots of the zeta function of
a curve (of absolute value `√q` by the Riemann hypothesis) and the `b_j` those of the
characteristic polynomial of the Frobenius of its jacobian, `∏ (1 - b_j^m)` being the number of
rational points of the jacobian over `𝔽_{q^m}`. The condition on the absolute values cannot be
dropped: `{1/2, 1/3, √6, √6}` and `{2, 3, 1/√6, 1/√6}` have the same products.

The argument: by linear independence of the characters `m ↦ z^m`, the signed numbers of subsets
`S` with `∏_{j ∈ S} b_j = z` and `∏_{i ∈ S} α_i = z` agree for every `z ≠ 0`
(`Stacks.PowerProduct.signedCount_eq_of_prod_eq`); summing over circles gives the same
statement for the absolute values (`Stacks.PowerProduct.normCount`). For the constant family `s`
these counts are `(-1)^k C(n, k)` at `s^k`. A coordinate `|b_j| = 1` would make all counts
vanish; comparing the largest and the smallest products gives `|b_j| > 1` for all `j`, and the
second largest product, `∏ |b| / min |b|`, gives `min |b_j| = s` with multiplicity `n`
(`Stacks.PowerProduct.forall_eq_of_normCount_eq`). Then the counts at `∏ α / w`, `|w| = s`, are
`± #{j : b_j = w}` and `± #{i : α_i = w}`.

## Main results

* `Stacks.PowerProduct.forall_eq_of_normCount_eq` — the absolute values.
* `Stacks.PowerProduct.multiset_eq_of_prod_one_sub_pow_eq` — the multisets.
* `Stacks.PowerProduct.norm_eq_sqrt_of_functional_eq` — the Riemann hypothesis `|α_i| = √q` (and
  `r = 2γ`) from the Riemann inequality `|α_i| ≤ √q` and the functional equation
  `q^{m(2γ - r)} ∏ (q^m - α_i^m) = q^{mγ} ∏ (1 - α_i^m)` of the zeta function.
-/

@[expose] public noncomputable section

open Finset

namespace Stacks.PowerProduct

variable {n : ℕ}

/-- The signed number of subsets `S` with `∏_{j ∈ S} u_j = ρ`. -/
def normCount (u : Fin n → ℝ) (ρ : ℝ) : ℤ :=
  ∑ S ∈ (univ : Finset (Fin n)).powerset with ∏ j ∈ S, u j = ρ, (-1) ^ S.card

/-- If `u j₀ = 1`, toggling `j₀` in `S` preserves `∏_{j ∈ S} u_j` and flips the sign
`(-1)^{|S|}`. -/
theorem symmDiff_singleton_props (u : Fin n → ℝ) {j₀ : Fin n} (hj₀ : u j₀ = 1)
    (S : Finset (Fin n)) :
    ∏ j ∈ symmDiff S {j₀}, u j = ∏ j ∈ S, u j ∧
      ((-1 : ℤ) ^ (symmDiff S {j₀}).card = -(-1) ^ S.card) := by
  classical
  by_cases h : j₀ ∈ S
  · have e : symmDiff S {j₀} = S.erase j₀ := by
      ext x
      by_cases hx : x = j₀ <;> simp [Finset.mem_symmDiff, hx, h]
    rw [e, ← Finset.mul_prod_erase S u h, hj₀, one_mul, Finset.card_erase_of_mem h]
    refine ⟨rfl, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := ⟨S.card - 1, by
      have := Finset.card_pos.2 ⟨j₀, h⟩; omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]
    ring
  · have e : symmDiff S {j₀} = insert j₀ S := by
      ext x
      by_cases hx : x = j₀ <;> simp [Finset.mem_symmDiff, hx, h]
    rw [e, Finset.prod_insert h, hj₀, one_mul, Finset.card_insert_of_notMem h, pow_succ]
    exact ⟨rfl, by ring⟩

/-- A coordinate equal to `1` makes all signed counts vanish. -/
theorem normCount_eq_zero_of_eq_one (u : Fin n → ℝ) {j₀ : Fin n} (hj₀ : u j₀ = 1) (ρ : ℝ) :
    normCount u ρ = 0 := by
  classical
  unfold normCount
  refine Finset.sum_involution (fun S _ => symmDiff S {j₀}) (fun S _ => ?_) (fun S _ _ => ?_)
    (fun S hS => ?_) (fun S _ => symmDiff_symmDiff_cancel_right _ _)
  · rw [(symmDiff_singleton_props u hj₀ S).2]
    ring
  · intro hne
    have := congrArg (fun T => j₀ ∈ T) hne
    simp [Finset.mem_symmDiff] at this
  · simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and] at hS ⊢
    rw [(symmDiff_singleton_props u hj₀ S).1, hS]

/-- If `T` is the only subset with `∏_{j ∈ T} u_j = ρ`, then the signed count at `ρ` is
`(-1)^{|T|}`. -/
theorem normCount_eq_of_filter_eq (u : Fin n → ℝ) (ρ : ℝ) (T : Finset (Fin n))
    (hT : ∀ S : Finset (Fin n), ∏ j ∈ S, u j = ρ ↔ S = T) : normCount u ρ = (-1) ^ T.card := by
  classical
  unfold normCount
  rw [Finset.sum_eq_single_of_mem T (by simp [hT]) fun S hS hST => absurd
    ((hT S).1 (Finset.mem_filter.1 hS).2) hST]

/-- If no subset has product `ρ`, then the signed count at `ρ` vanishes. -/
theorem normCount_eq_zero_of_forall_ne (u : Fin n → ℝ) (ρ : ℝ)
    (hT : ∀ S : Finset (Fin n), ∏ j ∈ S, u j ≠ ρ) : normCount u ρ = 0 := by
  classical
  unfold normCount
  rw [Finset.filter_false_of_mem fun S _ => hT S, Finset.sum_empty]

/-- For the constant family `s > 1` on `n` coordinates, the signed count at `s^k` is
`(-1)^k C(n, k)`. -/
theorem normCount_const_pow (s : ℝ) (hs : 1 < s) (k : ℕ) :
    normCount (fun _ : Fin n => s) (s ^ k) = (-1) ^ k * (n.choose k : ℤ) := by
  classical
  unfold normCount
  have hinj : Function.Injective fun m : ℕ => s ^ m := pow_right_injective₀ (by linarith) hs.ne'
  have : ((univ : Finset (Fin n)).powerset.filter fun S => ∏ _j ∈ S, s = s ^ k) =
      (univ : Finset (Fin n)).powersetCard k := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.prod_const, Finset.mem_powersetCard]
    exact ⟨fun h => hinj h, fun h => by rw [h]⟩
  rw [this, Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_powersetCard.1 hS).2],
    Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_comm]

/-- For the constant family `s`, the signed count vanishes at every `ρ` that is not a power of
`s`. -/
theorem normCount_const_eq_zero (s : ℝ) (ρ : ℝ) (hρ : ∀ k : ℕ, s ^ k ≠ ρ) :
    normCount (fun _ : Fin n => s) ρ = 0 :=
  normCount_eq_zero_of_forall_ne _ ρ fun _ => (Finset.prod_const s).trans_ne (hρ _)

/-- If `s ⊆ t`, `∏_{j ∈ s} u_j ≥ 0` and `u_j ≥ 1` on `t \ s`, then
`∏_{j ∈ s} u_j ≤ ∏_{j ∈ t} u_j`. -/
theorem prod_le_prod_of_subset_one_le {u : Fin n → ℝ} {s t : Finset (Fin n)} (h : s ⊆ t)
    (hs : 0 ≤ ∏ j ∈ s, u j) (ht : ∀ j ∈ t \ s, 1 ≤ u j) : ∏ j ∈ s, u j ≤ ∏ j ∈ t, u j := by
  rw [← Finset.prod_sdiff h]
  exact le_mul_of_one_le_left hs (Finset.one_le_prod₀ ht)

/-- The products over admissible subsets are maximal exactly at the set of coordinates `> 1`. -/
theorem prod_le_prod_filter_one_lt (u : Fin n → ℝ) (hu : ∀ j, 0 ≤ u j) (h1 : ∀ j, u j ≠ 1)
    (S : Finset (Fin n)) (hS : ∀ j ∈ S, u j ≠ 0) :
    ∏ j ∈ S, u j ≤ ∏ j ∈ univ.filter (fun j => 1 < u j), u j ∧
      (∏ j ∈ S, u j = ∏ j ∈ univ.filter (fun j => 1 < u j), u j →
        S = univ.filter fun j => 1 < u j) := by
  classical
  set P := univ.filter fun j => 1 < u j
  have hsplit : ∏ j ∈ S, u j = (∏ j ∈ S.filter (fun j => 1 < u j), u j) *
      ∏ j ∈ S.filter (fun j => ¬ 1 < u j), u j :=
    (Finset.prod_filter_mul_prod_filter_not S _ u).symm
  have hlow : ∀ j ∈ S.filter (fun j => ¬ 1 < u j), 0 < u j ∧ u j < 1 := fun j hj => by
    obtain ⟨hjS, hj1⟩ := Finset.mem_filter.1 hj
    exact ⟨lt_of_le_of_ne (hu j) (hS j hjS).symm, lt_of_le_of_ne (not_lt.1 hj1) (h1 j)⟩
  have hA : ∏ j ∈ S.filter (fun j => ¬ 1 < u j), u j ≤ 1 :=
    Finset.prod_le_one₀ (fun j hj => (hlow j hj).1.le) fun j hj => (hlow j hj).2.le
  have hsub : S.filter (fun j => 1 < u j) ⊆ P :=
    Finset.filter_subset_filter _ (Finset.subset_univ S)
  have hBpos : 0 < ∏ j ∈ S.filter (fun j => 1 < u j), u j :=
    Finset.prod_pos fun j hj => lt_trans one_pos (Finset.mem_filter.1 hj).2
  have hB : ∏ j ∈ S.filter (fun j => 1 < u j), u j ≤ ∏ j ∈ P, u j :=
    prod_le_prod_of_subset_one_le hsub hBpos.le fun j hj =>
      (Finset.mem_filter.1 (Finset.mem_sdiff.1 hj).1).2.le
  refine ⟨?_, fun heq => ?_⟩
  · rw [hsplit]
    exact (mul_le_of_le_one_right hBpos.le hA).trans hB
  · -- equality forces `S ∩ {u ≤ 1} = ∅` and `S ∩ {u > 1} = P`
    have hA1 : ∏ j ∈ S.filter (fun j => ¬ 1 < u j), u j = 1 := by
      by_contra hne
      have : ∏ j ∈ S, u j < ∏ j ∈ P, u j := by
        rw [hsplit]
        exact (mul_lt_of_lt_one_right hBpos (lt_of_le_of_ne hA hne)).trans_le hB
      exact this.ne heq
    have hempty : S.filter (fun j => ¬ 1 < u j) = ∅ := by
      by_contra hne
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have : ∏ j ∈ S.filter (fun j => ¬ 1 < u j), u j < 1 := by
        rw [← Finset.mul_prod_erase _ _ hj]
        calc u j * ∏ x ∈ (S.filter fun j => ¬ 1 < u j).erase j, u x ≤ u j * 1 :=
              mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun x hx => (hlow x
                (Finset.mem_of_mem_erase hx)).1.le) fun x hx => (hlow x
                (Finset.mem_of_mem_erase hx)).2.le) (hlow j hj).1.le
          _ < 1 := by rw [mul_one]; exact (hlow j hj).2
      exact this.ne hA1
    have hBeq : ∏ j ∈ S.filter (fun j => 1 < u j), u j = ∏ j ∈ P, u j := by
      rwa [hsplit, hA1, mul_one] at heq
    have hSP : S.filter (fun j => 1 < u j) = P := by
      by_contra hne
      obtain ⟨j, hjP, hjS⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
      have : ∏ j ∈ S.filter (fun j => 1 < u j), u j < ∏ j ∈ P, u j := by
        calc _ ≤ ∏ x ∈ P.erase j, u x :=
              prod_le_prod_of_subset_one_le (fun x hx => Finset.mem_erase.2
                ⟨fun e => hjS (e ▸ hx), hsub hx⟩) hBpos.le fun x hx =>
                  (Finset.mem_filter.1 (Finset.mem_of_mem_erase (Finset.mem_sdiff.1 hx).1)).2.le
          _ < u j * ∏ x ∈ P.erase j, u x := lt_mul_left (Finset.prod_pos fun x hx => lt_trans
              one_pos (Finset.mem_filter.1 (Finset.mem_of_mem_erase hx)).2)
              (Finset.mem_filter.1 hjP).2
          _ = _ := Finset.mul_prod_erase _ _ hjP
      exact this.ne hBeq
    rw [← Finset.filter_union_filter_not_eq (fun j => 1 < u j) S, hSP, hempty, Finset.union_empty]

/-- A product over a subset containing a zero coordinate is zero. -/
theorem prod_eq_zero_of_not_admissible (u : Fin n → ℝ) (S : Finset (Fin n))
    (hS : ¬ ∀ j ∈ S, u j ≠ 0) : ∏ j ∈ S, u j = 0 := by
  push Not at hS
  obtain ⟨j, hj, h0⟩ := hS
  exact Finset.prod_eq_zero hj h0

/-- A value `f S` lies in the union of the image of `f` on all subsets with any finset. -/
private theorem apply_mem_image_powerset_union_left {ι : Type*} [Fintype ι] [DecidableEq ℂ]
    (f : Finset ι → ℂ) (B : Finset ℂ) (S : Finset ι) :
    f S ∈ (univ : Finset ι).powerset.image f ∪ B :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_powerset.2 (subset_univ _)))

/-- A value `f S` lies in the union of any finset with the image of `f` on all subsets. -/
private theorem apply_mem_union_image_powerset_right {ι : Type*} [Fintype ι] [DecidableEq ℂ]
    (f : Finset ι → ℂ) (A : Finset ℂ) (S : Finset ι) :
    f S ∈ A ∪ (univ : Finset ι).powerset.image f :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem f (Finset.mem_powerset.2 (subset_univ _)))

/-- If `‖x_j‖ = s` for all `j`, then `‖∏_{j ∈ S} x_j‖ = s^{|S|}`. -/
private theorem norm_prod_eq_pow_card {ι : Type*} (x : ι → ℂ) (s : ℝ) (hx : ∀ j, ‖x j‖ = s)
    (S : Finset ι) : ‖∏ j ∈ S, x j‖ = s ^ S.card := by
  rw [norm_prod, Finset.prod_congr rfl fun j _ => hx j, Finset.prod_const]

/-- Cancelling the common sign `(-1)^j`-twisted factor: natural numbers with equal signed
multiples are equal. -/
private theorem eq_of_neg_one_pow_mul_eq {j k a b : ℕ} (h : (-1 : ℤ) ^ j * a = (-1) ^ k * b) :
    a = b := by
  simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs h

/-- **Coordinates with the signed product counts of a constant family `s > 1` are all `s`.** -/
theorem forall_eq_of_normCount_eq (s : ℝ) (hs : 1 < s) (u : Fin n → ℝ) (hu : ∀ j, 0 ≤ u j)
    (h : ∀ ρ, 0 < ρ → normCount u ρ = normCount (fun _ : Fin n => s) ρ) : ∀ j, u j = s := by
  classical
  have hs0 : 0 < s := by linarith
  have hconst : ∀ k, normCount (fun _ : Fin n => s) (s ^ k) = (-1) ^ k * (n.choose k : ℤ) :=
    normCount_const_pow s hs
  -- the support of the constant counts
  have hsupp : ∀ ρ, normCount (fun _ : Fin n => s) ρ ≠ 0 → ∃ k ≤ n, s ^ k = ρ := by
    intro ρ hρ
    by_contra hno
    push Not at hno
    apply hρ
    by_cases hk : ∃ k, s ^ k = ρ
    · obtain ⟨k, rfl⟩ := hk
      have hkn : n < k := by by_contra hle; exact hno k (not_lt.1 hle) rfl
      rw [hconst, Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, mul_zero]
    · push Not at hk
      exact normCount_const_eq_zero s ρ hk
  -- no coordinate equals one
  have h1 : ∀ j, u j ≠ 1 := fun j hj => by
    have := h 1 one_pos
    rw [normCount_eq_zero_of_eq_one u hj, show (1 : ℝ) = s ^ 0 from (pow_zero s).symm, hconst]
      at this
    simp at this
  -- the top
  set P := univ.filter fun j => 1 < u j with hP
  set ρmax := ∏ j ∈ P, u j
  have hρmax : 0 < ρmax := Finset.prod_pos fun j hj => lt_trans one_pos (by simpa [P] using hj)
  have htop := prod_le_prod_filter_one_lt u hu h1
  have hcount_top : normCount u ρmax = (-1) ^ P.card :=
    normCount_eq_of_filter_eq u ρmax P fun S => ⟨fun hS => by
      by_cases hadm : ∀ j ∈ S, u j ≠ 0
      · exact (htop S hadm).2 hS
      · rw [prod_eq_zero_of_not_admissible u S hadm] at hS
        exact absurd hS hρmax.ne, fun e => e ▸ rfl⟩
  have hvanish_top : ∀ ρ, ρmax < ρ → normCount u ρ = 0 := fun ρ hρ =>
    normCount_eq_zero_of_forall_ne u ρ fun S => by
      by_cases hadm : ∀ j ∈ S, u j ≠ 0
      · exact ((htop S hadm).1.trans_lt hρ).ne
      · rw [prod_eq_zero_of_not_admissible u S hadm]; exact (hρmax.trans hρ).ne
  have hmax : ρmax = s ^ n := by
    have hn : normCount u (s ^ n) ≠ 0 := by
      rw [h _ (pow_pos hs0 n), hconst, Nat.choose_self]; simp
    have h₁ : s ^ n ≤ ρmax := not_lt.1 fun hlt => hn (hvanish_top _ hlt)
    obtain ⟨k, hk, hkρ⟩ := hsupp ρmax (by rw [← h _ hρmax, hcount_top]; simp)
    rw [← hkρ] at h₁ ⊢
    exact le_antisymm (pow_le_pow_right₀ hs.le hk) h₁
  -- the bottom, through the inverses
  set v : Fin n → ℝ := fun j => if u j = 0 then 0 else (u j)⁻¹
  have hv0 : ∀ j, 0 ≤ v j := fun j => by
    simp only [v]; split_ifs; exacts [le_rfl, inv_nonneg.2 (hu j)]
  have hv1 : ∀ j, v j ≠ 1 := fun j => by
    simp only [v]; split_ifs with h0
    · exact zero_ne_one
    · exact fun e => h1 j (inv_eq_one.1 e)
  have hvS : ∀ S : Finset (Fin n), (∀ j ∈ S, u j ≠ 0) → ∏ j ∈ S, v j = (∏ j ∈ S, u j)⁻¹ :=
    fun S hS => by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun j hj => by simp only [v, ite_eq_right (hS j hj)]
  have hvadm : ∀ S : Finset (Fin n), (∀ j ∈ S, u j ≠ 0) → ∀ j ∈ S, v j ≠ 0 := fun S hS j hj => by
    simp only [v, ite_eq_right (hS j hj)]; exact inv_ne_zero (hS j hj)
  set Q := univ.filter fun j => 1 < v j with hQ
  have hQadm : ∀ j ∈ Q, u j ≠ 0 := fun j hj h0 => by
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, v, ite_eq_left h0] at hj
    exact absurd hj (by norm_num)
  set ρmin := ∏ j ∈ Q, u j
  have hρmin : 0 < ρmin := Finset.prod_pos fun j hj => lt_of_le_of_ne (hu j) (hQadm j hj).symm
  have hbot := prod_le_prod_filter_one_lt v hv0 hv1
  have hle_bot : ∀ S : Finset (Fin n), (∀ j ∈ S, u j ≠ 0) → ρmin ≤ ∏ j ∈ S, u j ∧
      (∏ j ∈ S, u j = ρmin → S = Q) := fun S hS => by
    have hpos : 0 < ∏ j ∈ S, u j := Finset.prod_pos fun j hj => lt_of_le_of_ne (hu j) (hS j hj).symm
    obtain ⟨hle, heq⟩ := hbot S (hvadm S hS)
    rw [hvS S hS, hvS Q hQadm] at hle
    refine ⟨(inv_le_inv₀ hpos hρmin).1 hle, fun e => heq ?_⟩
    rw [hvS S hS, hvS Q hQadm, e]
  have hcount_bot : normCount u ρmin = (-1) ^ Q.card :=
    normCount_eq_of_filter_eq u ρmin Q fun S => ⟨fun hS => by
      by_cases hadm : ∀ j ∈ S, u j ≠ 0
      · exact (hle_bot S hadm).2 hS
      · rw [prod_eq_zero_of_not_admissible u S hadm] at hS; exact absurd hS.symm hρmin.ne',
        fun e => e ▸ rfl⟩
  have hvanish_bot : ∀ ρ, 0 < ρ → ρ < ρmin → normCount u ρ = 0 := fun ρ hρ0 hρ =>
    normCount_eq_zero_of_forall_ne u ρ fun S => by
      by_cases hadm : ∀ j ∈ S, u j ≠ 0
      · exact (hρ.trans_le (hle_bot S hadm).1).ne'
      · rw [prod_eq_zero_of_not_admissible u S hadm]; exact hρ0.ne
  have hmin : ρmin = 1 := by
    have hn : normCount u 1 ≠ 0 := by
      rw [h _ one_pos, show (1 : ℝ) = s ^ 0 from (pow_zero s).symm, hconst]; simp
    have h₁ : ρmin ≤ 1 := not_lt.1 fun hlt => hn (hvanish_bot _ one_pos hlt)
    obtain ⟨k, -, hkρ⟩ := hsupp ρmin (by rw [← h _ hρmin, hcount_bot]; simp)
    rw [← hkρ] at h₁ ⊢
    exact le_antisymm h₁ (one_le_pow₀ hs.le)
  have hQe : Q = ∅ := by
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hne
    have hj' : 1 < v j := by simpa [Q] using hj
    have hujlt : u j < 1 := by
      simp only [v, ite_eq_right (hQadm j hj)] at hj'
      exact (one_lt_inv₀ (lt_of_le_of_ne (hu j) (hQadm j hj).symm)).1 hj'
    have : ρmin < 1 := by
      show ∏ x ∈ Q, u x < 1
      rw [← Finset.mul_prod_erase Q u hj]
      have hle : ∏ x ∈ Q.erase j, u x ≤ 1 := Finset.prod_le_one₀ (fun x _ => hu x) fun x hx => by
        have hx' := Finset.mem_of_mem_erase hx
        have : 1 < v x := by simpa [Q] using hx'
        simp only [v, ite_eq_right (hQadm x hx')] at this
        exact ((one_lt_inv₀ (lt_of_le_of_ne (hu x) (hQadm x hx').symm)).1 this).le
      calc u j * ∏ x ∈ Q.erase j, u x ≤ u j * 1 := mul_le_mul_of_nonneg_left hle (hu j)
        _ < 1 := by rw [mul_one]; exact hujlt
    exact this.ne hmin
  -- every admissible coordinate is `> 1`
  have hbig : ∀ j, u j ≠ 0 → 1 < u j := fun j h0 => by
    rcases lt_or_gt_of_ne (h1 j) with hlt | hgt
    · exfalso
      have : j ∈ Q := by
        simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, v, ite_eq_right h0]
        exact (one_lt_inv₀ (lt_of_le_of_ne (hu j) (Ne.symm h0))).2 hlt
      rw [hQe] at this; exact Finset.notMem_empty j this
    · exact hgt
  -- the second level from the top
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact fun j => j.elim0
  have hPne : P.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : ρmax = 1 := by simp only [ρmax, hne, Finset.prod_empty]
    rw [this] at hmax
    have := (pow_lt_pow_iff_right₀ hs).2 hn
    rw [pow_zero, ← hmax] at this
    exact this.false
  have hadmP : ∀ S : Finset (Fin n), (∀ j ∈ S, u j ≠ 0) → S ⊆ P := fun S hS j hj => by
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]; exact hbig j (hS j hj)
  set μ := P.inf' hPne u
  have hμle : ∀ j ∈ P, μ ≤ u j := fun j hj => Finset.inf'_le u hj
  have hμ1 : 1 < μ := (Finset.lt_inf'_iff hPne).2 fun j hj => by simpa [P] using hj
  have hP1 : ∀ j ∈ P, 1 < u j := fun j hj => by simpa [P] using hj
  -- products over nonempty `T ⊆ P` are `≥ μ`, with equality only for a singleton of value `μ`
  have hT : ∀ T ⊆ P, T.Nonempty → μ ≤ ∏ j ∈ T, u j ∧
      (∏ j ∈ T, u j = μ → ∃ j ∈ P, u j = μ ∧ T = {j}) := by
    intro T hTP ⟨j, hj⟩
    have hrest : 1 ≤ ∏ x ∈ T.erase j, u x :=
      Finset.one_le_prod₀ fun x hx => (hP1 x (hTP (Finset.mem_of_mem_erase hx))).le
    rw [← Finset.mul_prod_erase T u hj]
    have hujpos : 0 < u j := lt_trans one_pos (hP1 j (hTP hj))
    refine ⟨(hμle j (hTP hj)).trans (le_mul_of_one_le_right hujpos.le hrest), fun e => ?_⟩
    have huj : u j = μ := le_antisymm (by
      calc u j ≤ u j * ∏ x ∈ T.erase j, u x := le_mul_of_one_le_right hujpos.le hrest
        _ = μ := e) (hμle j (hTP hj))
    refine ⟨j, hTP hj, huj, ?_⟩
    have hrest1 : ∏ x ∈ T.erase j, u x = 1 := by
      rw [huj] at e
      have := mul_left_cancel₀ (lt_trans one_pos hμ1).ne' (e.trans (mul_one μ).symm)
      exact this
    have herase : T.erase j = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have : 1 < ∏ y ∈ T.erase j, u y := by
        rw [← Finset.mul_prod_erase _ u hx]
        exact one_lt_mul_of_lt_of_le (hP1 x (hTP (Finset.mem_of_mem_erase hx)))
          (Finset.one_le_prod₀ fun y hy => (hP1 y (hTP (Finset.mem_of_mem_erase
            (Finset.mem_of_mem_erase hy)))).le)
      exact this.ne' hrest1
    ext x
    by_cases hx : x = j
    · simp [hx, hj]
    · have : x ∉ T.erase j := by rw [herase]; exact Finset.notMem_empty x
      simp only [Finset.mem_erase, not_and] at this
      simp [hx, fun h => this hx h]
  set ρ2 := ρmax / μ
  have hμpos : 0 < μ := lt_trans one_pos hμ1
  have hsplitP : ∀ S ⊆ P, ∏ j ∈ P, u j = (∏ j ∈ P \ S, u j) * ∏ j ∈ S, u j := fun S hS =>
    (Finset.prod_sdiff hS).symm
  have hρ2lt : ρ2 < ρmax := div_lt_self hρmax hμ1
  have hρ2pos : 0 < ρ2 := div_pos hρmax hμpos
  -- admissible proper subsets of `P` have products `≤ ρ2`
  have hprop : ∀ S ⊆ P, S ≠ P → ∏ j ∈ S, u j ≤ ρ2 ∧
      (∏ j ∈ S, u j = ρ2 → ∃ j ∈ P, u j = μ ∧ S = P.erase j) := by
    intro S hSP hne
    have hTne : (P \ S).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
      exact fun h => hne (le_antisymm hSP h)
    obtain ⟨hle, heq⟩ := hT (P \ S) Finset.sdiff_subset hTne
    have hTpos : 0 < ∏ j ∈ P \ S, u j := hμpos.trans_le hle
    have hS' : ∏ j ∈ S, u j = ρmax / ∏ j ∈ P \ S, u j := by
      rw [eq_div_iff hTpos.ne', mul_comm]; exact (hsplitP S hSP).symm
    refine ⟨?_, fun e => ?_⟩
    · rw [hS']; exact div_le_div_of_nonneg_left hρmax.le hμpos hle
    · rw [hS', div_eq_div_iff hTpos.ne' hμpos.ne'] at e
      obtain ⟨j, hjP, hj, hTj⟩ := heq (mul_left_cancel₀ hρmax.ne' e).symm
      refine ⟨j, hjP, hj, ?_⟩
      ext x
      by_cases hx : x = j
      · subst hx
        have : x ∈ P \ S := by rw [hTj]; exact Finset.mem_singleton_self x
        simp [(Finset.mem_sdiff.1 this).2]
      · have hxT : x ∉ P \ S := by rw [hTj]; simpa using hx
        simp only [Finset.mem_sdiff, not_and, not_not] at hxT
        simp only [Finset.mem_erase, hx, ne_eq, not_false_eq_true, true_and]
        exact ⟨fun h => hSP h, hxT⟩
  have hvan2 : ∀ ρ, ρ2 < ρ → ρ < ρmax → normCount u ρ = 0 := fun ρ hρ hρ' =>
    normCount_eq_zero_of_forall_ne u ρ fun S => by
      by_cases hadm : ∀ j ∈ S, u j ≠ 0
      · by_cases hSP : S = P
        · rw [hSP]; exact hρ'.ne'
        · exact ((hprop S (hadmP S hadm) hSP).1.trans_lt hρ).ne
      · rw [prod_eq_zero_of_not_admissible u S hadm]
        exact (hρ2pos.trans hρ).ne
  set c := (P.filter fun j => u j = μ).card
  have hcount2 : normCount u ρ2 = (-1) ^ (P.card - 1) * c := by
    unfold normCount
    have hF : ((univ : Finset (Fin n)).powerset.filter fun S => ∏ j ∈ S, u j = ρ2) =
        (P.filter fun j => u j = μ).image P.erase := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
        Finset.mem_image]
      constructor
      · intro hS
        have hadm : ∀ j ∈ S, u j ≠ 0 := by
          by_contra hna
          rw [prod_eq_zero_of_not_admissible u S hna] at hS
          exact hρ2pos.ne hS
        have hSP : S ≠ P := fun e => by rw [e] at hS; exact hρ2lt.ne' hS
        obtain ⟨j, hjP, hj, rfl⟩ := (hprop S (hadmP S hadm) hSP).2 hS
        exact ⟨j, ⟨hjP, hj⟩, rfl⟩
      · rintro ⟨j, ⟨hjP, hjμ⟩, rfl⟩
        have := Finset.mul_prod_erase P u hjP
        rw [hjμ] at this
        show ∏ x ∈ P.erase j, u x = ρmax / μ
        rw [eq_div_iff hμpos.ne', mul_comm, this]
    rw [hF, Finset.sum_image fun j hj _ _ e => (Finset.erase_inj P (Finset.mem_filter.1 hj).1).1 e]
    rw [Finset.sum_congr rfl fun j hj => by
      rw [Finset.card_erase_of_mem (Finset.mem_filter.1 hj).1], Finset.sum_const, nsmul_eq_mul,
      mul_comm]
  have hc : 0 < c := by
    obtain ⟨j, hjP, hj⟩ := Finset.exists_mem_eq_inf' hPne u
    exact Finset.card_pos.2 ⟨j, Finset.mem_filter.2 ⟨hjP, hj.symm⟩⟩
  -- the comparison
  have hρ2 : ρ2 = s ^ (n - 1) := by
    obtain ⟨k, hk, hkρ⟩ := hsupp ρ2 (by
      rw [← h _ hρ2pos, hcount2]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hc.ne'))
    have hkn : k < n := by
      by_contra hkn
      have : k = n := le_antisymm hk (not_lt.1 hkn)
      rw [this, ← hmax] at hkρ
      exact hρ2lt.ne' hkρ
    have h₁ : ρ2 ≤ s ^ (n - 1) := by
      rw [← hkρ]; exact pow_le_pow_right₀ hs.le (by omega)
    have hn1 : normCount u (s ^ (n - 1)) ≠ 0 := by
      rw [h _ (pow_pos hs0 _), hconst, Nat.choose_symm_of_eq_add (show n = n - 1 + 1 by omega),
        Nat.choose_one_right]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hn.ne')
    have h₂ : s ^ (n - 1) ≤ ρ2 := by
      by_contra hlt
      refine hn1 (hvan2 _ (not_le.1 hlt) ?_)
      rw [hmax]; exact pow_lt_pow_right₀ hs (by omega)
    exact le_antisymm h₁ h₂
  have hμs : μ = s := by
    have h' : ρmax / μ = s ^ (n - 1) := hρ2
    rw [hmax, div_eq_iff hμpos.ne', show n = n - 1 + 1 by omega, pow_succ,
      Nat.add_sub_cancel] at h'
    exact (mul_left_cancel₀ (pow_ne_zero _ hs0.ne') h').symm
  have hcn : c = n := by
    have := h ρ2 hρ2pos
    rw [hcount2, hρ2, hconst, Nat.choose_symm_of_eq_add (show n = n - 1 + 1 by omega),
      Nat.choose_one_right] at this
    exact eq_of_neg_one_pow_mul_eq this
  have hall : (P.filter fun j => u j = μ) = univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Fintype.card_fin]; exact hcn
  intro j
  have : j ∈ P.filter fun j => u j = μ := by rw [hall]; exact Finset.mem_univ j
  rw [(Finset.mem_filter.1 this).2, hμs]

/-- The signed number of subsets `S` with `∏_{j ∈ S} x_j = z`. -/
def signedCount (x : Fin n → ℂ) (z : ℂ) : ℤ :=
  ∑ S ∈ (univ : Finset (Fin n)).powerset with ∏ j ∈ S, x j = z, (-1) ^ S.card

/-- The expansion `∏_j (1 - x_j^m) = ∑_S (-1)^{|S|} (∏_{j ∈ S} x_j)^m`. -/
theorem prod_one_sub_pow_eq_sum (x : Fin n → ℂ) (m : ℕ) :
    ∏ j, (1 - x j ^ m) = ∑ S ∈ (univ : Finset (Fin n)).powerset,
      ((-1) ^ S.card : ℂ) * (∏ j ∈ S, x j) ^ m := by
  classical
  have := Finset.prod_add (fun j => -x j ^ m) (fun _ => (1 : ℂ)) (univ : Finset (Fin n))
  simp only [Finset.prod_const_one, mul_one] at this
  rw [show (fun j => 1 - x j ^ m) = fun j => -x j ^ m + 1 by funext; ring, this]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_neg, Finset.prod_pow]

/-- Grouping the signed sum `∑_S (-1)^{|S|} f(V S)` over the fibres of `V` in a finset `Z`. -/
private theorem sum_powerset_eq_sum_fiber {ι : Type*} [Fintype ι] (V : Finset ι → ℂ)
    (Z : Finset ℂ) (hV : ∀ S, V S ∈ Z) (f : ℂ → ℂ) :
    ∑ S ∈ (univ : Finset ι).powerset, ((-1) ^ S.card : ℂ) * f (V S) =
      ∑ z ∈ Z, ((∑ S ∈ (univ : Finset ι).powerset with V S = z, (-1) ^ S.card : ℤ) : ℂ) * f z := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := V) (t := Z) fun S _ => hV S]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [(Finset.mem_filter.1 hS).2]
  push_cast
  rfl

/-- If `Z` contains every product `∏_{j ∈ S} x_j`, then
`∑_S (-1)^{|S|} f(∏_{j ∈ S} x_j) = ∑_{z ∈ Z} signedCount x z · f(z)`. -/
theorem sum_eq_sum_signedCount (x : Fin n → ℂ) (Z : Finset ℂ)
    (hZ : ∀ S : Finset (Fin n), ∏ j ∈ S, x j ∈ Z) (f : ℂ → ℂ) :
    ∑ S ∈ (univ : Finset (Fin n)).powerset, ((-1) ^ S.card : ℂ) * f (∏ j ∈ S, x j) =
      ∑ z ∈ Z, (signedCount x z : ℂ) * f z :=
  sum_powerset_eq_sum_fiber (fun S => ∏ j ∈ S, x j) Z hZ f

/-- **Linear independence of the characters `m ↦ z^m`, `m ≥ 1`.** If two exponential sums over a
finite set `Z ⊆ ℂ` agree for all `m ≥ 1`, their coefficients agree at every `z ≠ 0` of `Z`. -/
theorem coeff_eq_of_sum_pow_eq (Z : Finset ℂ) (c d : ℂ → ℂ)
    (h : ∀ m : ℕ, 0 < m → ∑ z ∈ Z, c z * z ^ m = ∑ z ∈ Z, d z * z ^ m) (z : ℂ) (hzZ : z ∈ Z)
    (hz : z ≠ 0) : c z = d z := by
  classical
  set Z' := Z.filter (· ≠ 0)
  have hsum : ∀ m : ℕ, ∑ w ∈ Z', (c w - d w) * w * w ^ m = 0 := fun m => by
    have hm := h (m + 1) (Nat.succ_pos m)
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
      ← Finset.sum_filter_add_sum_filter_not Z (· ≠ 0)] at hm
    rw [Finset.sum_eq_zero (s := Z.filter fun w => ¬ w ≠ 0) fun w hw => by
      rw [not_not.1 (Finset.mem_filter.1 hw).2]; simp, add_zero] at hm
    rw [← hm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [pow_succ]
    ring
  let χ : Z' → (Multiplicative ℕ →* ℂ) := fun w => powersHom ℂ w
  have hχinj : Function.Injective χ := fun w w' e => by
    have := congrArg (fun f : Multiplicative ℕ →* ℂ => f (Multiplicative.ofAdd 1)) e
    simp only [χ, powersHom_apply, toAdd_ofAdd, pow_one] at this
    exact Subtype.ext this
  have hli : LinearIndependent ℂ fun w : Z' => (χ w : Multiplicative ℕ → ℂ) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp χ hχinj
  have hcoef := Fintype.linearIndependent_iff.1 hli (fun w => (c w - d w) * w) (funext fun m => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, χ, powersHom_apply]
    rw [← hsum (Multiplicative.toAdd m)]
    exact (Finset.sum_coe_sort Z' fun w => (c w - d w) * w * w ^ (Multiplicative.toAdd m)))
  exact sub_eq_zero.1 ((mul_eq_zero.1 (hcoef ⟨z, Finset.mem_filter.2 ⟨hzZ, hz⟩⟩)).resolve_right hz)

/-- **Equal products `∏ (1 - x_j^m)` for all `m ≥ 1` give equal signed counts at every `z ≠ 0`**
(linear independence of the characters `m ↦ z^m`). -/
theorem signedCount_eq_of_prod_eq {n' : ℕ} (x : Fin n → ℂ) (y : Fin n' → ℂ)
    (h : ∀ m : ℕ, 0 < m → ∏ j, (1 - x j ^ m) = ∏ i, (1 - y i ^ m)) (z : ℂ) (hz : z ≠ 0) :
    signedCount x z = signedCount y z := by
  classical
  set Z := ((univ : Finset (Fin n)).powerset.image fun S => ∏ j ∈ S, x j) ∪
    ((univ : Finset (Fin n')).powerset.image fun S => ∏ j ∈ S, y j)
  have hxZ : ∀ S : Finset (Fin n), ∏ j ∈ S, x j ∈ Z :=
    apply_mem_image_powerset_union_left (fun S => ∏ j ∈ S, x j) _
  have hyZ : ∀ S : Finset (Fin n'), ∏ j ∈ S, y j ∈ Z :=
    apply_mem_union_image_powerset_right (fun S => ∏ j ∈ S, y j) _
  have hZsum : ∀ m : ℕ, 0 < m → ∑ w ∈ Z, (signedCount x w : ℂ) * w ^ m =
      ∑ w ∈ Z, (signedCount y w : ℂ) * w ^ m := fun m hm => by
    rw [← sum_eq_sum_signedCount x Z hxZ (· ^ m), ← sum_eq_sum_signedCount y Z hyZ (· ^ m),
      ← prod_one_sub_pow_eq_sum, ← prod_one_sub_pow_eq_sum, h m hm]
  by_cases hzZ : z ∈ Z
  · exact_mod_cast coeff_eq_of_sum_pow_eq Z _ _ hZsum z hzZ hz
  · have h0 : ∀ {k : ℕ} (w : Fin k → ℂ), (∀ S : Finset (Fin k), ∏ j ∈ S, w j ≠ z) →
        signedCount w z = 0 := fun w hw => by
      unfold signedCount
      rw [Finset.filter_false_of_mem fun S _ => hw S, Finset.sum_empty]
    rw [h0 x fun S e => hzZ (e ▸ hxZ S), h0 y fun S e => hzZ (e ▸ hyZ S)]

/-- If `Z` contains every product `∏_{j ∈ S} x_j`, the signed count of the absolute values at `ρ`
is the sum of the signed counts `signedCount x z` over `z ∈ Z` with `‖z‖ = ρ`. -/
theorem normCount_norm_eq_sum (x : Fin n → ℂ) (Z : Finset ℂ)
    (hZ : ∀ S : Finset (Fin n), ∏ j ∈ S, x j ∈ Z) (ρ : ℝ) :
    normCount (fun j => ‖x j‖) ρ = ∑ z ∈ Z with ‖z‖ = ρ, signedCount x z := by
  classical
  unfold normCount signedCount
  simp only [← norm_prod]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun S => ∏ j ∈ S, x j)
    (t := Z.filter fun z => ‖z‖ = ρ) fun S hS => Finset.mem_filter.2 ⟨hZ S,
      (Finset.mem_filter.1 hS).2⟩]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.filter_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ (Finset.mem_filter.1 hz).2, h⟩⟩

/-- If `‖x_j‖ = s > 1` for all `j` and `‖z‖ = s^k`, then `signedCount x z` is `(-1)^k` times
the number of `k`-element subsets `S` with `∏_{j ∈ S} x_j = z`. -/
theorem signedCount_of_norm_eq (x : Fin n → ℂ) (s : ℝ) (hs : 1 < s) (hx : ∀ j, ‖x j‖ = s)
    (k : ℕ) (z : ℂ) (hz : ‖z‖ = s ^ k) :
    signedCount x z = (-1) ^ k * (((univ : Finset (Fin n)).powersetCard k).filter
      fun S => ∏ j ∈ S, x j = z).card := by
  classical
  unfold signedCount
  have hinj : Function.Injective fun m : ℕ => s ^ m := pow_right_injective₀ (by linarith) hs.ne'
  have : ((univ : Finset (Fin n)).powerset.filter fun S => ∏ j ∈ S, x j = z) =
      ((univ : Finset (Fin n)).powersetCard k).filter fun S => ∏ j ∈ S, x j = z := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_powersetCard]
    exact ⟨fun h => ⟨hinj ((norm_prod_eq_pow_card x s hx S).symm.trans (h ▸ hz)), h⟩, fun h => h.2⟩
  rw [this, Finset.sum_congr rfl fun S hS => by
    rw [(Finset.mem_powersetCard.1 (Finset.mem_filter.1 hS).1).2], Finset.sum_const,
    nsmul_eq_mul, mul_comm]

/-- The only `n`-element subset of `Fin n` is `univ`. -/
theorem powersetCard_univ_self : (univ : Finset (Fin n)).powersetCard n = {univ} := by
  simpa using Finset.powersetCard_self (univ : Finset (Fin n))

/-- For `n > 0`, the `(n - 1)`-element subsets of `Fin n` are the sets `univ.erase j`. -/
theorem mem_powersetCard_pred_iff {S : Finset (Fin n)} (hn : 0 < n) :
    S ∈ (univ : Finset (Fin n)).powersetCard (n - 1) ↔ ∃ j, S = univ.erase j := by
  classical
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · intro hS
    have hc : (univ \ S).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin,
        hS]
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hc
    refine ⟨j, ?_⟩
    rw [← Finset.sdiff_singleton_eq_erase, ← hj, Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)]
  · rintro ⟨j, rfl⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-- **A family of complex numbers with the products `∏ (1 - b_j^m)` of a family of numbers of
absolute value `s > 1` is that family, up to order.** If `‖α_i‖ = s > 1` for all `i` and
`∏_j (1 - b_j^m) = ∏_i (1 - α_i^m)` for all `m ≥ 1`, then the multisets `{b_j}` and `{α_i}`
agree. (Without the condition on `‖α_i‖` this fails: `{1/2, 1/3, √6, √6}` and
`{2, 3, 1/√6, 1/√6}` have the same products.) -/
theorem multiset_eq_of_prod_one_sub_pow_eq (s : ℝ) (hs : 1 < s) (α b : Fin n → ℂ)
    (hα : ∀ i, ‖α i‖ = s) (h : ∀ m : ℕ, 0 < m → ∏ j, (1 - b j ^ m) = ∏ i, (1 - α i ^ m)) :
    Multiset.map b univ.val = Multiset.map α univ.val := by
  classical
  have hs0 : 0 < s := by linarith
  have hc := signedCount_eq_of_prod_eq b α h
  set Z := ((univ : Finset (Fin n)).powerset.image fun S => ∏ j ∈ S, b j) ∪
    ((univ : Finset (Fin n)).powerset.image fun S => ∏ j ∈ S, α j)
  have hbZ : ∀ S : Finset (Fin n), ∏ j ∈ S, b j ∈ Z :=
    apply_mem_image_powerset_union_left (fun S => ∏ j ∈ S, b j) _
  have hαZ : ∀ S : Finset (Fin n), ∏ j ∈ S, α j ∈ Z :=
    apply_mem_union_image_powerset_right (fun S => ∏ j ∈ S, α j) _
  -- the absolute values
  have hb : ∀ j, ‖b j‖ = s := by
    refine forall_eq_of_normCount_eq s hs (fun j => ‖b j‖) (fun j => norm_nonneg _)
      fun ρ hρ => ?_
    rw [show (fun _ : Fin n => s) = fun j => ‖α j‖ from funext fun j => (hα j).symm,
      normCount_norm_eq_sum b Z hbZ, normCount_norm_eq_sum α Z hαZ]
    refine Finset.sum_congr rfl fun z hz => hc z fun h0 => ?_
    rw [(Finset.mem_filter.1 hz).2.symm, h0, norm_zero] at hρ
    exact lt_irrefl _ hρ
  -- the products of all coordinates agree
  have hnormall : ∀ x : Fin n → ℂ, (∀ j, ‖x j‖ = s) → ‖∏ j, x j‖ = s ^ n := fun x hx => by
    rw [norm_prod_eq_pow_card x s hx, Finset.card_univ, Fintype.card_fin]
  have htop : ∀ (x : Fin n → ℂ), (∀ j, ‖x j‖ = s) →
      signedCount x (∏ j, x j) = (-1) ^ n := fun x hx => by
    rw [signedCount_of_norm_eq x s hs hx n _ (hnormall x hx), powersetCard_univ_self,
      Finset.filter_singleton, ite_eq_left rfl, Finset.card_singleton]
    simp
  have hαne : ∏ j, α j ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => norm_ne_zero_iff.1 ((hα i).trans_ne hs0.ne')
  have hall : ∏ j, b j = ∏ j, α j := by
    have h1 := hc _ hαne
    rw [htop α hα, signedCount_of_norm_eq b s hs hb n _ (hnormall α hα),
      powersetCard_univ_self] at h1
    by_contra hne
    rw [Finset.filter_singleton, ite_eq_right hne, Finset.card_empty] at h1
    simp only [Nat.cast_zero, mul_zero] at h1
    exact (pow_ne_zero n (by norm_num : (-1 : ℤ) ≠ 0)) h1.symm
  -- the multiplicities agree
  ext w
  rw [Multiset.count_map, Multiset.count_map]
  show (univ.filter fun j => w = b j).card = (univ.filter fun j => w = α j).card
  by_cases hw : ‖w‖ = s
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    have hw0 : w ≠ 0 := fun h0 => by rw [h0, norm_zero] at hw; exact hs0.ne hw
    have hcount : ∀ (x : Fin n → ℂ), (∀ j, ‖x j‖ = s) → ∏ j, x j = ∏ j, α j →
        signedCount x ((∏ j, α j) / w) =
          (-1) ^ (n - 1) * (univ.filter fun j => w = x j).card := fun x hx hxall => by
      have hxj : ∀ j, x j ≠ 0 := fun j h0 => by
        have := hx j; rw [h0, norm_zero] at this; exact hs0.ne this
      rw [signedCount_of_norm_eq x s hs hx (n - 1) _ (by
        rw [norm_div, ← hxall, norm_prod_eq_pow_card x s hx, hw, Finset.card_univ,
          Fintype.card_fin,
          show n = n - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel, mul_div_cancel_right₀ _
            hs0.ne'])]
      congr 2
      have hset : ((univ : Finset (Fin n)).powersetCard (n - 1)).filter
          (fun S => ∏ j ∈ S, x j = (∏ j, α j) / w) =
          (univ.filter fun j => w = x j).image fun j => univ.erase j := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        rw [mem_powersetCard_pred_iff hn]
        constructor
        · rintro ⟨⟨j, rfl⟩, hj⟩
          refine ⟨j, ?_, rfl⟩
          rw [← hxall, ← Finset.mul_prod_erase univ x (Finset.mem_univ j), eq_div_iff hw0,
            mul_comm, mul_left_inj' (Finset.prod_ne_zero_iff.2 fun i _ => hxj i)] at hj
          exact hj
        · rintro ⟨j, hj, rfl⟩
          refine ⟨⟨j, rfl⟩, ?_⟩
          rw [← hxall, ← Finset.mul_prod_erase univ x (Finset.mem_univ j), eq_div_iff hw0,
            mul_comm, hj]
      rw [hset, Finset.card_image_of_injective _ fun j j' e =>
        (Finset.erase_inj univ (Finset.mem_univ j)).1 e]
    have := hc _ (div_ne_zero hαne hw0)
    rw [hcount b hb hall, hcount α hα rfl] at this
    exact eq_of_neg_one_pow_mul_eq this
  · have hb' : (univ.filter fun j => w = b j) = ∅ := Finset.filter_false_of_mem fun j _ e =>
      hw (e ▸ hb j)
    have hα' : (univ.filter fun j => w = α j) = ∅ := Finset.filter_false_of_mem fun j _ e =>
      hw (e ▸ hα j)
    rw [hb', hα']

/-- **The Riemann hypothesis from the Riemann inequality and the functional equation.** Let
`q ≥ 2`, `r ≤ 2γ` and `α_1, …, α_r` with `|α_i| ≤ √q` such that
`q^{m(2γ - r)} ∏ (q^m - α_i^m) = q^{mγ} ∏ (1 - α_i^m)` for all `m ≥ 1` (the identity
`P_m(q^{-m}) = q^{-mγ} P_m(1)` of the zeta function). Then `r = 2γ` and `|α_i| = √q` for all `i`:
the character `q^{2γ}` occurs on the left (from `S = ∅`) with coefficient `1`, so on the right
some `q^γ ∏_{i ∈ S} α_i = q^{2γ}`, which forces `|S| ≥ 2γ`. -/
theorem norm_eq_sqrt_of_functional_eq (q : ℕ) (hq : 2 ≤ q) (γ : ℕ) {r : ℕ} (hr : r ≤ 2 * γ)
    (α : Fin r → ℂ) (hle : ∀ i, ‖α i‖ ≤ Real.sqrt q)
    (h : ∀ m : ℕ, 0 < m → (q : ℂ) ^ (m * (2 * γ - r)) * ∏ i, ((q : ℂ) ^ m - α i ^ m) =
      (q : ℂ) ^ (m * γ) * ∏ i, (1 - α i ^ m)) :
    r = 2 * γ ∧ ∀ i, ‖α i‖ = Real.sqrt q := by
  classical
  set sq := Real.sqrt q
  have hsq : 1 < sq := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast (by omega : 1 < q))
  have hsq2 : sq ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  have hqC : ‖(q : ℂ)‖ = q := by rw [Complex.norm_natCast]
  set L : Finset (Fin r) → ℂ := fun S => (q : ℂ) ^ (2 * γ - S.card) * ∏ i ∈ S, α i
  set R : Finset (Fin r) → ℂ := fun S => (q : ℂ) ^ γ * ∏ i ∈ S, α i
  have hexpL : ∀ m, (q : ℂ) ^ (m * (2 * γ - r)) * ∏ i, ((q : ℂ) ^ m - α i ^ m) =
      ∑ S ∈ (univ : Finset (Fin r)).powerset, ((-1) ^ S.card : ℂ) * (L S) ^ m := fun m => by
    have := Finset.prod_add (fun i => -α i ^ m) (fun _ => (q : ℂ) ^ m) (univ : Finset (Fin r))
    rw [show (fun i => (q : ℂ) ^ m - α i ^ m) = fun i => -α i ^ m + (q : ℂ) ^ m by
      funext; ring, this, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hSc : S.card ≤ r := by
      simpa using Finset.card_le_card (Finset.mem_powerset.1 hS)
    rw [Finset.prod_neg, Finset.prod_pow, Finset.prod_const, Finset.card_sdiff_of_subset
      (Finset.mem_powerset.1 hS), Finset.card_univ, Fintype.card_fin]
    simp only [L, mul_pow, ← pow_mul]
    rw [show (2 * γ - S.card) * m = m * (2 * γ - r) + m * (r - S.card) by
      rw [show 2 * γ - S.card = (2 * γ - r) + (r - S.card) by omega]; ring, pow_add]
    ring
  have hexpR : ∀ m, (q : ℂ) ^ (m * γ) * ∏ i, (1 - α i ^ m) =
      ∑ S ∈ (univ : Finset (Fin r)).powerset, ((-1) ^ S.card : ℂ) * (R S) ^ m := fun m => by
    rw [prod_one_sub_pow_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp only [R, mul_pow, ← pow_mul]
    ring
  set Z := ((univ : Finset (Fin r)).powerset.image L) ∪ ((univ : Finset (Fin r)).powerset.image R)
  have hLZ : ∀ S, L S ∈ Z := apply_mem_image_powerset_union_left L _
  have hRZ : ∀ S, R S ∈ Z := apply_mem_union_image_powerset_right R _
  set z₀ : ℂ := (q : ℂ) ^ (2 * γ)
  have hz₀ : z₀ ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
  have hz₀Z : z₀ ∈ Z := by simpa [L, z₀] using hLZ ∅
  have hc := coeff_eq_of_sum_pow_eq Z
    (fun z => ((∑ S ∈ (univ : Finset (Fin r)).powerset with L S = z, (-1) ^ S.card : ℤ) : ℂ))
    (fun z => ((∑ S ∈ (univ : Finset (Fin r)).powerset with R S = z, (-1) ^ S.card : ℤ) : ℂ))
    (fun m hm => by
    rw [← sum_powerset_eq_sum_fiber L Z hLZ (· ^ m),
      ← sum_powerset_eq_sum_fiber R Z hRZ (· ^ m), ← hexpL, ← hexpR, h m hm]) z₀ hz₀Z hz₀
  -- the norms of the products
  have hnormS : ∀ S : Finset (Fin r), ‖∏ i ∈ S, α i‖ ≤ sq ^ S.card := fun S => by
    rw [norm_prod]
    exact (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hle i).trans_eq
      (Finset.prod_const sq)
  -- on the left only `S = ∅` contributes
  have hL :
      ((∑ S ∈ (univ : Finset (Fin r)).powerset with L S = z₀, (-1) ^ S.card : ℤ) : ℂ) = 1 := by
    have : ((univ : Finset (Fin r)).powerset.filter fun S => L S = z₀) = {∅} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hS
        by_contra hne
        have hpos : 0 < S.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hne)
        have hSc : S.card ≤ 2 * γ := (Finset.card_le_univ S).trans (by simpa using hr)
        have hn := congrArg norm hS
        simp only [L, z₀, norm_mul, norm_pow, hqC] at hn
        have h1 : (q : ℝ) ^ (2 * γ - S.card) * ‖∏ i ∈ S, α i‖ ≤
            (q : ℝ) ^ (2 * γ - S.card) * sq ^ S.card :=
          mul_le_mul_of_nonneg_left (hnormS S) (by positivity)
        have h2 : (q : ℝ) ^ (2 * γ - S.card) * sq ^ S.card < (q : ℝ) ^ (2 * γ) := by
          rw [show (q : ℝ) ^ (2 * γ) = (q : ℝ) ^ (2 * γ - S.card) * (q : ℝ) ^ S.card by
            rw [← pow_add, Nat.sub_add_cancel hSc]]
          refine mul_lt_mul_of_pos_left ?_ (by positivity)
          rw [← hsq2, ← pow_mul]
          exact pow_lt_pow_right₀ hsq (by omega)
        linarith
      · rintro rfl; simp [L, z₀]
    rw [this, Finset.sum_singleton]
    simp
  rw [hL] at hc
  -- so on the right some `S` contributes
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin r), R S = z₀ := by
    by_contra hno
    push Not at hno
    rw [Finset.filter_false_of_mem fun S _ => hno S, Finset.sum_empty, Int.cast_zero] at hc
    exact one_ne_zero hc
  have hn := congrArg norm hS
  simp only [R, z₀, norm_mul, norm_pow, hqC] at hn
  have hprod : ‖∏ i ∈ S, α i‖ = (q : ℝ) ^ γ := by
    have hqγ : (0 : ℝ) < (q : ℝ) ^ γ := by positivity
    rw [show (q : ℝ) ^ (2 * γ) = (q : ℝ) ^ γ * (q : ℝ) ^ γ by rw [← pow_add, two_mul]] at hn
    exact mul_left_cancel₀ hqγ.ne' hn
  have hSc : 2 * γ ≤ S.card := by
    have := (hnormS S)
    rw [hprod, ← hsq2, ← pow_mul] at this
    exact (pow_le_pow_iff_right₀ hsq).1 this
  have hSr : S.card ≤ r := by simpa using Finset.card_le_univ S
  have hr' : r = 2 * γ := by omega
  have hSuniv : S = univ := Finset.eq_univ_of_card S (by rw [Fintype.card_fin]; omega)
  rw [hSuniv] at hprod
  refine ⟨hr', fun i => le_antisymm (hle i) ?_⟩
  by_contra hlt
  push Not at hlt
  have hr1 : r = r - 1 + 1 := by have := i.2; omega
  have : ∏ j, ‖α j‖ < sq ^ (r - 1 + 1) := by
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i), pow_succ, mul_comm (sq ^ (r - 1))]
    have hrest : ∏ j ∈ univ.erase i, ‖α j‖ ≤ sq ^ (r - 1) := by
      refine (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => hle j).trans_eq ?_
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
    calc ‖α i‖ * ∏ j ∈ univ.erase i, ‖α j‖ ≤ ‖α i‖ * sq ^ (r - 1) :=
          mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
      _ < sq * sq ^ (r - 1) := mul_lt_mul_of_pos_right hlt (by positivity)
  rw [← hr1, ← norm_prod, hprod, ← hsq2, ← pow_mul, hr', mul_comm] at this
  exact lt_irrefl _ this

end Stacks.PowerProduct
