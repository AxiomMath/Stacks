module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.MinusTwoComponents
import all StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.MinusTwoComponents

/-!
# Sums over the edges of the Dynkin diagrams of types A, B and C

Evaluations of the sums `∑ s, if DynkinShape.Edge d r s then f s else 0` over
the neighbours of a vertex `r` in the Dynkin diagrams of types `A`, `B` and
`C`, at the head, the tail and the inner vertices of the chain. They feed the
boundary control of the multiplicities of a Dynkin configuration of minus-two
indices.

## References

* [Stacks Project, Tag 0C9W](https://stacks.math.columbia.edu/tag/0C9W)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

private lemma sum_if_fin_val_eq {t : ℕ} (n : ℕ) (hn : n < t)
    (f : Fin t → ℤ) :
    (∑ s : Fin t, if s.val = n then f s else 0) = f ⟨n, hn⟩ := by
  classical
  rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin t)]
  · simp
  · intro s _ hne
    simp [show s.val ≠ n from fun h => hne (Fin.ext h)]
  · simp

private lemma sum_if_fin_val_succ_eq {t : ℕ} (n : ℕ) (hn : 0 < n) (hn' : n < t)
    (f : Fin t → ℤ) :
    (∑ s : Fin t, if s.val + 1 = n then f s else 0) =
      f ⟨n - 1, by omega⟩ := by
  have hrewrite : (∑ s : Fin t, if s.val + 1 = n then f s else 0) =
      ∑ s : Fin t, if s.val = n - 1 then f s else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    by_cases h : s.val + 1 = n <;> by_cases h' : s.val = n - 1 <;> simp_all <;> omega
  rw [hrewrite, sum_if_fin_val_eq (n - 1) (by omega)]

private lemma sum_if_fin_adjacent_eq {t : ℕ} (n : ℕ) (hn : 0 < n)
    (hn' : n + 1 < t) (f : Fin t → ℤ) :
    (∑ s : Fin t,
      if n + 1 = s.val ∨ s.val + 1 = n then f s else 0) =
        f ⟨n + 1, by omega⟩ + f ⟨n - 1, by omega⟩ := by
  classical
  have hpoint (s : Fin t) :
      (if n + 1 = s.val ∨ s.val + 1 = n then f s else 0) =
        (if s.val = n + 1 then f s else 0) +
          (if s.val + 1 = n then f s else 0) := by
    by_cases h₁ : s.val = n + 1 <;> by_cases h₂ : s.val + 1 = n <;>
      simp_all <;> omega
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [sum_if_fin_val_eq (n + 1) (by omega),
    sum_if_fin_val_succ_eq n hn (by omega)]

private lemma sum_edge_A_head {t : ℕ} (ht : 1 < t) (f : Fin t → ℤ) :
    (∑ s : Fin t,
      if DynkinShape.Edge .A (⟨0, by omega⟩ : Fin t) s then f s else 0) =
        f ⟨1, by omega⟩ := by
  classical
  have hpoint (s : Fin t) :
      (if DynkinShape.Edge .A (⟨0, by omega⟩ : Fin t) s then f s else 0) =
        if s.val = 1 then f s else 0 := by
    by_cases h : s.val = 1
    all_goals simp [DynkinShape.Edge, h]
    all_goals omega
  simp_rw [hpoint]
  exact sum_if_fin_val_eq 1 (by omega) f

private lemma sum_edge_A_tail {t : ℕ} (ht : 1 < t) (f : Fin t → ℤ) :
    (∑ s : Fin t,
      if DynkinShape.Edge .A
        (⟨t - 1, by omega⟩ : Fin t) s then f s else 0) =
        f ⟨t - 2, by omega⟩ := by
  classical
  let n := t - 1
  have hn : 0 < n := by dsimp [n]; omega
  have hpoint (s : Fin t) :
      (if DynkinShape.Edge .A
        (⟨t - 1, by omega⟩ : Fin t) s then f s else 0) =
        if s.val + 1 = n then f s else 0 := by
    by_cases h : s.val + 1 = n
    all_goals simp [DynkinShape.Edge, n, h]
    all_goals omega
  simp_rw [hpoint]
  have hsum := sum_if_fin_val_succ_eq n hn (by dsimp [n]; omega) f
  convert hsum using 1; congr 1

private lemma sum_edge_A_inner {t : ℕ} (n : ℕ) (hn : 0 < n)
    (hnt : n + 1 < t) (f : Fin t → ℤ) :
    (∑ s : Fin t,
      if DynkinShape.Edge .A (⟨n, by omega⟩ : Fin t) s then f s else 0) =
        f ⟨n + 1, by omega⟩ + f ⟨n - 1, by omega⟩ := by
  classical
  have hpoint (s : Fin t) :
      (if DynkinShape.Edge .A (⟨n, by omega⟩ : Fin t) s then f s else 0) =
        if n + 1 = s.val ∨ s.val + 1 = n then f s else 0 := by
    by_cases h₁ : n + 1 = s.val <;> by_cases h₂ : s.val + 1 = n <;>
      simp [DynkinShape.Edge, h₁, h₂]
  simp_rw [hpoint]
  exact sum_if_fin_adjacent_eq n hn hnt f

/-- If the edges of `d` at `r` are those of type `A` and the larger endpoint weight is the constant
`c` along them, then the weighted edge sum is `c` times the unweighted one. -/
private lemma sum_edge_max_weight {t : ℕ} (d : DynkinShape) (r : Fin t) (c : ℤ)
    (hd : ∀ s, DynkinShape.Edge d r s ↔ DynkinShape.Edge .A r s)
    (hc : ∀ s, DynkinShape.Edge .A r s →
      max (DynkinShape.weightFactor d r) (DynkinShape.weightFactor d s) = c)
    (f : Fin t → ℤ) :
    (∑ s : Fin t, if DynkinShape.Edge d r s then
      max (DynkinShape.weightFactor d r)
        (DynkinShape.weightFactor d s) * f s else 0) =
      c * (∑ s : Fin t,
        if DynkinShape.Edge .A r s then f s else 0) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : DynkinShape.Edge .A r s
  · rw [ite_eq_left ((hd s).mpr h), ite_eq_left h, hc s h]
  · rw [ite_eq_right (mt (hd s).mp h), ite_eq_right h, mul_zero]

private lemma sum_edge_B_nonlast {t : ℕ} (r : Fin t) (hr : r.val + 1 < t)
    (f : Fin t → ℤ) :
    (∑ s : Fin t, if DynkinShape.Edge .B r s then
      max (DynkinShape.weightFactor .B r)
        (DynkinShape.weightFactor .B s) * f s else 0) =
      2 * (∑ s : Fin t,
        if DynkinShape.Edge .A r s then f s else 0) := by
  refine sum_edge_max_weight .B r 2 (fun s => by simp [DynkinShape.Edge]) (fun s _ => ?_) f
  have hfr : DynkinShape.weightFactor .B r = 2 := by
    have hnot : r.val + 1 ≠ t := by omega
    simp [DynkinShape.weightFactor, hnot]
  have hfs : DynkinShape.weightFactor .B s ≤ 2 := by
    simp [DynkinShape.weightFactor]
    split_ifs <;> omega
  rw [hfr, max_eq_left hfs]

private lemma sum_edge_B_last {t : ℕ} (ht : 1 < t) (f : Fin t → ℤ) :
    (∑ s : Fin t,
      if DynkinShape.Edge .B
          (⟨t - 1, by omega⟩ : Fin t) s then
        max (DynkinShape.weightFactor .B
            (⟨t - 1, by omega⟩ : Fin t))
          (DynkinShape.weightFactor .B s) * f s else 0) =
      2 * f ⟨t - 2, by omega⟩ := by
  rw [sum_edge_max_weight .B _ 2 (fun s => by simp [DynkinShape.Edge]) (fun s h => ?_) f,
    sum_edge_A_tail ht f]
  have hs : s.val + 1 = t - 1 := by
    simp [DynkinShape.Edge] at h
    omega
  have hfr : DynkinShape.weightFactor .B (⟨t - 1, by omega⟩ : Fin t) = 1 := by
    show (if t - 1 + 1 = t then 1 else 2) = 1
    simp [Nat.sub_add_cancel (by omega : 1 ≤ t)]
  have hfs : DynkinShape.weightFactor .B s = 2 := by
    show (if s.val + 1 = t then 1 else 2) = 2
    have hsn : s.val + 1 ≠ t := by omega
    rw [ite_eq_right hsn]
  rw [hfr, hfs]
  norm_num

private lemma sum_edge_C_nonlast {t : ℕ} (r : Fin t) (hr : r.val + 2 < t)
    (f : Fin t → ℤ) :
    (∑ s : Fin t, if DynkinShape.Edge .C r s then
      max (DynkinShape.weightFactor .C r)
        (DynkinShape.weightFactor .C s) * f s else 0) =
      (∑ s : Fin t,
        if DynkinShape.Edge .A r s then f s else 0) := by
  rw [sum_edge_max_weight .C r 1 (fun s => by simp [DynkinShape.Edge]) (fun s h => ?_) f,
    one_mul]
  have hfr : DynkinShape.weightFactor .C r = 1 := by
    show (if r.val + 1 = t then 2 else 1) = 1
    have hnot : r.val + 1 ≠ t := by omega
    rw [ite_eq_right hnot]
  have hfs : DynkinShape.weightFactor .C s = 1 := by
    simp [DynkinShape.Edge] at h
    have hsn : s.val + 1 ≠ t := by omega
    show (if s.val + 1 = t then 2 else 1) = 1
    rw [ite_eq_right hsn]
  rw [hfr, hfs]
  simp

private lemma sum_edge_C_last {t : ℕ} (ht : 1 < t) (f : Fin t → ℤ) :
    (∑ s : Fin t,
      if DynkinShape.Edge .C
          (⟨t - 1, by omega⟩ : Fin t) s then
        max (DynkinShape.weightFactor .C
            (⟨t - 1, by omega⟩ : Fin t))
          (DynkinShape.weightFactor .C s) * f s else 0) =
      2 * f ⟨t - 2, by omega⟩ := by
  rw [sum_edge_max_weight .C _ 2 (fun s => by simp [DynkinShape.Edge]) (fun s h => ?_) f,
    sum_edge_A_tail ht f]
  have hs : s.val + 1 = t - 1 := by
    simp [DynkinShape.Edge] at h
    omega
  have hfr : DynkinShape.weightFactor .C (⟨t - 1, by omega⟩ : Fin t) = 2 := by
    show (if t - 1 + 1 = t then 2 else 1) = 2
    simp [Nat.sub_add_cancel (by omega : 1 ≤ t)]
  have hfs : DynkinShape.weightFactor .C s = 1 := by
    have hsn : s.val + 1 ≠ t := by omega
    show (if s.val + 1 = t then 2 else 1) = 1
    rw [ite_eq_right hsn]
  rw [hfr, hfs]
  norm_num

private lemma sum_edge_C_penultimate {t : ℕ} (ht : 2 < t) (f : Fin t → ℤ) :
    (∑ s : Fin t,
      if DynkinShape.Edge .C
          (⟨t - 2, by omega⟩ : Fin t) s then
        max (DynkinShape.weightFactor .C
            (⟨t - 2, by omega⟩ : Fin t))
          (DynkinShape.weightFactor .C s) * f s else 0) =
      f ⟨t - 3, by omega⟩ + 2 * f ⟨t - 1, by omega⟩ := by
  classical
  let r : Fin t := ⟨t - 2, by omega⟩
  have hpoint (s : Fin t) :
      (if DynkinShape.Edge .C r s then
        max (DynkinShape.weightFactor .C r)
          (DynkinShape.weightFactor .C s) * f s else 0) =
      (if DynkinShape.Edge .A r s then f s else 0) +
        (if s.val = t - 1 then f s else 0) := by
    by_cases hedge : DynkinShape.Edge .A r s
    · have hedgeC : DynkinShape.Edge .C r s := by
        simpa [DynkinShape.Edge] using hedge
      by_cases hlast : s.val = t - 1
      · have hfr : DynkinShape.weightFactor .C r = 1 := by
          show (if t - 2 + 1 = t then 2 else 1) = 1
          rw [ite_eq_right (by omega)]
        have hfs : DynkinShape.weightFactor .C s = 2 := by
          show (if s.val + 1 = t then 2 else 1) = 2
          rw [ite_eq_left (by omega)]
        simp [hedge, hedgeC, hlast, hfr, hfs]
        ring
      · have hfr : DynkinShape.weightFactor .C r = 1 := by
          show (if t - 2 + 1 = t then 2 else 1) = 1
          rw [ite_eq_right (by omega)]
        have hh := hedge
        simp [DynkinShape.Edge, r] at hh
        have hsnot : s.val + 1 ≠ t := by omega
        have hfs : DynkinShape.weightFactor .C s = 1 := by
          simp [DynkinShape.weightFactor, hsnot]
        simp [hedge, hedgeC, hlast, hfr, hfs]
    · have hedgeC : ¬ DynkinShape.Edge .C r s := by
        simpa [DynkinShape.Edge] using hedge
      have hlast : s.val ≠ t - 1 := by
        intro h
        have hsEq : s = ⟨t - 1, by omega⟩ := Fin.ext h
        have hA : DynkinShape.Edge .A r s := by
          rw [hsEq]
          simp [DynkinShape.Edge, r]
          omega
        exact hedge hA
      simp [hedge, hedgeC, hlast]
  calc
    _ = ∑ s : Fin t,
        ((if DynkinShape.Edge .A r s then f s else 0) +
          (if s.val = t - 1 then f s else 0)) :=
            Finset.sum_congr rfl fun s _ => hpoint s
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_edge_A_inner (t - 2) (by omega) (by omega) f,
        sum_if_fin_val_eq (t - 1) (by omega) f]
      have h₁ : (⟨t - 2 + 1, by omega⟩ : Fin t) = ⟨t - 1, by omega⟩ :=
        Fin.ext (show t - 2 + 1 = t - 1 by omega)
      have h₂ : (⟨t - 2 - 1, by omega⟩ : Fin t) = ⟨t - 3, by omega⟩ :=
        Fin.ext (show t - 2 - 1 = t - 3 by omega)
      rw [h₁, h₂]
      ring

end AlgebraicGeometry.NumericalType
