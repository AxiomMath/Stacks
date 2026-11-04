module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.TwoVertices
public import Mathlib

/-!
# Three-vertex subgraphs

Three distinct minus-two indices spanning a connected subgraph form a path, and
after ordering the path the edge data is that of `A₃`, `B₃` or `C₃`. In
particular there is no triangle of minus-two indices.

## Main results

* `AlgebraicGeometry.NumericalType.exists_ordering_of_three_minus_two_indices`.

## References

* [Stacks Project, Tag 0C7R](https://stacks.math.columbia.edu/tag/0C7R)
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

private lemma positive_edge_data (T : NumericalType) (hn : 3 < T.componentCount)
    (i j : Fin T.componentCount)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hpos : 0 < T.intersection i j) :
    ∃ r s : ℤ,
      (r = 1 ∨ r = 2 ∨ r = 3) ∧ (s = 1 ∨ s = 2 ∨ s = 3) ∧
      ((r = 1 ∧ s = 1) ∨ (r = 2 ∧ s = 1) ∨ (r = 1 ∧ s = 2) ∨
        (r = 3 ∧ s = 1) ∨ (r = 1 ∧ s = 3)) ∧
      T.intersection i j = r * T.weight i ∧
      T.intersection i j = s * T.weight j ∧
      r * T.multiplicity j ≤ 2 * T.multiplicity i ∧
      s * T.multiplicity i ≤ 2 * T.multiplicity j := by
  rcases isTwoVertexConfiguration_or_swap T (by omega) i j hi hj hpos with
    hpair | hpair
  · rcases hpair with hA | hB | hG
    · rcases hA with ⟨w, hwi, hwj, hii, he, hji, hjj, hmj, hmi⟩
      refine ⟨1, 1, Or.inl rfl, Or.inl rfl, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
      · simpa [hwi] using he
      · simpa [hwj] using he
      · simpa using hmj
      · simpa using hmi
    · rcases hB with ⟨w, hwi, hwj, hii, he, hji, hjj, hmj, hmi⟩
      refine ⟨2, 1, Or.inr (Or.inl rfl), Or.inl rfl,
        Or.inr (Or.inl ⟨rfl, rfl⟩), ?_, ?_, ?_, ?_⟩
      · simpa [hwi] using he
      · simpa [hwj] using he
      · omega
      · simpa using hmi
    · rcases hG with ⟨w, hwi, hwj, hii, he, hji, hjj, hmj, hmi⟩
      refine ⟨3, 1, Or.inr (Or.inr rfl), Or.inl rfl,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), ?_, ?_, ?_, ?_⟩
      · simpa [hwi] using he
      · simpa [hwj] using he
      · exact hmj
      · simpa using hmi
  · rcases hpair with hA | hB | hG
    · rcases hA with ⟨w, hwi, hwj, hii, he, hji, hjj, hmi, hmj⟩
      have he' : T.intersection i j = w := (T.intersection_symm i j).trans he
      refine ⟨1, 1, Or.inl rfl, Or.inl rfl, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
      · simpa [hwj] using he'
      · simpa [hwi] using he'
      · simpa using hmj
      · simpa using hmi
    · rcases hB with ⟨w, hwi, hwj, hii, he, hji, hjj, hmi, hmj⟩
      refine ⟨1, 2, Or.inl rfl, Or.inr (Or.inl rfl),
        Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_, ?_, ?_, ?_⟩
      · simpa [hwj] using (T.intersection_symm i j).trans he
      · have he' : T.intersection i j = 2 * w := by
          calc
            T.intersection i j = T.intersection j i := T.intersection_symm i j
            _ = 2 * w := by simpa [mul_comm] using he
        simpa [hwi] using he'
      · simpa using hmj
      · omega
    · rcases hG with ⟨w, hwi, hwj, hii, he, hji, hjj, hmi, hmj⟩
      refine ⟨1, 3, Or.inl rfl, Or.inr (Or.inr rfl),
        Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))), ?_, ?_, ?_, ?_⟩
      · simpa [hwj] using (T.intersection_symm i j).trans he
      · have he' : T.intersection i j = 3 * w := by
          calc
            T.intersection i j = T.intersection j i := T.intersection_symm i j
            _ = 3 * w := by simpa [mul_comm] using he
        simpa [hwi] using he'
      · simpa using hmj
      · omega

private lemma row_sum_le (T : NumericalType) (i : Fin T.componentCount)
    (S : Finset (Fin T.componentCount))
    (hii : T.intersection i i = -2 * T.weight i) (hS : S ⊆ Finset.univ.erase i) :
    ∑ j ∈ S, T.intersection i j * T.multiplicity j ≤
      2 * T.weight i * T.multiplicity i := by
  have hbalance := T.intersection_mul_multiplicity i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hii] at hbalance
  have := Finset.sum_le_sum_of_subset_of_nonneg hS fun j hj _ =>
    mul_nonneg (T.intersection_nonneg i j (Finset.ne_of_mem_erase hj).symm)
      (T.multiplicity_pos j).le
  linarith

private lemma two_row_bound (T : NumericalType) (i j k : Fin T.componentCount)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hii : T.intersection i i = -2 * T.weight i) :
    T.intersection i j * T.multiplicity j +
        T.intersection i k * T.multiplicity k ≤
      2 * T.weight i * T.multiplicity i := by
  classical
  simpa [Finset.sum_pair hjk] using row_sum_le T i {j, k} hii
    (by simp [Finset.insert_subset_iff, Ne.symm hij, Ne.symm hik])

private lemma no_other_neighbor_of_saturated_row (T : NumericalType)
    (i : Fin T.componentCount) (S : Finset (Fin T.componentCount))
    (hii : T.intersection i i = -2 * T.weight i)
    (hS : S ⊆ Finset.univ.erase i)
    (hsat : ∑ j ∈ S, T.intersection i j * T.multiplicity j =
      2 * T.weight i * T.multiplicity i)
    (k : Fin T.componentCount) (hki : k ≠ i) (hkS : k ∉ S) :
    T.intersection i k = 0 := by
  classical
  have hlarge := row_sum_le T i (insert k S) hii
    (Finset.insert_subset (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ _⟩) hS)
  rw [Finset.sum_insert hkS, hsat] at hlarge
  have hnn := mul_nonneg (T.intersection_nonneg i k hki.symm) (T.multiplicity_pos k).le
  exact (mul_eq_zero.mp (by linarith)).resolve_right (T.multiplicity_pos k).ne'


private lemma normalized_two_row_bound (T : NumericalType)
    (i j k : Fin T.componentCount) (r s : ℤ)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hii : T.intersection i i = -2 * T.weight i)
    (hij' : T.intersection i j = r * T.weight i)
    (hik' : T.intersection i k = s * T.weight i) :
    r * T.multiplicity j + s * T.multiplicity k ≤ 2 * T.multiplicity i := by
  have hraw := two_row_bound T i j k hij hik hjk hii
  rw [hij', hik'] at hraw
  exact le_of_mul_le_mul_left (by linarith) (T.weight_pos i)

private lemma exists_outside_three (T : NumericalType) (hn : 3 < T.componentCount)
    (a b c : Fin T.componentCount) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ z, z ≠ a ∧ z ≠ b ∧ z ≠ c := by
  classical
  by_contra h
  have hall : ∀ z : Fin T.componentCount, z = a ∨ z = b ∨ z = c := by
    intro z
    by_contra hz
    exact h ⟨z, fun e => hz (.inl e), fun e => hz (.inr (.inl e)),
      fun e => hz (.inr (.inr e))⟩
  let v : Fin 3 → Fin T.componentCount := ![a, b, c]
  have hinj : Function.Injective v := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [v]
  have hsurj : Function.Surjective v := by
    intro z
    rcases hall z with rfl | rfl | rfl
    · exact ⟨0, by simp [v]⟩
    · exact ⟨1, by simp [v]⟩
    · exact ⟨2, by simp [v]⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective v ⟨hinj, hsurj⟩)
  simp only [Fintype.card_fin] at hcard
  omega

private lemma three_rows_saturated_false (T : NumericalType)
    (hn : 3 < T.componentCount) (a b c : Fin T.componentCount)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haa : T.intersection a a = -2 * T.weight a)
    (hbb : T.intersection b b = -2 * T.weight b)
    (hcc : T.intersection c c = -2 * T.weight c)
    (hsata : ∑ j ∈ ({b, c} : Finset (Fin T.componentCount)),
      T.intersection a j * T.multiplicity j = 2 * T.weight a * T.multiplicity a)
    (hsatb : ∑ j ∈ ({a, c} : Finset (Fin T.componentCount)),
      T.intersection b j * T.multiplicity j = 2 * T.weight b * T.multiplicity b)
    (hsatc : ∑ j ∈ ({a, b} : Finset (Fin T.componentCount)),
      T.intersection c j * T.multiplicity j = 2 * T.weight c * T.multiplicity c) : False := by
  obtain ⟨z, hza, hzb, hzc⟩ := exists_outside_three T hn a b c hab hac hbc
  have hzabc : z ∉ ({a, b, c} : Set (Fin T.componentCount)) := by
    simp [hza, hzb, hzc]
  have hsa : ({b, c} : Finset (Fin T.componentCount)) ⊆ Finset.univ.erase a := by
    simp [Finset.insert_subset_iff, Ne.symm hab, Ne.symm hac]
  have hsb : ({a, c} : Finset (Fin T.componentCount)) ⊆ Finset.univ.erase b := by
    simp [Finset.insert_subset_iff, hab, Ne.symm hbc]
  have hsc : ({a, b} : Finset (Fin T.componentCount)) ⊆ Finset.univ.erase c := by
    simp [Finset.insert_subset_iff, hac, hbc]
  have hcross : ∀ x, x ∈ ({a, b, c} : Set (Fin T.componentCount)) →
      ∀ y, y ∉ ({a, b, c} : Set (Fin T.componentCount)) →
        T.intersection x y = 0 := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl
    · exact no_other_neighbor_of_saturated_row T _ {b, c} haa hsa hsata y (by tauto)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    · exact no_other_neighbor_of_saturated_row T _ {a, c} hbb hsb hsatb y (by tauto)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    · exact no_other_neighbor_of_saturated_row T _ {a, b} hcc hsc hsatc y (by tauto)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  exact T.connected ⟨{a, b, c}, by simp, fun heq => hzabc (by simp [heq]), hcross⟩

/-- A row whose two other nonzero entries are `r` and `s` times its weight is saturated once
`r * m j + s * m k = 2 * m i`. -/
private lemma saturated_pair_row (T : NumericalType) (i j k : Fin T.componentCount)
    (hjk : j ≠ k) (r s : ℤ) (hij : T.intersection i j = r * T.weight i)
    (hik : T.intersection i k = s * T.weight i)
    (hm : r * T.multiplicity j + s * T.multiplicity k = 2 * T.multiplicity i) :
    ∑ x ∈ ({j, k} : Finset (Fin T.componentCount)),
      T.intersection i x * T.multiplicity x = 2 * T.weight i * T.multiplicity i := by
  rw [Finset.sum_pair hjk, hij, hik]
  linear_combination T.weight i * hm

private lemma no_triangle (T : NumericalType) (hn : 3 < T.componentCount)
    (a b c : Fin T.componentCount)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : IsMinusTwoIndex T a) (hb : IsMinusTwoIndex T b)
    (hc : IsMinusTwoIndex T c)
    (habpos : 0 < T.intersection a b) (hbcpos : 0 < T.intersection b c)
    (hcapos : 0 < T.intersection c a) : False := by
  have haa := ha.2
  have hbb := hb.2
  have hcc := hc.2
  obtain ⟨r₁, s₁, _, _, hshape₁, hab₁, hab₂, _, _⟩ :=
    positive_edge_data T hn a b ha hb habpos
  obtain ⟨r₂, s₂, _, _, hshape₂, hbc₁, hbc₂, _, _⟩ :=
    positive_edge_data T hn b c hb hc hbcpos
  obtain ⟨r₃, s₃, _, _, hshape₃, hca₁, hca₂, _, _⟩ :=
    positive_edge_data T hn c a hc ha hcapos
  have hba₂ : T.intersection b a = s₁ * T.weight b := (T.intersection_symm b a).trans hab₂
  have hcb₂ : T.intersection c b = s₂ * T.weight c := (T.intersection_symm c b).trans hbc₂
  have hac₂ : T.intersection a c = s₃ * T.weight a := (T.intersection_symm a c).trans hca₂
  have hwab : r₁ * T.weight a = s₁ * T.weight b := hab₁.symm.trans hab₂
  have hwbc : r₂ * T.weight b = s₂ * T.weight c := hbc₁.symm.trans hbc₂
  have hwca : r₃ * T.weight c = s₃ * T.weight a := hca₁.symm.trans hca₂
  have hwposa := T.weight_pos a
  have hwposb := T.weight_pos b
  have hwposc := T.weight_pos c
  have hmaposa := T.multiplicity_pos a
  have hmaposb := T.multiplicity_pos b
  have hmaposc := T.multiplicity_pos c
  have hrowa := normalized_two_row_bound T a b c r₁ s₃ hab hac hbc haa hab₁ hac₂
  have hrowb := normalized_two_row_bound T b a c s₁ r₂ hab.symm hbc hac hbb hba₂ hbc₁
  have hrowc := normalized_two_row_bound T c a b r₃ s₂ hac.symm hbc.symm hab hcc hca₁ hcb₂
  rcases hshape₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rcases hshape₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rcases hshape₃ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals try omega
  all_goals
    exact three_rows_saturated_false T hn a b c hab hac hbc haa hbb hcc
      (saturated_pair_row T a b c hbc _ _ hab₁ hac₂ (by omega))
      (saturated_pair_row T b a c hac _ _ hba₂ hbc₁ (by omega))
      (saturated_pair_row T c a b hab _ _ hca₁ hcb₂ (by omega))

private lemma path_factors_good (T : NumericalType) (hn : 3 < T.componentCount)
    (a b c : Fin T.componentCount) (r s t u : ℤ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haa : T.intersection a a = -2 * T.weight a)
    (hbb : T.intersection b b = -2 * T.weight b)
    (hcc : T.intersection c c = -2 * T.weight c)
    (hshape₁ : (r = 1 ∧ s = 1) ∨ (r = 2 ∧ s = 1) ∨
      (r = 1 ∧ s = 2) ∨ (r = 3 ∧ s = 1) ∨ (r = 1 ∧ s = 3))
    (hshape₂ : (t = 1 ∧ u = 1) ∨ (t = 2 ∧ u = 1) ∨
      (t = 1 ∧ u = 2) ∨ (t = 3 ∧ u = 1) ∨ (t = 1 ∧ u = 3))
    (hab₁ : T.intersection a b = r * T.weight a)
    (hab₂ : T.intersection a b = s * T.weight b)
    (hbc₁ : T.intersection b c = t * T.weight b)
    (hbc₂ : T.intersection b c = u * T.weight c)
    (hm₁ : r * T.multiplicity b ≤ 2 * T.multiplicity a)
    (hm₃ : t * T.multiplicity c ≤ 2 * T.multiplicity b)
    (hm₄ : u * T.multiplicity b ≤ 2 * T.multiplicity c)
    (hmid : s * T.multiplicity a + t * T.multiplicity c ≤
      2 * T.multiplicity b) (haczero : T.intersection a c = 0) :
    (r = 1 ∧ s = 1 ∧ t = 1 ∧ u = 1) ∨
      (r = 1 ∧ s = 1 ∧ t = 2 ∧ u = 1) ∨
      (r = 1 ∧ s = 1 ∧ t = 1 ∧ u = 2) ∨
      (r = 2 ∧ s = 1 ∧ t = 1 ∧ u = 1) ∨
      (r = 1 ∧ s = 2 ∧ t = 1 ∧ u = 1) := by
  have hba₂ : T.intersection b a = s * T.weight b := (T.intersection_symm b a).trans hab₂
  have hcb₂ : T.intersection c b = u * T.weight c := (T.intersection_symm c b).trans hbc₂
  have hca₀ : T.intersection c a = 0 * T.weight c := by
    rw [T.intersection_symm, haczero, zero_mul]
  have hac₀ : T.intersection a c = 0 * T.weight a := by rw [haczero, zero_mul]
  have hma := T.multiplicity_pos a
  have hmb := T.multiplicity_pos b
  have hmc := T.multiplicity_pos c
  rcases hshape₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases hshape₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  first
  | decide
  | exact (three_rows_saturated_false T hn a b c hab hac hbc haa hbb hcc
      (saturated_pair_row T a b c hbc _ _ hab₁ hac₀ (by omega))
      (saturated_pair_row T b a c hac _ _ hba₂ hbc₁ (by omega))
      (saturated_pair_row T c a b hab _ _ hca₀ hcb₂ (by omega))).elim

private lemma ordered_path_edge_data (T : NumericalType) (hn : 3 < T.componentCount)
    (a b c : Fin T.componentCount)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : IsMinusTwoIndex T a) (hb : IsMinusTwoIndex T b)
    (hc : IsMinusTwoIndex T c)
    (habpos : 0 < T.intersection a b) (hbcpos : 0 < T.intersection b c) :
    ∃ r s t u : ℤ,
      ((r = 1 ∧ s = 1) ∨ (r = 2 ∧ s = 1) ∨ (r = 1 ∧ s = 2) ∨
        (r = 3 ∧ s = 1) ∨ (r = 1 ∧ s = 3)) ∧
      ((t = 1 ∧ u = 1) ∨ (t = 2 ∧ u = 1) ∨ (t = 1 ∧ u = 2) ∨
        (t = 3 ∧ u = 1) ∨ (t = 1 ∧ u = 3)) ∧
      T.intersection a b = r * T.weight a ∧
      T.intersection a b = s * T.weight b ∧
      T.intersection b c = t * T.weight b ∧
      T.intersection b c = u * T.weight c ∧
      r * T.multiplicity b ≤ 2 * T.multiplicity a ∧
      s * T.multiplicity a ≤ 2 * T.multiplicity b ∧
      t * T.multiplicity c ≤ 2 * T.multiplicity b ∧
      u * T.multiplicity b ≤ 2 * T.multiplicity c ∧
      s * T.multiplicity a + t * T.multiplicity c ≤ 2 * T.multiplicity b ∧
      T.intersection a c = 0 ∧
      ((r = 1 ∧ s = 1 ∧ t = 1 ∧ u = 1) ∨
        (r = 1 ∧ s = 1 ∧ t = 2 ∧ u = 1) ∨
        (r = 1 ∧ s = 1 ∧ t = 1 ∧ u = 2) ∨
        (r = 2 ∧ s = 1 ∧ t = 1 ∧ u = 1) ∨
        (r = 1 ∧ s = 2 ∧ t = 1 ∧ u = 1)) := by
  have haczero : T.intersection a c = 0 := by
    by_contra hne
    exact no_triangle T hn a b c hab hac hbc ha hb hc habpos hbcpos
      (by simpa [T.intersection_symm] using (T.intersection_nonneg a c hac).lt_of_ne' hne)
  obtain ⟨r, s, _, _, hshape₁, hab₁, hab₂, hm₁, hm₂⟩ :=
    positive_edge_data T hn a b ha hb habpos
  obtain ⟨t, u, _, _, hshape₂, hbc₁, hbc₂, hm₃, hm₄⟩ :=
    positive_edge_data T hn b c hb hc hbcpos
  have hba₂ : T.intersection b a = s * T.weight b := (T.intersection_symm b a).trans hab₂
  have hmid := normalized_two_row_bound T b a c s t hab.symm hbc hac hb.2 hba₂ hbc₁
  have hgood := path_factors_good T hn a b c r s t u
    hab hac hbc ha.2 hb.2 hc.2 hshape₁ hshape₂ hab₁ hab₂ hbc₁ hbc₂
    hm₁ hm₃ hm₄ hmid haczero
  exact ⟨r, s, t, u, hshape₁, hshape₂, hab₁, hab₂, hbc₁, hbc₂, hm₁, hm₂,
    hm₃, hm₄, hmid, haczero, hgood⟩

private abbrev IsA3Path (T : NumericalType) (v : Fin 3 → Fin T.componentCount) : Prop :=
  ∃ w : ℤ,
    T.weight (v 0) = w ∧ T.weight (v 1) = w ∧ T.weight (v 2) = w ∧
    T.intersection (v 0) (v 0) = -2 * w ∧ T.intersection (v 0) (v 1) = w ∧
    T.intersection (v 0) (v 2) = 0 ∧ T.intersection (v 1) (v 0) = w ∧
    T.intersection (v 1) (v 1) = -2 * w ∧ T.intersection (v 1) (v 2) = w ∧
    T.intersection (v 2) (v 0) = 0 ∧ T.intersection (v 2) (v 1) = w ∧
    T.intersection (v 2) (v 2) = -2 * w ∧
    T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0) ∧
    T.multiplicity (v 0) + T.multiplicity (v 2) ≤ 2 * T.multiplicity (v 1) ∧
    T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 2)

private abbrev IsC3Path (T : NumericalType) (v : Fin 3 → Fin T.componentCount) : Prop :=
  ∃ w : ℤ,
    T.weight (v 0) = w ∧ T.weight (v 1) = w ∧ T.weight (v 2) = 2 * w ∧
    T.intersection (v 0) (v 0) = -2 * w ∧ T.intersection (v 0) (v 1) = w ∧
    T.intersection (v 0) (v 2) = 0 ∧ T.intersection (v 1) (v 0) = w ∧
    T.intersection (v 1) (v 1) = -2 * w ∧ T.intersection (v 1) (v 2) = 2 * w ∧
    T.intersection (v 2) (v 0) = 0 ∧ T.intersection (v 2) (v 1) = 2 * w ∧
    T.intersection (v 2) (v 2) = -4 * w ∧
    T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0) ∧
    T.multiplicity (v 0) + 2 * T.multiplicity (v 2) ≤ 2 * T.multiplicity (v 1) ∧
    T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 2)

private abbrev IsB3Path (T : NumericalType) (v : Fin 3 → Fin T.componentCount) : Prop :=
  ∃ w : ℤ,
    T.weight (v 0) = 2 * w ∧ T.weight (v 1) = 2 * w ∧ T.weight (v 2) = w ∧
    T.intersection (v 0) (v 0) = -4 * w ∧ T.intersection (v 0) (v 1) = 2 * w ∧
    T.intersection (v 0) (v 2) = 0 ∧ T.intersection (v 1) (v 0) = 2 * w ∧
    T.intersection (v 1) (v 1) = -4 * w ∧ T.intersection (v 1) (v 2) = 2 * w ∧
    T.intersection (v 2) (v 0) = 0 ∧ T.intersection (v 2) (v 1) = 2 * w ∧
    T.intersection (v 2) (v 2) = -2 * w ∧
    T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0) ∧
    T.multiplicity (v 0) + T.multiplicity (v 2) ≤ 2 * T.multiplicity (v 1) ∧
    T.multiplicity (v 1) ≤ T.multiplicity (v 2)

private abbrev PathConclusion (T : NumericalType)
    (v : Fin 3 → Fin T.componentCount) : Prop :=
  IsA3Path T v ∨ IsC3Path T v ∨ IsB3Path T v

private lemma ordered_fin3 (T : NumericalType) (a b c : Fin T.componentCount)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] ∧ Set.range ![a, b, c] = {a, b, c} := by
  refine ⟨fun x y hxy => ?_, by ext; simp [or_comm, or_left_comm]⟩
  fin_cases x <;> fin_cases y <;> simp_all

private lemma path_to_ordering (T : NumericalType)
    (a b c : Fin T.componentCount)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : IsMinusTwoIndex T a) (hb : IsMinusTwoIndex T b)
    (hc : IsMinusTwoIndex T c)
    (r s t u : ℤ)
    (hab₁ : T.intersection a b = r * T.weight a)
    (hab₂ : T.intersection a b = s * T.weight b)
    (hbc₁ : T.intersection b c = t * T.weight b)
    (hbc₂ : T.intersection b c = u * T.weight c)
    (hm₁ : r * T.multiplicity b ≤ 2 * T.multiplicity a)
    (hm₂ : s * T.multiplicity a ≤ 2 * T.multiplicity b)
    (hm₃ : t * T.multiplicity c ≤ 2 * T.multiplicity b)
    (hm₄ : u * T.multiplicity b ≤ 2 * T.multiplicity c)
    (hmid : s * T.multiplicity a + t * T.multiplicity c ≤
      2 * T.multiplicity b)
    (haczero : T.intersection a c = 0)
    (hgood :
      (r = 1 ∧ s = 1 ∧ t = 1 ∧ u = 1) ∨
      (r = 1 ∧ s = 1 ∧ t = 2 ∧ u = 1) ∨
      (r = 1 ∧ s = 1 ∧ t = 1 ∧ u = 2) ∨
      (r = 2 ∧ s = 1 ∧ t = 1 ∧ u = 1) ∨
      (r = 1 ∧ s = 2 ∧ t = 1 ∧ u = 1)) :
    ∃ v : Fin 3 → Fin T.componentCount,
      Function.Injective v ∧ Set.range v = {a, b, c} ∧ PathConclusion T v := by
  have haa := ha.2
  have hbb := hb.2
  have hcc := hc.2
  rcases hgood with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩
  · let v : Fin 3 → Fin T.componentCount := ![a, b, c]
    obtain ⟨hv, hrange⟩ := ordered_fin3 T a b c hab hac hbc
    refine ⟨v, hv, hrange, ?_⟩
    left
    refine ⟨T.weight a, ?_⟩
    simp_all [v, T.intersection_symm]
  · let v : Fin 3 → Fin T.componentCount := ![a, b, c]
    obtain ⟨hv, hrange⟩ := ordered_fin3 T a b c hab hac hbc
    refine ⟨v, hv, hrange, ?_⟩
    right
    left
    refine ⟨T.weight a, ?_⟩
    simp_all [v, T.intersection_symm]
    omega
  · let v : Fin 3 → Fin T.componentCount := ![a, b, c]
    obtain ⟨hv, hrange⟩ := ordered_fin3 T a b c hab hac hbc
    refine ⟨v, hv, hrange, ?_⟩
    right
    right
    refine ⟨T.weight c, ?_⟩
    have hwa : T.weight a = 2 * T.weight c := by
      have habw : T.weight a = T.weight b := by
        simpa using hab₁.symm.trans hab₂
      have hbcw : T.weight b = 2 * T.weight c := by
        simpa using hbc₁.symm.trans hbc₂
      omega
    have hmbc : T.multiplicity b ≤ T.multiplicity c := by omega
    simp_all [v, T.intersection_symm]
    omega
  · let v : Fin 3 → Fin T.componentCount := ![c, b, a]
    obtain ⟨hv, hrange⟩ := ordered_fin3 T c b a hbc.symm hac.symm hab.symm
    refine ⟨v, hv, by simp [v], ?_⟩
    right
    right
    refine ⟨T.weight a, ?_⟩
    have hmbma : T.multiplicity b ≤ T.multiplicity a := by omega
    simp_all [v, T.intersection_symm]
    omega
  · let v : Fin 3 → Fin T.componentCount := ![c, b, a]
    obtain ⟨hv, hrange⟩ := ordered_fin3 T c b a hbc.symm hac.symm hab.symm
    refine ⟨v, hv, by simp [v], ?_⟩
    right
    left
    refine ⟨T.weight b, ?_⟩
    have hmbmc : T.multiplicity b ≤ 2 * T.multiplicity c := by omega
    have hmbma : T.multiplicity b ≤ 2 * T.multiplicity a := by omega
    simp_all [v, T.intersection_symm]
    omega

-- The expanded output alternatives need extra reduction fuel during elaboration.
/-- Three distinct minus-two indices in a numerical type with more than three
components, at least two of whose pairwise intersections are nonzero, can be
ordered so that their numerical data have one of the three listed weighted-path
forms. -/
@[stacks 0C7R]
public theorem exists_ordering_of_three_minus_two_indices
    (T : NumericalType) (hn : 3 < T.componentCount)
    (i j k : Fin T.componentCount)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hk : IsMinusTwoIndex T k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hintersections :
      (T.intersection i j ≠ 0 ∧ T.intersection i k ≠ 0) ∨
      (T.intersection i j ≠ 0 ∧ T.intersection j k ≠ 0) ∨
      (T.intersection i k ≠ 0 ∧ T.intersection j k ≠ 0)) :
    ∃ v : Fin 3 → Fin T.componentCount,
      Function.Injective v ∧ Set.range v = {i, j, k} ∧
        ((∃ w : ℤ,
            T.weight (v 0) = w ∧
            T.weight (v 1) = w ∧
            T.weight (v 2) = w ∧
            T.intersection (v 0) (v 0) = -2 * w ∧
            T.intersection (v 0) (v 1) = w ∧
            T.intersection (v 0) (v 2) = 0 ∧
            T.intersection (v 1) (v 0) = w ∧
            T.intersection (v 1) (v 1) = -2 * w ∧
            T.intersection (v 1) (v 2) = w ∧
            T.intersection (v 2) (v 0) = 0 ∧
            T.intersection (v 2) (v 1) = w ∧
            T.intersection (v 2) (v 2) = -2 * w ∧
            T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0) ∧
            T.multiplicity (v 0) + T.multiplicity (v 2) ≤
              2 * T.multiplicity (v 1) ∧
            T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 2)) ∨
          (∃ w : ℤ,
            T.weight (v 0) = w ∧
            T.weight (v 1) = w ∧
            T.weight (v 2) = 2 * w ∧
            T.intersection (v 0) (v 0) = -2 * w ∧
            T.intersection (v 0) (v 1) = w ∧
            T.intersection (v 0) (v 2) = 0 ∧
            T.intersection (v 1) (v 0) = w ∧
            T.intersection (v 1) (v 1) = -2 * w ∧
            T.intersection (v 1) (v 2) = 2 * w ∧
            T.intersection (v 2) (v 0) = 0 ∧
            T.intersection (v 2) (v 1) = 2 * w ∧
            T.intersection (v 2) (v 2) = -4 * w ∧
            T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0) ∧
            T.multiplicity (v 0) + 2 * T.multiplicity (v 2) ≤
              2 * T.multiplicity (v 1) ∧
            T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 2)) ∨
          (∃ w : ℤ,
            T.weight (v 0) = 2 * w ∧
            T.weight (v 1) = 2 * w ∧
            T.weight (v 2) = w ∧
            T.intersection (v 0) (v 0) = -4 * w ∧
            T.intersection (v 0) (v 1) = 2 * w ∧
            T.intersection (v 0) (v 2) = 0 ∧
            T.intersection (v 1) (v 0) = 2 * w ∧
            T.intersection (v 1) (v 1) = -4 * w ∧
            T.intersection (v 1) (v 2) = 2 * w ∧
            T.intersection (v 2) (v 0) = 0 ∧
            T.intersection (v 2) (v 1) = 2 * w ∧
            T.intersection (v 2) (v 2) = -2 * w ∧
            T.multiplicity (v 1) ≤ 2 * T.multiplicity (v 0) ∧
            T.multiplicity (v 0) + T.multiplicity (v 2) ≤
              2 * T.multiplicity (v 1) ∧
            T.multiplicity (v 1) ≤ T.multiplicity (v 2))) := by
  show ∃ v : Fin 3 → Fin T.componentCount,
    Function.Injective v ∧ Set.range v = {i, j, k} ∧ PathConclusion T v
  rcases hintersections with hijik | hijjk | hikjk
  · have hikpos : 0 < T.intersection i k :=
      (T.intersection_nonneg i k hik).lt_of_ne' hijik.2
    have hjiPos : 0 < T.intersection j i := by
      simpa [T.intersection_symm] using (T.intersection_nonneg i j hij).lt_of_ne' hijik.1
    obtain ⟨r, s, t, u, _, _, hab₁, hab₂, hbc₁, hbc₂,
      hm₁, hm₂, hm₃, hm₄, hmid, hzero, hgood⟩ :=
      ordered_path_edge_data T hn j i k hij.symm hjk hik
        hj hi hk hjiPos hikpos
    obtain ⟨v, hv, hrange, hconfig⟩ := path_to_ordering T j i k
      hij.symm hjk hik hj hi hk r s t u hab₁ hab₂ hbc₁ hbc₂
      hm₁ hm₂ hm₃ hm₄ hmid hzero hgood
    refine ⟨v, hv, ?_, hconfig⟩
    simpa [Set.insert_comm] using hrange
  · have hijpos : 0 < T.intersection i j :=
      (T.intersection_nonneg i j hij).lt_of_ne' hijjk.1
    have hjkpos : 0 < T.intersection j k :=
      (T.intersection_nonneg j k hjk).lt_of_ne' hijjk.2
    obtain ⟨r, s, t, u, _, _, hab₁, hab₂, hbc₁, hbc₂,
      hm₁, hm₂, hm₃, hm₄, hmid, hzero, hgood⟩ :=
      ordered_path_edge_data T hn i j k hij hik hjk
        hi hj hk hijpos hjkpos
    exact path_to_ordering T i j k hij hik hjk hi hj hk r s t u hab₁ hab₂ hbc₁ hbc₂
      hm₁ hm₂ hm₃ hm₄ hmid hzero hgood
  · have hikpos : 0 < T.intersection i k :=
      (T.intersection_nonneg i k hik).lt_of_ne' hikjk.1
    have hkjPos : 0 < T.intersection k j := by
      simpa [T.intersection_symm] using (T.intersection_nonneg j k hjk).lt_of_ne' hikjk.2
    obtain ⟨r, s, t, u, _, _, hab₁, hab₂, hbc₁, hbc₂,
      hm₁, hm₂, hm₃, hm₄, hmid, hzero, hgood⟩ :=
      ordered_path_edge_data T hn i k j hik hij hjk.symm
        hi hk hj hikpos hkjPos
    obtain ⟨v, hv, hrange, hconfig⟩ := path_to_ordering T i k j
      hik hij hjk.symm hi hk hj r s t u hab₁ hab₂ hbc₁ hbc₂
      hm₁ hm₂ hm₃ hm₄ hmid hzero hgood
    exact ⟨v, hv, by rw [hrange, Set.pair_comm k j], hconfig⟩

end AlgebraicGeometry.NumericalType
