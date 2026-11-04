module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Fork
public import StacksCore.Tactic.StacksAttribute

/-!
# Proper subgraphs of type E7

Seven distinct minus-two indices of a numerical type whose incidence graph is
the Dynkin diagram `E₇` — a six-vertex chain with a leaf attached to the fourth
vertex — have a uniquely prescribed intersection pattern and a common weight,
and their multiplicities satisfy the seven Cartan inequalities coming from the
remaining components.

The weight and most of the intersection numbers come from applying the fork
classification along the long arm and the `D₅` classification along the short
arm. What those two applications leave open is whether the first two vertices
of the chain meet the fifth; both possibilities are ruled out by summing the
seven row inequalities, which forces a strict inequality at the branch vertex.

## Main results

* `AlgebraicGeometry.NumericalType.e7_subgraph_classification`: the restricted
  intersection matrix.
* `AlgebraicGeometry.NumericalType.e7_subgraph_weight_eq`: the common weight.
* The seven `AlgebraicGeometry.NumericalType.e7_subgraph_multiplicity_le_*`
  lemmas: the multiplicity inequalities at the respective vertices.

## Implementation notes

The seven distinct indices are packaged as an embedding from `Fin 7`, in the
order used by the source: `i 0, …, i 5` is the chain and `i 6` is the leaf
attached to `i 3`. Equality with an explicit matrix states every intersection
number at once, including the zero entries not mentioned in the incidence
hypotheses.

## References

* [Stacks Project, Tag 0C8J](https://stacks.math.columbia.edu/tag/0C8J)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

open Matrix

variable (T : NumericalType) (hn : 7 < T.componentCount)
  (i : Fin 7 ↪ Fin T.componentCount)
  (hminus : ∀ k, IsMinusTwoIndex T (i k))
  (hedges : T.intersection (i 0) (i 1) ≠ 0 ∧
    T.intersection (i 1) (i 2) ≠ 0 ∧
    T.intersection (i 2) (i 3) ≠ 0 ∧
    T.intersection (i 3) (i 4) ≠ 0 ∧
    T.intersection (i 4) (i 5) ≠ 0 ∧
    T.intersection (i 3) (i 6) ≠ 0)

include hn hminus hedges

omit T hn i hminus hedges in
/-- The six vertices of `E₇` forming its `D₆` subdiagram, in fork order. -/
private def e7_d6Index : Fin 6 → Fin 7 := ![0, 1, 2, 3, 4, 6]

omit T hn i hminus hedges in
private theorem e7_d6Index_injective : Function.Injective e7_d6Index := by
  intro a b hab
  apply Fin.ext
  fin_cases a <;> fin_cases b <;> simp [e7_d6Index] at hab ⊢

omit T hn i hminus hedges in
/-- The five vertices of `E₇` forming the `D₅` subdiagram at the other end. -/
private def e7_d5Index : Fin 5 → Fin 7 := ![5, 4, 3, 2, 6]

omit T hn i hminus hedges in
private theorem e7_d5Index_injective : Function.Injective e7_d5Index := by
  intro a b hab
  apply Fin.ext
  fin_cases a <;> fin_cases b <;> simp [e7_d5Index] at hab ⊢

/-- The common weight and the intersection numbers of an `E₇` configuration
that are determined by its two fork subdiagrams. -/
private theorem e7_fork_data :
    ∃ w : ℤ, (∀ j : Fin 7, T.weight (i j) = w) ∧
      (T.intersection (i 0) (i 1) = w) ∧
      (T.intersection (i 1) (i 2) = w) ∧
      (T.intersection (i 2) (i 3) = w) ∧
      (T.intersection (i 3) (i 4) = w) ∧
      (T.intersection (i 4) (i 5) = w) ∧
      (T.intersection (i 3) (i 6) = w) ∧
      (∀ a b : Fin 6, b < a →
        ¬ (a.val = b.val + 1 ∧ b.val < 4) →
        ¬ (a.val = 5 ∧ b.val = 3) →
        T.intersection (i (e7_d6Index a)) (i (e7_d6Index b)) = 0) ∧
      T.intersection (i 5) (i 3) = 0 ∧
      T.intersection (i 5) (i 2) = 0 ∧
      T.intersection (i 5) (i 6) = 0 := by
  let d6 : Fin 6 → Fin T.componentCount := fun j => i (e7_d6Index j)
  have hd6chain : ∀ j : Fin 4,
      T.intersection (d6 ⟨j.val, by omega⟩) (d6 ⟨j.val + 1, by omega⟩) ≠ 0 := by
    intro j
    fin_cases j
    · simpa [d6, e7_d6Index] using hedges.1
    · simpa [d6, e7_d6Index] using hedges.2.1
    · simpa [d6, e7_d6Index] using hedges.2.2.1
    · simpa [d6, e7_d6Index] using hedges.2.2.2.1
  have hd6branch : T.intersection (d6 3) (d6 5) ≠ 0 := by
    simpa [d6, e7_d6Index] using hedges.2.2.2.2.2
  obtain ⟨w, hw, he, hb, hz⟩ :=
    eq_fork_of_isMinusTwoIndex T 5 (by omega) (by omega) d6
      (i.injective.comp e7_d6Index_injective) (fun j => hminus (e7_d6Index j))
      hd6chain hd6branch
  let d5 : Fin 5 ↪ Fin T.componentCount :=
    ⟨fun j => i (e7_d5Index j), i.injective.comp e7_d5Index_injective⟩
  have hd5_01 : T.intersection (d5 0) (d5 1) ≠ 0 := by
    rw [T.intersection_symm]; exact hedges.2.2.2.2.1
  have hd5_12 : T.intersection (d5 1) (d5 2) ≠ 0 := by
    rw [T.intersection_symm]; exact hedges.2.2.2.1
  have hd5_23 : T.intersection (d5 2) (d5 3) ≠ 0 := by
    rw [T.intersection_symm]; exact hedges.2.2.1
  have hd5_24 : T.intersection (d5 2) (d5 4) ≠ 0 := by
    simpa [d5, e7_d5Index] using hedges.2.2.2.2.2
  obtain ⟨w', hw', hm⟩ :=
    exists_weight_eq_d5_of_isMinusTwoIndex T (by omega)
      d5 (fun j => hminus (e7_d5Index j)) hd5_01 hd5_12 hd5_23 hd5_24
  have hwEq : w = w' := by
    have h1 := hw 4
    have h2 := congrFun hw' (1 : Fin 5)
    simpa [d6, e7_d6Index, d5, e7_d5Index] using h1.symm.trans h2
  subst w'
  refine ⟨w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · simpa [d6, e7_d6Index] using hw 0
    · simpa [d6, e7_d6Index] using hw 1
    · simpa [d6, e7_d6Index] using hw 2
    · simpa [d6, e7_d6Index] using hw 3
    · simpa [d6, e7_d6Index] using hw 4
    · simpa [d5, e7_d5Index] using congrFun hw' (0 : Fin 5)
    · simpa [d6, e7_d6Index] using hw 5
  · simpa [d6, e7_d6Index] using he 0
  · simpa [d6, e7_d6Index] using he 1
  · simpa [d6, e7_d6Index] using he 2
  · simpa [d6, e7_d6Index] using he 3
  · have h := congrFun (congrFun hm (0 : Fin 5)) (1 : Fin 5)
    have h' : T.intersection (i 5) (i 4) = w := by
      simpa [d5, e7_d5Index] using h
    rw [T.intersection_symm]
    exact h'
  · simpa [d6, e7_d6Index] using hb
  · exact hz
  · simpa [d5, e7_d5Index] using congrFun (congrFun hm (0 : Fin 5)) (2 : Fin 5)
  · simpa [d5, e7_d5Index] using congrFun (congrFun hm (0 : Fin 5)) (3 : Fin 5)
  · simpa [d5, e7_d5Index] using congrFun (congrFun hm (0 : Fin 5)) (4 : Fin 5)

omit hn i hminus hedges in
/-- At a minus-two index `x`, the multiplicities of any set of components each
meeting `x` in at least the weight of `x` sum to at most twice the
multiplicity of `x`. -/
private theorem e7_multiplicity_neighbors
    (x : Fin T.componentCount) (S : Finset (Fin T.componentCount))
    (hminusx : IsMinusTwoIndex T x) (hnot : x ∉ S)
    (hedge : ∀ y ∈ S, T.weight x ≤ T.intersection x y) :
    (∑ y ∈ S, T.multiplicity y) ≤ 2 * T.multiplicity x := by
  let f : Fin T.componentCount → ℤ :=
    fun y => T.intersection x y * T.multiplicity y
  have hrow : (∑ y, f y) = 0 := by
    simpa [f] using T.intersection_mul_multiplicity x
  have hdiag : T.intersection x x = -2 * T.weight x := hminusx.2
  have hsplit : (∑ y ∈ Finset.univ.erase x, f y) + f x = ∑ y, f y :=
    Finset.sum_erase_add (s := Finset.univ) (f := f) (a := x) (Finset.mem_univ x)
  have hrest : (∑ y ∈ Finset.univ.erase x, f y) =
      2 * T.weight x * T.multiplicity x := by
    rw [hrow] at hsplit
    dsimp [f] at hsplit ⊢
    rw [hdiag] at hsplit
    linarith
  have hsubset : S ⊆ Finset.univ.erase x := by
    intro y hy
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    exact hnot (heq ▸ hy)
  have hnonneg : ∀ y ∈ Finset.univ.erase x, 0 ≤ f y := by
    intro y hy
    have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
    exact mul_nonneg (T.intersection_nonneg x y (Ne.symm hyx))
      (le_of_lt (T.multiplicity_pos y))
  have hsumle : (∑ y ∈ S, f y) ≤ ∑ y ∈ Finset.univ.erase x, f y :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun y hy _ => hnonneg y hy)
  have hselected : T.weight x * (∑ y ∈ S, T.multiplicity y) ≤
      ∑ y ∈ S, f y := by
    calc
      T.weight x * (∑ y ∈ S, T.multiplicity y) =
          ∑ y ∈ S, T.weight x * T.multiplicity y := by rw [Finset.mul_sum]
      _ ≤ ∑ y ∈ S, f y :=
        Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_right (hedge y hy)
          (le_of_lt (T.multiplicity_pos y))
  have hcombined := hselected.trans hsumle
  rw [hrest, show 2 * T.weight x * T.multiplicity x =
    T.weight x * (2 * T.multiplicity x) from by ring] at hcombined
  exact le_of_mul_le_mul_left hcombined (T.weight_pos x)

omit hn i hminus hedges in
/-- A nonzero intersection number is at least the weight of its row, since the
weight divides it. -/
private theorem e7_intersection_ge_weight
    (x y : Fin T.componentCount) (hxy : x ≠ y)
    (hne : T.intersection x y ≠ 0) :
    T.weight x ≤ T.intersection x y :=
  Int.le_of_dvd (lt_of_le_of_ne (T.intersection_nonneg x y hxy) (Ne.symm hne))
    (T.weight_dvd_intersection x y)

omit hn hedges in
/-- `e7_multiplicity_neighbors` transported to a set of positions in `Fin 7`, for
edges recorded as `w ≤ intersection` in either order. -/
private theorem e7_row_bound (w : ℤ) (hw : ∀ j, T.weight (i j) = w)
    (x : Fin 7) (S : Finset (Fin 7)) (hnot : x ∉ S)
    (hedge : ∀ y ∈ S, w ≤ T.intersection (i x) (i y) ∨ w ≤ T.intersection (i y) (i x)) :
    (∑ y ∈ S, T.multiplicity (i y)) ≤ 2 * T.multiplicity (i x) := by
  have h := e7_multiplicity_neighbors T (i x) (S.map i)
    (hminus x) (by
      intro hx
      obtain ⟨y, hy, hiy⟩ := Finset.mem_map.mp hx
      exact hnot (i.injective hiy ▸ hy))
    (by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
      rw [hw x]
      rcases hedge z hz with h | h
      · exact h
      · rwa [T.intersection_symm])
  simpa using h

/-- The row inequalities at the four vertices `2, 3, 4, 6` of an `E₇` configuration. -/
private theorem e7_inner_bounds :
    T.multiplicity (i 1) + T.multiplicity (i 3) ≤ 2 * T.multiplicity (i 2) ∧
    T.multiplicity (i 2) + T.multiplicity (i 4) + T.multiplicity (i 6) ≤
      2 * T.multiplicity (i 3) ∧
    T.multiplicity (i 3) + T.multiplicity (i 5) ≤ 2 * T.multiplicity (i 4) ∧
    T.multiplicity (i 3) ≤ 2 * T.multiplicity (i 6) := by
  obtain ⟨w, hw, -, h12, h23, h34, h45, h36, -⟩ := e7_fork_data T hn i hminus hedges
  have r2 := e7_row_bound T i hminus w hw 2 {1, 3} (by simp) (by simp [h12.ge, h23.ge])
  have r3 := e7_row_bound T i hminus w hw 3 {2, 4, 6} (by simp)
    (by simp [h23.ge, h34.ge, h36.ge])
  have r4 := e7_row_bound T i hminus w hw 4 {3, 5} (by simp) (by simp [h34.ge, h45.ge])
  have r6 := e7_row_bound T i hminus w hw 6 {3} (by simp) (by simp [h36.ge])
  exact ⟨by simpa using r2, by simpa [add_assoc] using r3, by simpa using r4,
    by simpa using r6⟩

/-- Neither of the first two vertices of the chain meets the fifth. -/
private theorem e7_cross_intersections_zero :
    T.intersection (i 0) (i 5) = 0 ∧
      T.intersection (i 1) (i 5) = 0 := by
  obtain ⟨w, hw, h01, h12, -, -, h45, -⟩ := e7_fork_data T hn i hminus hedges
  obtain ⟨r2, r3, r4, r6⟩ := e7_inner_bounds T hn i hminus hedges
  have hge (a : Fin 7) (ha : a ≠ 5) (h : T.intersection (i a) (i 5) ≠ 0) :
      w ≤ T.intersection (i a) (i 5) :=
    (hw a).symm.trans_le (e7_intersection_ge_weight T _ _ (i.injective.ne ha) h)
  have hm3 := T.multiplicity_pos (i 3)
  rcases eq_or_ne (T.intersection (i 0) (i 5)) 0 with h05 | h05
  · rcases eq_or_ne (T.intersection (i 1) (i 5)) 0 with h15 | h15
    · exact ⟨h05, h15⟩
    · have h15ge := hge 1 (by decide) h15
      have r0 := e7_row_bound T i hminus w hw 0 {1} (by simp) (by simp [h01.ge])
      have r1 := e7_row_bound T i hminus w hw 1 {0, 2, 5} (by simp)
        (by simp [h01.ge, h12.ge, h15ge])
      have r5 := e7_row_bound T i hminus w hw 5 {1, 4} (by simp) (by simp [h15ge, h45.ge])
      simp at r0 r1 r5
      linarith
  · have h05ge := hge 0 (by decide) h05
    have r0 := e7_row_bound T i hminus w hw 0 {1, 5} (by simp) (by simp [h01.ge, h05ge])
    have r1 := e7_row_bound T i hminus w hw 1 {0, 2} (by simp) (by simp [h01.ge, h12.ge])
    have r5 := e7_row_bound T i hminus w hw 5 {0, 4} (by simp) (by simp [h05ge, h45.ge])
    simp at r0 r1 r5
    linarith

/-- The seven row inequalities of an `E₇` configuration. -/
private theorem e7_all_multiplicity_bounds :
    T.multiplicity (i 1) ≤ 2 * T.multiplicity (i 0) ∧
    T.multiplicity (i 0) + T.multiplicity (i 2) ≤ 2 * T.multiplicity (i 1) ∧
    T.multiplicity (i 1) + T.multiplicity (i 3) ≤ 2 * T.multiplicity (i 2) ∧
    T.multiplicity (i 2) + T.multiplicity (i 4) + T.multiplicity (i 6) ≤
      2 * T.multiplicity (i 3) ∧
    T.multiplicity (i 3) + T.multiplicity (i 5) ≤ 2 * T.multiplicity (i 4) ∧
    T.multiplicity (i 4) ≤ 2 * T.multiplicity (i 5) ∧
    T.multiplicity (i 3) ≤ 2 * T.multiplicity (i 6) := by
  obtain ⟨w, hw, h01, h12, -, -, h45, -⟩ := e7_fork_data T hn i hminus hedges
  obtain ⟨r2, r3, r4, r6⟩ := e7_inner_bounds T hn i hminus hedges
  have r0 := e7_row_bound T i hminus w hw 0 {1} (by simp) (by simp [h01.ge])
  have r1 := e7_row_bound T i hminus w hw 1 {0, 2} (by simp) (by simp [h01.ge, h12.ge])
  have r5 := e7_row_bound T i hminus w hw 5 {4} (by simp) (by simp [h45.ge])
  exact ⟨by simpa using r0, by simpa using r1, r2, r3, r4, by simpa using r5, r6⟩

/-- **Stacks Project, Tag 0C8J.** The restricted intersection matrix of a
proper `E₇` subgraph. -/
@[stacks 0C8J "intersection matrix"]
public theorem e7_subgraph_classification :
    (fun p q => T.intersection (i p) (i q)) =
      !![(-2 * T.weight (i 0)), T.weight (i 0), 0, 0, 0, 0, 0;
         T.weight (i 0), (-2 * T.weight (i 0)), T.weight (i 0), 0, 0, 0, 0;
         0, T.weight (i 0), (-2 * T.weight (i 0)), T.weight (i 0), 0, 0, 0;
         0, 0, T.weight (i 0), (-2 * T.weight (i 0)), T.weight (i 0), 0,
           T.weight (i 0);
         0, 0, 0, T.weight (i 0), (-2 * T.weight (i 0)), T.weight (i 0), 0;
         0, 0, 0, 0, T.weight (i 0), (-2 * T.weight (i 0)), 0;
         0, 0, 0, T.weight (i 0), 0, 0, (-2 * T.weight (i 0))] := by
  obtain ⟨w, hw, h01, h12, h23, h34, h45, h36, hzero,
      h53, h52, h56⟩ := e7_fork_data T hn i hminus hedges
  obtain ⟨h05, h15⟩ := e7_cross_intersections_zero T hn i hminus hedges
  have h10 : T.intersection (i 1) (i 0) = w := by rw [T.intersection_symm, h01]
  have h35 : T.intersection (i 3) (i 5) = 0 := by rw [T.intersection_symm, h53]
  have h25 : T.intersection (i 2) (i 5) = 0 := by rw [T.intersection_symm, h52]
  have z (b a : Fin 6) (h : b < a ∧ ¬ (a.val = b.val + 1 ∧ b.val < 4) ∧
      ¬ (a.val = 5 ∧ b.val = 3) := by decide) :
      T.intersection (i (e7_d6Index b)) (i (e7_d6Index a)) = 0 := by
    rw [T.intersection_symm]; exact hzero a b h.1 h.2.1 h.2.2
  have z02 : T.intersection (i 0) (i 2) = 0 := z 0 2
  have z03 : T.intersection (i 0) (i 3) = 0 := z 0 3
  have z04 : T.intersection (i 0) (i 4) = 0 := z 0 4
  have z06 : T.intersection (i 0) (i 6) = 0 := z 0 5
  have z13 : T.intersection (i 1) (i 3) = 0 := z 1 3
  have z14 : T.intersection (i 1) (i 4) = 0 := z 1 4
  have z16 : T.intersection (i 1) (i 6) = 0 := z 1 5
  have z24 : T.intersection (i 2) (i 4) = 0 := z 2 4
  have z26 : T.intersection (i 2) (i 6) = 0 := z 2 5
  have z46 : T.intersection (i 4) (i 6) = 0 := z 4 5
  have hdiag (j : Fin 7) : T.intersection (i j) (i j) = -2 * w := by
    rw [(hminus j).2, hw j]
  rw [hw 0]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [T.intersection_symm, hdiag, h10, h12, h23, h34, h45, h36, h05, h15,
      h35, h25, h56, z02, z03, z04, z06, z13, z14, z16, z24, z26, z46]

/-- **Stacks Project, Tag 0C8J.** The seven weights of a proper `E₇` subgraph
agree. -/
@[stacks 0C8J "common weight"]
public theorem e7_subgraph_weight_eq :
    (fun p => T.weight (i p)) =
      ![T.weight (i 0), T.weight (i 0), T.weight (i 0), T.weight (i 0),
        T.weight (i 0), T.weight (i 0), T.weight (i 0)] := by
  obtain ⟨w, hw, -⟩ := e7_fork_data T hn i hminus hedges
  funext p
  fin_cases p <;> simp [hw]

/-- **Stacks Project, Tag 0C8J.** The multiplicity inequality at the first
vertex. -/
@[stacks 0C8J "first multiplicity inequality"]
public theorem e7_subgraph_multiplicity_le_zero :
    T.multiplicity (i 1) ≤ 2 * T.multiplicity (i 0) :=
  (e7_all_multiplicity_bounds T hn i hminus hedges).1

/-- **Stacks Project, Tag 0C8J.** The multiplicity inequality at the second
vertex. -/
@[stacks 0C8J "second multiplicity inequality"]
public theorem e7_subgraph_multiplicity_le_one :
    T.multiplicity (i 0) + T.multiplicity (i 2) ≤ 2 * T.multiplicity (i 1) :=
  (e7_all_multiplicity_bounds T hn i hminus hedges).2.1

/-- **Stacks Project, Tag 0C8J.** The multiplicity inequality at the third
vertex. -/
@[stacks 0C8J "third multiplicity inequality"]
public theorem e7_subgraph_multiplicity_le_two :
    T.multiplicity (i 1) + T.multiplicity (i 3) ≤ 2 * T.multiplicity (i 2) :=
  (e7_all_multiplicity_bounds T hn i hminus hedges).2.2.1

/-- **Stacks Project, Tag 0C8J.** The multiplicity inequality at the branching
vertex. -/
@[stacks 0C8J "fourth multiplicity inequality"]
public theorem e7_subgraph_multiplicity_le_three :
    T.multiplicity (i 2) + T.multiplicity (i 4) + T.multiplicity (i 6) ≤
      2 * T.multiplicity (i 3) :=
  (e7_all_multiplicity_bounds T hn i hminus hedges).2.2.2.1

/-- **Stacks Project, Tag 0C8J.** The multiplicity inequality at the fifth
vertex. -/
@[stacks 0C8J "fifth multiplicity inequality"]
public theorem e7_subgraph_multiplicity_le_four :
    T.multiplicity (i 3) + T.multiplicity (i 5) ≤ 2 * T.multiplicity (i 4) :=
  (e7_all_multiplicity_bounds T hn i hminus hedges).2.2.2.2.1

/-- **Stacks Project, Tag 0C8J.** The multiplicity inequality at the sixth
vertex. -/
@[stacks 0C8J "sixth multiplicity inequality"]
public theorem e7_subgraph_multiplicity_le_five :
    T.multiplicity (i 4) ≤ 2 * T.multiplicity (i 5) :=
  (e7_all_multiplicity_bounds T hn i hminus hedges).2.2.2.2.2.1

/-- **Stacks Project, Tag 0C8J.** The multiplicity inequality at the seventh
vertex. -/
@[stacks 0C8J "seventh multiplicity inequality"]
public theorem e7_subgraph_multiplicity_le_six :
    T.multiplicity (i 3) ≤ 2 * T.multiplicity (i 6) :=
  (e7_all_multiplicity_bounds T hn i hminus hedges).2.2.2.2.2.2

end AlgebraicGeometry.NumericalType
