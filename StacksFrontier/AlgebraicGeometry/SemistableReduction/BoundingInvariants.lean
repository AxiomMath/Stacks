module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Contribution
public import Mathlib

/-!
# Bounding the invariants of a minimal numerical type

The genus of a minimal numerical type bounds every piece of its numerical data:
the multiplicities times the intersection numbers, the multiplicities times the
weights, the component genera, and the number of indices that are not minus-two
indices.

## Main results

* `AlgebraicGeometry.NumericalType.multiplicity_mul_intersection_le` and
  `AlgebraicGeometry.NumericalType.multiplicity_mul_weight_le`: bounds in terms
  of a neighbouring component.
* `AlgebraicGeometry.NumericalType.multiplicity_mul_abs_intersection_self_le`
  and `AlgebraicGeometry.NumericalType.multiplicity_mul_intersection_le_genus`:
  bounds by the genus.
* `AlgebraicGeometry.NumericalType.card_non_minus_two_indices_le`: at most
  `2(g - 1)` indices are not minus-two indices.
* `AlgebraicGeometry.NumericalType.componentGenus_lt_genus`.

## References

* [Stacks Project, Tag 0C9U](https://stacks.math.columbia.edu/tag/0C9U)
* [Stacks Project, Tag 0C9V](https://stacks.math.columbia.edu/tag/0C9V)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-! ### Bounds from a neighbouring component -/

private lemma diagonal_nonpos (T : NumericalType) (j : Fin T.componentCount) :
    T.intersection j j ≤ 0 := by
  by_contra h
  have hjj : 0 < T.intersection j j := lt_of_not_ge h
  have hnonneg : ∀ k, 0 ≤ T.intersection j k * T.multiplicity k := by
    intro k
    by_cases hkj : k = j
    · subst k
      exact mul_nonneg (le_of_lt hjj) (le_of_lt (T.multiplicity_pos j))
    · exact mul_nonneg (T.intersection_nonneg j k (Ne.symm hkj))
        (le_of_lt (T.multiplicity_pos k))
  have hpos : 0 < ∑ k, T.intersection j k * T.multiplicity k :=
    Finset.sum_pos' (fun k _ ↦ hnonneg k) ⟨j, Finset.mem_univ j,
      mul_pos hjj (T.multiplicity_pos j)⟩
  rw [T.intersection_mul_multiplicity j] at hpos
  exact lt_irrefl 0 hpos

private lemma intersection_summand_le (T : NumericalType)
    (i j : Fin T.componentCount) (hij : 0 < T.intersection i j) :
    T.multiplicity i * T.intersection i j ≤
      -(T.intersection j j * T.multiplicity j) := by
  have hij_ne : i ≠ j := by
    intro h
    subst i
    exact (not_lt_of_ge (diagonal_nonpos T j)) hij
  have hle : T.intersection j i * T.multiplicity i ≤
      ∑ k ∈ Finset.univ.erase j, T.intersection j k * T.multiplicity k :=
    Finset.single_le_sum (s := Finset.univ.erase j) (a := i) (by
      intro k hk
      exact mul_nonneg (T.intersection_nonneg j k (Finset.ne_of_mem_erase hk).symm)
        (le_of_lt (T.multiplicity_pos k))) (by simp [hij_ne])
  have hsum : (∑ k ∈ Finset.univ.erase j,
      T.intersection j k * T.multiplicity k) =
      -(T.intersection j j * T.multiplicity j) := by
    have h := T.intersection_mul_multiplicity j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h
    omega
  rw [← T.intersection_symm i j, mul_comm, hsum] at hle
  exact hle

/-- A positive intersection with a component is bounded, after multiplication by
its multiplicity, by the absolute diagonal contribution of the other component. -/
@[stacks 0C9U "intersection bound"]
public lemma multiplicity_mul_intersection_le (T : NumericalType)
    (i j : Fin T.componentCount) (hij : 0 < T.intersection i j) :
    T.multiplicity i * T.intersection i j ≤
      T.multiplicity j * |T.intersection j j| := by
  have h := intersection_summand_le T i j hij
  nlinarith [neg_le_abs (T.intersection j j), T.multiplicity_pos j]

/-- The multiplicity-weight product of a component meeting another component is
bounded by the latter component's absolute diagonal contribution. -/
@[stacks 0C9U "weight bound"]
public lemma multiplicity_mul_weight_le (T : NumericalType)
    (i j : Fin T.componentCount) (hij : 0 < T.intersection i j) :
    T.multiplicity i * T.weight i ≤
      T.multiplicity j * |T.intersection j j| := by
  obtain ⟨c, hc⟩ := T.weight_dvd_intersection i j
  have hc_pos : 0 < c := by
    rw [hc] at hij
    nlinarith [T.weight_pos i]
  have hweight : T.weight i ≤ T.intersection i j := by
    rw [hc]
    nlinarith [T.weight_pos i]
  calc
    T.multiplicity i * T.weight i ≤
        T.multiplicity i * T.intersection i j :=
      mul_le_mul_of_nonneg_left hweight (le_of_lt (T.multiplicity_pos i))
    _ ≤ T.multiplicity j * |T.intersection j j| :=
      multiplicity_mul_intersection_le T i j hij

/-! ### Diagonal intersection numbers -/

/-- At a non-minus-two index of a minimal numerical type of genus at least two,
the multiplicity times the absolute diagonal intersection is at most six times
the genus minus six. -/
@[stacks 0C9V "bound_diagonal"]
public lemma multiplicity_mul_abs_intersection_self_le
    (T : NumericalType) (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g)
    (hminimal : IsMinimal T) (hn : 1 < T.componentCount)
    (j : Fin T.componentCount) (hj : ¬ IsMinusTwoIndex T j) :
    T.multiplicity j * |T.intersection j j| ≤ 6 * g - 6 := by
  have hdiag : T.intersection j j < 0 :=
    intersection_self_neg_of_one_lt_componentCount T hn j
  have hcontrib := contribution_le_genus_sub_one
    T g hgenus hminimal hn j
  have hmul : 0 < T.multiplicity j := T.multiplicity_pos j
  have hweight : 0 < T.weight j := T.weight_pos j
  by_cases hgenusj : T.componentGenus j = 0
  · obtain ⟨z, hz⟩ := T.weight_dvd_intersection j j
    let k : ℤ := -z
    have hfactor : T.intersection j j = -(k * T.weight j) := by
      dsimp [k]
      rw [hz]
      ring
    have hkpos : 0 < k := by
      have : T.weight j * z < 0 := by rw [← hz]; exact hdiag
      dsimp [k]
      nlinarith
    have hk_ne_one : k ≠ 1 := fun hk =>
      hminimal ⟨j, hgenusj, by rw [hfactor, hk]; ring⟩
    have hk_ne_two : k ≠ 2 := fun hk =>
      hj ⟨hgenusj, by rw [hfactor, hk]; ring⟩
    have hkthree : 3 ≤ k := by omega
    have hboundQ :
        (T.multiplicity j : ℚ) * (T.weight j : ℚ) * (k : ℚ) ≤
          6 * ((g : ℚ) - 1) := by
      rw [hgenusj, hfactor] at hcontrib
      have hm : (0 : ℚ) ≤ T.multiplicity j := by exact_mod_cast (le_of_lt hmul)
      have hw : (0 : ℚ) ≤ T.weight j := by exact_mod_cast (le_of_lt hweight)
      have hk : (3 : ℚ) ≤ k := by exact_mod_cast hkthree
      have hx : 0 ≤ (T.multiplicity j : ℚ) * T.weight j * ((k : ℚ) - 3) :=
        mul_nonneg (mul_nonneg hm hw) (by linarith)
      norm_num at hcontrib ⊢
      nlinarith
    have hboundInt : T.multiplicity j * T.weight j * k ≤ 6 * g - 6 := by
      have h : T.multiplicity j * T.weight j * k ≤ 6 * (g - 1) := by
        exact_mod_cast hboundQ
      nlinarith
    rw [abs_of_neg hdiag, hfactor]
    nlinarith [hboundInt]
  · have hgenusj_pos : 0 < T.componentGenus j := by
      have hnonneg := T.componentGenus_nonneg j
      omega
    have hboundQ :
        (T.multiplicity j : ℚ) * (-(T.intersection j j : ℚ)) ≤
          6 * (g : ℚ) - 6 := by
      have hm : (0 : ℚ) ≤ T.multiplicity j := by exact_mod_cast (le_of_lt hmul)
      have hw : (0 : ℚ) ≤ T.weight j := by exact_mod_cast (le_of_lt hweight)
      have hgj : (1 : ℚ) ≤ T.componentGenus j := by exact_mod_cast hgenusj_pos
      have hx : 0 ≤ (T.multiplicity j : ℚ) * T.weight j * ((T.componentGenus j : ℚ) - 1) :=
        mul_nonneg (mul_nonneg hm hw) (by linarith)
      have hgq : (2 : ℚ) ≤ g := by exact_mod_cast hg
      nlinarith
    rw [abs_of_neg hdiag]
    exact_mod_cast hboundQ

/-! ### The number of non-minus-two indices -/

/-- A minimal numerical type with more than one component has at most twice its
genus minus two non-minus-two indices. -/
@[stacks 0C9V "bound_non_minus_two_indices"]
public lemma card_non_minus_two_indices_le
    (T : NumericalType) (hminimal : IsMinimal T) (hn : 1 < T.componentCount) :
    ((Finset.univ.filter (fun i : Fin T.componentCount => ¬ IsMinusTwoIndex T i)).card : ℤ) ≤
      2 * genus T - 2 := by
  let J := Finset.univ.filter (fun i : Fin T.componentCount => ¬ IsMinusTwoIndex T i)
  let c : Fin T.componentCount → ℚ := fun i =>
    (T.multiplicity i : ℚ) * ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
      (T.intersection i i : ℚ) / 2)
  have htotal : (∑ i, c i) = (genus T : ℚ) - 1 := by
    dsimp [c]; rw [cast_genus]; ring
  have hq : (J.card : ℚ) / 2 ≤ (genus T : ℚ) - 1 := calc
    (J.card : ℚ) / 2 = ∑ i ∈ J, (1 : ℚ) / 2 := by
      simp [J, div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ J, c i := Finset.sum_le_sum (by
      intro i hi
      exact one_half_le_contribution_of_not_isMinusTwoIndex
        T hminimal hn i (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i, c i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      (by intro i hi hnot
          exact contribution_nonneg_of_isMinimal T hminimal hn i)
    _ = (genus T : ℚ) - 1 := htotal
  have hq' : (J.card : ℚ) ≤ (2 : ℚ) * ((genus T : ℚ) - 1) := by linarith
  have hi : (J.card : ℤ) ≤ 2 * (genus T - 1) := by exact_mod_cast hq'
  simpa [J, mul_sub] using hi

/-! ### Intersections with a non-minus-two component -/

/-- The multiplicity-weighted intersection with a non-minus-two component of a
minimal numerical type is at most six times its genus minus six. -/
@[stacks 0C9V "bound_off_diagonal"]
public lemma multiplicity_mul_intersection_le_genus
    (T : NumericalType) (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g)
    (hminimal : IsMinimal T) (hn : 1 < T.componentCount)
    (i j : Fin T.componentCount) (hj : ¬ IsMinusTwoIndex T j) :
    T.multiplicity i * T.intersection i j ≤ 6 * g - 6 := by
  by_cases hij : 0 < T.intersection i j
  · exact (multiplicity_mul_intersection_le T i j hij).trans
      (multiplicity_mul_abs_intersection_self_le
        T g hg hgenus hminimal hn j hj)
  · exact (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (T.multiplicity_pos i))
      (le_of_not_gt hij)).trans (by omega)

/-! ### Component genera -/

/-- A non-minus-two component of a minimal numerical type of genus at least two
has genus strictly less than that of the numerical type. -/
@[stacks 0C9V "component_genus_lt"]
public lemma componentGenus_lt_genus
    (T : NumericalType) (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g)
    (hminimal : IsMinimal T) (hn : 1 < T.componentCount)
    (j : Fin T.componentCount) (hj : ¬ IsMinusTwoIndex T j) :
    T.componentGenus j < g := by
  have hm : (1 : ℚ) ≤ T.multiplicity j := by
    exact_mod_cast (show 1 ≤ T.multiplicity j by
      have := T.multiplicity_pos j
      omega)
  have hw : (1 : ℚ) ≤ T.weight j := by
    exact_mod_cast (show 1 ≤ T.weight j by
      have := T.weight_pos j
      omega)
  have hd : (T.intersection j j : ℚ) < 0 := by exact_mod_cast
    intersection_self_neg_of_one_lt_componentCount T hn j
  have hc := contribution_le_genus_sub_one T g hgenus hminimal hn j
  by_contra hnot
  have hjg : (g : ℚ) ≤ T.componentGenus j := by exact_mod_cast (show g ≤ T.componentGenus j by
    omega)
  have hmw : (1 : ℚ) ≤ (T.multiplicity j : ℚ) * T.weight j := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hw)]
  have hgq : (2 : ℚ) ≤ g := by exact_mod_cast hg
  have hp := mul_nonneg (sub_nonneg.mpr hmw) (show (0 : ℚ) ≤ T.componentGenus j - 1 by linarith)
  have hmd := mul_neg_of_pos_of_neg (show (0 : ℚ) < T.multiplicity j by linarith) hd
  nlinarith

end AlgebraicGeometry.NumericalType
