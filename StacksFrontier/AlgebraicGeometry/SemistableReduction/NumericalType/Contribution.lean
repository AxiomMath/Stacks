module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import Mathlib
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# Contributions of components to the genus

The genus of a numerical type is `1` plus the sum over components of the
contribution `mᵢ (wᵢ (gᵢ - 1) - aᵢᵢ / 2)`. This file collects what the sign and
size of a single contribution force about its component, and bounds every
contribution of a minimal numerical type.

## Main results

* `NumericalType.intersection_self_neg_of_one_lt_componentCount`: diagonal intersection numbers
  are negative once there is more than one component.
* `NumericalType.componentGenus_eq_zero_of_contribution_neg` and
  `NumericalType.intersection_self_eq_neg_weight_of_contribution_neg`: a negative contribution
  forces a minus-one index.
* `NumericalType.componentGenus_eq_zero_of_contribution_eq_zero` and
  `NumericalType.intersection_self_eq_neg_two_mul_weight_of_contribution_eq_zero`: a zero
  contribution forces a minus-two index.
* `NumericalType.contribution_nonneg_of_isMinimal`,
  `NumericalType.contribution_eq_zero_of_isMinusTwoIndex`,
  `NumericalType.one_half_le_contribution_of_not_isMinusTwoIndex` and
  `NumericalType.contribution_le_genus_sub_one`: the contributions of a minimal numerical type
  are nonnegative, vanish exactly on the minus-two indices, and are bounded by the genus minus
  one.

## Implementation notes

Contributions are written explicitly in `ℚ`, as in the rational genus formula.
Each assertion carries only the hypotheses it uses; in particular the upper
bound does not need the non-minus-two assumption, so it is stated for every
index.

## References

* [Stacks Project, Tag 0C74](https://stacks.math.columbia.edu/tag/0C74)
* [Stacks Project, Tag 0C75](https://stacks.math.columbia.edu/tag/0C75)
* [Stacks Project, Tag 0C7D](https://stacks.math.columbia.edu/tag/0C7D)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-! ### Negative diagonal entries -/

/-- Every diagonal intersection number of a numerical type with more than one
component is strictly negative. -/
@[stacks 0C74]
public lemma intersection_self_neg_of_one_lt_componentCount
    (T : NumericalType) (hcomponentCount : 1 < T.componentCount)
    (i : Fin T.componentCount) :
    T.intersection i i < 0 := by
  let f : Fin T.componentCount → ℤ := fun j => T.intersection i j * T.multiplicity j
  have hrow : f i + ∑ j ∈ Finset.univ.erase i, f j = 0 := by
    simpa [f, Finset.add_sum_erase] using T.intersection_mul_multiplicity i
  have hnonneg : ∀ j ∈ Finset.univ.erase i, 0 ≤ f j := fun j hj =>
    mul_nonneg (T.intersection_nonneg i j (Finset.mem_erase.mp hj).1.symm)
      (T.multiplicity_pos j).le
  have hdiag : T.intersection i i ≤ 0 := by
    have : f i ≤ 0 := by
      have := Finset.sum_nonneg hnonneg
      omega
    exact le_of_mul_le_mul_right (by simpa [f] using this) (T.multiplicity_pos i)
  have hne : T.intersection i i ≠ 0 := by
    intro hz
    have hzero : ∀ j ∈ Finset.univ.erase i, f j = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp
      simpa [f, hz] using hrow
    have : Nontrivial (Fin T.componentCount) :=
      Fin.nontrivial_iff_two_le.mpr (by omega)
    refine T.connected ⟨{i}, ⟨i, rfl⟩, Set.singleton_ne_univ i, fun j hj k hk => ?_⟩
    obtain rfl : j = i := hj
    exact (mul_eq_zero.mp (hzero k (by simpa using hk))).resolve_right (T.multiplicity_pos k).ne'
  omega

/-! ### Negative contributions -/

/-- The bracket of a negative contribution is negative. -/
private lemma contribution_bracket_neg
    (T : NumericalType) (i : Fin T.componentCount)
    (hi : (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
        (T.intersection i i : ℚ) / 2) < 0) :
    (T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
      (T.intersection i i : ℚ) / 2 < 0 :=
  neg_of_mul_neg_right hi (mod_cast (T.multiplicity_pos i).le)

/-- With more than one component, a diagonal intersection number is a negative multiple of the
weight. -/
private lemma exists_neg_int_intersection_self_eq
    (T : NumericalType) (hn : 1 < T.componentCount) (i : Fin T.componentCount) :
    ∃ k : ℤ, k < 0 ∧ T.intersection i i = T.weight i * k := by
  obtain ⟨k, hk⟩ := T.weight_dvd_intersection i i
  exact ⟨k, neg_of_mul_neg_right (hk ▸ intersection_self_neg_of_one_lt_componentCount T hn i)
    (T.weight_pos i).le, hk⟩

/-- A component with negative contribution to the genus has component genus zero. -/
@[stacks 0C75 "component genus"]
public lemma componentGenus_eq_zero_of_contribution_neg
    (T : NumericalType) (hn : 1 < T.componentCount) (i : Fin T.componentCount)
    (hi : (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
        (T.intersection i i : ℚ) / 2) < 0) :
    T.componentGenus i = 0 := by
  have hb := contribution_bracket_neg T i hi
  by_contra hne
  have hg : (1 : ℚ) ≤ T.componentGenus i := by
    have := T.componentGenus_nonneg i
    exact_mod_cast (show 1 ≤ T.componentGenus i by omega)
  have hw : (0 : ℚ) < T.weight i := by exact_mod_cast T.weight_pos i
  have ha : (T.intersection i i : ℚ) < 0 := by
    exact_mod_cast intersection_self_neg_of_one_lt_componentCount T hn i
  nlinarith

/-- The diagonal intersection number of a component with negative contribution to
the genus is the negative of its weight. -/
@[stacks 0C75 "diagonal intersection"]
public lemma intersection_self_eq_neg_weight_of_contribution_neg
    (T : NumericalType) (hn : 1 < T.componentCount) (i : Fin T.componentCount)
    (hi : (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
        (T.intersection i i : ℚ) / 2) < 0) :
    T.intersection i i = -T.weight i := by
  have hg := componentGenus_eq_zero_of_contribution_neg T hn i hi
  have hw : (0 : ℚ) < T.weight i := by exact_mod_cast T.weight_pos i
  obtain ⟨k, hkneg, hk⟩ := exists_neg_int_intersection_self_eq T hn i
  have hb := contribution_bracket_neg T i hi
  have hkgt : (-2 : ℚ) < k := by
    rw [hg, hk] at hb
    push_cast at hb
    nlinarith
  have : (-2 : ℤ) < k := by exact_mod_cast hkgt
  obtain rfl : k = -1 := by omega
  rw [hk]
  ring

/-! ### Zero contributions -/

private lemma intersection_eq_two_mul_weight_mul_genus_sub_one
    (T : NumericalType) (i : Fin T.componentCount)
    (hcontribution : (T.weight i : ℚ) *
      ((T.componentGenus i : ℚ) - 1) - (T.intersection i i : ℚ) / 2 = 0) :
    T.intersection i i = 2 * T.weight i * (T.componentGenus i - 1) := by
  have hq : (2 : ℚ) * (T.weight i : ℚ) *
      ((T.componentGenus i : ℚ) - 1) = (T.intersection i i : ℚ) := by
    linarith
  exact_mod_cast hq.symm

private lemma contribution_bracket_eq_zero
    (T : NumericalType) (i : Fin T.componentCount)
    (hcontribution : (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
        (T.intersection i i : ℚ) / 2) = 0) :
    (T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
      (T.intersection i i : ℚ) / 2 = 0 :=
  (mul_eq_zero.mp hcontribution).resolve_left (mod_cast (T.multiplicity_pos i).ne')

/-- A component of zero contribution in a numerical type with more than one
component has component genus zero. -/
@[stacks 0C7D "component genus"]
public lemma componentGenus_eq_zero_of_contribution_eq_zero
    (T : NumericalType) (hn : 1 < T.componentCount) (i : Fin T.componentCount)
    (hi : (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
        (T.intersection i i : ℚ) / 2) = 0) :
    T.componentGenus i = 0 := by
  have hdiag := intersection_eq_two_mul_weight_mul_genus_sub_one T i
    (contribution_bracket_eq_zero T i hi)
  have hnegative := intersection_self_neg_of_one_lt_componentCount T hn i
  by_contra hne
  have hsub : 0 ≤ T.componentGenus i - 1 := by
    have := T.componentGenus_nonneg i
    omega
  nlinarith [mul_nonneg (le_of_lt (T.weight_pos i)) hsub,
    T.componentGenus_nonneg i]

/-- A component of zero contribution in a numerical type with more than one
component has diagonal intersection number equal to minus twice its weight. -/
@[stacks 0C7D "diagonal intersection"]
public lemma intersection_self_eq_neg_two_mul_weight_of_contribution_eq_zero
    (T : NumericalType) (hn : 1 < T.componentCount) (i : Fin T.componentCount)
    (hi : (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
        (T.intersection i i : ℚ) / 2) = 0) :
    T.intersection i i = -2 * T.weight i := by
  rw [intersection_eq_two_mul_weight_mul_genus_sub_one T i
    (contribution_bracket_eq_zero T i hi), componentGenus_eq_zero_of_contribution_eq_zero T hn i hi]
  ring

/-! ### Bounds on the contributions of a minimal numerical type -/

private lemma contribution_numerator_bounds (T : NumericalType)
    (hminimal : IsMinimal T) (hn : 1 < T.componentCount)
    (i : Fin T.componentCount) :
    0 ≤ T.multiplicity i *
        (2 * T.weight i * (T.componentGenus i - 1) - T.intersection i i) ∧
      (¬ IsMinusTwoIndex T i →
        1 ≤ T.multiplicity i *
          (2 * T.weight i * (T.componentGenus i - 1) - T.intersection i i)) := by
  have ha := intersection_self_neg_of_one_lt_componentCount T hn i
  have hm := T.multiplicity_pos i
  have hw := T.weight_pos i
  have hg := T.componentGenus_nonneg i
  by_cases hgi : T.componentGenus i = 0
  · obtain ⟨k, hkneg, hk⟩ := exists_neg_int_intersection_self_eq T hn i
    have hkone : k ≠ -1 := fun hkeq => hminimal ⟨i, hgi, by rw [hk, hkeq]; ring⟩
    rw [hgi, hk, show 2 * T.weight i * (0 - 1) - T.weight i * k = T.weight i * (-2 - k) by ring]
    refine ⟨mul_nonneg hm.le (mul_nonneg hw.le (by omega)), fun hnot => ?_⟩
    have hktwo : k ≠ -2 := fun hkeq => hnot ⟨hgi, by rw [hk, hkeq]; ring⟩
    have := mul_pos hm (mul_pos hw (show 0 < -2 - k by omega))
    omega
  · have hterm : 0 ≤ 2 * T.weight i * (T.componentGenus i - 1) :=
      mul_nonneg (mul_nonneg (by omega) hw.le) (by omega)
    have := mul_pos hm
      (show 0 < 2 * T.weight i * (T.componentGenus i - 1) - T.intersection i i by omega)
    exact ⟨this.le, fun _ => by omega⟩

private lemma contribution_bounds (T : NumericalType)
    (hminimal : IsMinimal T) (hn : 1 < T.componentCount)
    (i : Fin T.componentCount) :
    0 ≤ (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2) ∧
      (¬ IsMinusTwoIndex T i →
        (1 : ℚ) / 2 ≤ (T.multiplicity i : ℚ) *
          ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
            (T.intersection i i : ℚ) / 2)) := by
  obtain ⟨hzero, hone⟩ := contribution_numerator_bounds T hminimal hn i
  refine ⟨?_, fun hi => ?_⟩
  · have : (0 : ℚ) ≤ T.multiplicity i *
        (2 * T.weight i * (T.componentGenus i - 1) - T.intersection i i) := by
      exact_mod_cast hzero
    linarith
  · have : (1 : ℚ) ≤ T.multiplicity i *
        (2 * T.weight i * (T.componentGenus i - 1) - T.intersection i i) := by
      exact_mod_cast hone hi
    linarith

/-- Every component of a minimal numerical type with more than one component
has nonnegative contribution to the genus. -/
public lemma contribution_nonneg_of_isMinimal (T : NumericalType)
    (hminimal : IsMinimal T) (hn : 1 < T.componentCount)
    (i : Fin T.componentCount) :
    0 ≤ (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
        (T.intersection i i : ℚ) / 2) :=
  (contribution_bounds T hminimal hn i).1

/-- A minus-two index makes zero contribution to the genus. -/
public lemma contribution_eq_zero_of_isMinusTwoIndex (T : NumericalType)
    (i : Fin T.componentCount) (hi : IsMinusTwoIndex T i) :
    (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
        (T.intersection i i : ℚ) / 2) = 0 := by
  rw [hi.1, hi.2]
  push_cast
  ring

/-- The contribution of a non-minus-two index of a minimal numerical type is
at least one half. -/
public lemma one_half_le_contribution_of_not_isMinusTwoIndex (T : NumericalType)
    (hminimal : IsMinimal T) (hn : 1 < T.componentCount)
    (i : Fin T.componentCount) (hi : ¬ IsMinusTwoIndex T i) :
    (1 : ℚ) / 2 ≤ (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
        (T.intersection i i : ℚ) / 2) :=
  (contribution_bounds T hminimal hn i).2 hi

/-- The contribution of any index is at most the genus minus one. -/
public lemma contribution_le_genus_sub_one
    (T : NumericalType) (g : ℤ) (hgenus : genus T = g)
    (hminimal : IsMinimal T) (hn : 1 < T.componentCount)
    (i : Fin T.componentCount) :
    (T.multiplicity i : ℚ) *
      ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
        (T.intersection i i : ℚ) / 2) ≤ (g : ℚ) - 1 := by
  let f : Fin T.componentCount → ℚ := fun j =>
    (T.multiplicity j : ℚ) *
      ((T.weight j : ℚ) * ((T.componentGenus j : ℚ) - 1) -
        (T.intersection j j : ℚ) / 2)
  have hle : f i ≤ ∑ j, f j :=
    Finset.single_le_sum (fun j _ => (contribution_bounds T hminimal hn j).1) (Finset.mem_univ i)
  have hsum : ∑ j, f j = (g : ℚ) - 1 := by
    have hcast : (genus T : ℚ) = (g : ℚ) := by rw [hgenus]
    rw [cast_genus] at hcast
    linarith
  exact hle.trans_eq hsum

end AlgebraicGeometry.NumericalType
