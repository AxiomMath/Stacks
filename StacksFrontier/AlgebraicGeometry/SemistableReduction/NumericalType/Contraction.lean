module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Irreducible
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import Mathlib

/-!
# Contracting a minus-one index

A numerical type with more than one component and a minus-one index at its last
component can be contracted: the last component is removed and the intersection
numbers, weights and component genera of the remaining components are adjusted
so that the result is again a numerical type of the same genus.

## Main definitions

* `AlgebraicGeometry.NumericalType.lastIndex` and
  `AlgebraicGeometry.NumericalType.remainingIndex`: the index being contracted
  and the inclusion of the surviving indices.
* `AlgebraicGeometry.NumericalType.IsContraction`: the relation between a
  numerical type and its contraction.
* `AlgebraicGeometry.NumericalType.contractLast`: the contracted numerical
  type.
* `AlgebraicGeometry.NumericalType.IsContractionUpToWeight`: the relation between a numerical
  type and a contraction whose weights are only required to divide the old ones.

## Main results

* `AlgebraicGeometry.NumericalType.isGreatest_contractLast_weight`: each weight of the
  contraction is the largest positive divisor of the old weight for which the genus formula is
  an integer.
* `AlgebraicGeometry.NumericalType.IsContractionUpToWeight.genus_eq`: a contraction up to weight
  has the same genus.

## References

* [Stacks Project, Tag 0C77](https://stacks.math.columbia.edu/tag/0C77)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

/-- The last component index of a numerical type. -/
public def lastIndex (T : NumericalType) : Fin T.componentCount :=
  ⟨T.componentCount - 1, Nat.sub_lt T.componentCount_pos (by omega)⟩

/-- The inclusion of the indices which remain after the last component is removed. -/
public def remainingIndex (T : NumericalType) (i : Fin (T.componentCount - 1)) :
    Fin T.componentCount :=
  Fin.castLE (Nat.sub_le _ _) i

/-- A numerical type whose last index is a minus-one index has more than one component. -/
lemma one_lt_componentCount (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) : 1 < T.componentCount := by
  rcases h with ⟨_, hd⟩
  by_contra hn
  have hc : T.componentCount = 1 := by
    have := T.componentCount_pos
    omega
  have hl : lastIndex T = ⟨0, T.componentCount_pos⟩ := Fin.ext (by simp [lastIndex, hc])
  have hz := intersection_self_eq_zero_of_componentCount_eq_one T hc
  rw [← hl] at hz
  have hw := T.weight_pos (lastIndex T)
  omega

/-- A sum over all component indices splits as the sum over the remaining indices plus the term
at the last index. -/
lemma sum_remaining_add_last (T : NumericalType) {M : Type*} [AddCommMonoid M]
    (f : Fin T.componentCount → M) :
    (∑ i, f i) = (∑ i : Fin (T.componentCount - 1), f (remainingIndex T i)) +
      f (lastIndex T) := by
  have hc : T.componentCount - 1 + 1 = T.componentCount :=
    Nat.sub_add_cancel T.componentCount_pos
  calc
    (∑ i, f i) = ∑ i : Fin (T.componentCount - 1 + 1), f (Fin.cast hc i) := by
      simpa [finCongr, Fin.cast] using (Equiv.sum_comp (finCongr hc) f).symm
    _ = (∑ i : Fin (T.componentCount - 1), f (remainingIndex T i)) +
        f (lastIndex T) := by
      simpa [remainingIndex, lastIndex, Fin.castLE, Fin.cast, Fin.castSucc, Fin.last] using
        (Fin.sum_univ_castSucc (f := fun i : Fin (T.componentCount - 1 + 1) =>
          f (Fin.cast hc i)))

/-- No remaining index is the last index. -/
lemma remainingIndex_ne_lastIndex (T : NumericalType)
    (i : Fin (T.componentCount - 1)) : remainingIndex T i ≠ lastIndex T := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [remainingIndex, lastIndex, Fin.val_castLE] at hv
  omega

/-- The inclusion `remainingIndex` of the remaining indices is injective. -/
lemma remainingIndex_injective (T : NumericalType) :
    Function.Injective (remainingIndex T) := by
  intro i j h
  apply Fin.ext
  simpa only [remainingIndex, Fin.val_castLE] using congrArg Fin.val h

/-- Every component index is either the last index or a remaining index. -/
lemma eq_lastIndex_or_eq_remainingIndex (T : NumericalType)
    (i : Fin T.componentCount) :
    i = lastIndex T ∨
      ∃ j : Fin (T.componentCount - 1), i = remainingIndex T j := by
  by_cases hi : i.val = T.componentCount - 1
  · exact Or.inl (Fin.ext hi)
  · exact Or.inr ⟨⟨i.val, by have := i.isLt; omega⟩, Fin.ext rfl⟩

/-- The intersection number `aᵢₙ` of a remaining component with the last one is nonnegative. -/
lemma intersection_remaining_last_nonneg (T : NumericalType)
    (i : Fin (T.componentCount - 1)) :
    0 ≤ T.intersection (remainingIndex T i) (lastIndex T) :=
  T.intersection_nonneg _ _ (remainingIndex_ne_lastIndex T i)

/-- The weight `wₙ` of the last component divides `aᵢₙ`: `aᵢₙ / wₙ * wₙ = aᵢₙ`. -/
lemma intersection_remaining_last_quotient (T : NumericalType)
    (i : Fin (T.componentCount - 1)) :
    T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (lastIndex T) * T.weight (lastIndex T) =
      T.intersection (remainingIndex T i) (lastIndex T) := by
  have hd := T.weight_dvd_intersection (lastIndex T) (remainingIndex T i)
  rw [T.intersection_symm (lastIndex T) (remainingIndex T i)] at hd
  exact Int.ediv_mul_cancel hd

/-- The quotient `aᵢₙ / wₙ` is nonnegative. -/
lemma intersection_remaining_last_quotient_nonneg (T : NumericalType)
    (i : Fin (T.componentCount - 1)) :
    0 ≤ T.intersection (remainingIndex T i) (lastIndex T) /
      T.weight (lastIndex T) :=
  Int.ediv_nonneg (intersection_remaining_last_nonneg T i)
    (le_of_lt (T.weight_pos (lastIndex T)))

/-- The weight `wᵢ` of a remaining component divides `aᵢₙ`: `aᵢₙ / wᵢ * wᵢ = aᵢₙ`. -/
lemma intersection_remaining_own_weight_quotient (T : NumericalType)
    (i : Fin (T.componentCount - 1)) :
    T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (remainingIndex T i) * T.weight (remainingIndex T i) =
      T.intersection (remainingIndex T i) (lastIndex T) :=
  Int.ediv_mul_cancel (T.weight_dvd_intersection _ _)

/-- The quotient `aᵢₙ / wᵢ` is nonnegative. -/
lemma intersection_remaining_own_weight_quotient_nonneg (T : NumericalType)
    (i : Fin (T.componentCount - 1)) :
    0 ≤ T.intersection (remainingIndex T i) (lastIndex T) /
      T.weight (remainingIndex T i) :=
  Int.ediv_nonneg (intersection_remaining_last_nonneg T i)
    (le_of_lt (T.weight_pos (remainingIndex T i)))

/-- For a minus-one last index `n`, the integer `aᵢⱼ + aᵢₙ (aⱼₙ / wₙ)` equals, in `ℚ`, the Schur
complement `aᵢⱼ - aᵢₙ aⱼₙ / aₙₙ`. -/
lemma contractedIntersection_cast (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i j : Fin (T.componentCount - 1)) :
    ((T.intersection (remainingIndex T i) (remainingIndex T j) +
      T.intersection (remainingIndex T i) (lastIndex T) *
        (T.intersection (remainingIndex T j) (lastIndex T) /
          T.weight (lastIndex T)) : ℤ) : ℚ) =
      T.intersection (remainingIndex T i) (remainingIndex T j) -
        (T.intersection (remainingIndex T i) (lastIndex T) *
          T.intersection (remainingIndex T j) (lastIndex T) : ℚ) /
          T.intersection (lastIndex T) (lastIndex T) := by
  have hd : (T.intersection (lastIndex T) (lastIndex T) : ℚ) =
      -(T.weight (lastIndex T) : ℚ) := by exact_mod_cast h.2
  have hq : ((T.intersection (remainingIndex T j) (lastIndex T) /
      T.weight (lastIndex T) : ℤ) : ℚ) * T.weight (lastIndex T) =
      T.intersection (remainingIndex T j) (lastIndex T) := by
    exact_mod_cast intersection_remaining_last_quotient T j
  have hw : (T.weight (lastIndex T) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (T.weight_pos (lastIndex T)))
  have hq' : ((T.intersection (remainingIndex T j) (lastIndex T) /
      T.weight (lastIndex T) : ℤ) : ℚ) =
      (T.intersection (remainingIndex T j) (lastIndex T) : ℚ) /
        T.weight (lastIndex T) :=
    (eq_div_iff hw).2 hq
  rw [hd]
  push_cast
  rw [hq']
  ring

/-- For a minus-one last index `n`, the contracted intersection numbers
`aᵢⱼ + aᵢₙ (aⱼₙ / wₙ)` are symmetric in `i` and `j`. -/
lemma contractedIntersection_symm (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i j : Fin (T.componentCount - 1)) :
    T.intersection (remainingIndex T i) (remainingIndex T j) +
        T.intersection (remainingIndex T i) (lastIndex T) *
          (T.intersection (remainingIndex T j) (lastIndex T) /
            T.weight (lastIndex T)) =
      T.intersection (remainingIndex T j) (remainingIndex T i) +
        T.intersection (remainingIndex T j) (lastIndex T) *
          (T.intersection (remainingIndex T i) (lastIndex T) /
            T.weight (lastIndex T)) := by
  apply Int.cast_injective (α := ℚ)
  rw [contractedIntersection_cast T h i j, contractedIntersection_cast T h j i,
    T.intersection_symm (remainingIndex T i) (remainingIndex T j)]
  ring

/-- For distinct remaining indices `i ≠ j`, the contracted intersection number
`aᵢⱼ + aᵢₙ (aⱼₙ / wₙ)` is nonnegative. -/
lemma contractedIntersection_nonneg (T : NumericalType)
    (i j : Fin (T.componentCount - 1)) (hij : i ≠ j) :
    0 ≤ T.intersection (remainingIndex T i) (remainingIndex T j) +
      T.intersection (remainingIndex T i) (lastIndex T) *
        (T.intersection (remainingIndex T j) (lastIndex T) /
          T.weight (lastIndex T)) :=
  add_nonneg (T.intersection_nonneg _ _ ((remainingIndex_injective T).ne hij))
    (mul_nonneg (intersection_remaining_last_nonneg T i)
      (intersection_remaining_last_quotient_nonneg T j))

/-- For distinct remaining indices `i ≠ j`, if the contracted intersection number
`aᵢⱼ + aᵢₙ (aⱼₙ / wₙ)` vanishes then `aᵢⱼ = 0` and one of `aᵢₙ`, `aⱼₙ` vanishes. -/
lemma contractedIntersection_zero (T : NumericalType)
    (i j : Fin (T.componentCount - 1)) (hij : i ≠ j)
    (hz : T.intersection (remainingIndex T i) (remainingIndex T j) +
      T.intersection (remainingIndex T i) (lastIndex T) *
        (T.intersection (remainingIndex T j) (lastIndex T) /
          T.weight (lastIndex T)) = 0) :
    T.intersection (remainingIndex T i) (remainingIndex T j) = 0 ∧
      (T.intersection (remainingIndex T i) (lastIndex T) = 0 ∨
        T.intersection (remainingIndex T j) (lastIndex T) = 0) := by
  have ha : 0 ≤ T.intersection (remainingIndex T i) (remainingIndex T j) :=
    T.intersection_nonneg _ _ ((remainingIndex_injective T).ne hij)
  have hb : 0 ≤ T.intersection (remainingIndex T i) (lastIndex T) *
      (T.intersection (remainingIndex T j) (lastIndex T) /
        T.weight (lastIndex T)) :=
    mul_nonneg (intersection_remaining_last_nonneg T i)
      (intersection_remaining_last_quotient_nonneg T j)
  refine ⟨by omega, ?_⟩
  have hb0 : T.intersection (remainingIndex T i) (lastIndex T) *
      (T.intersection (remainingIndex T j) (lastIndex T) /
        T.weight (lastIndex T)) = 0 := by omega
  rcases mul_eq_zero.mp hb0 with hi | hj
  · exact Or.inl hi
  · exact Or.inr (by rw [← intersection_remaining_last_quotient T j, hj, zero_mul])

/-- The contracted intersection numbers `aᵢⱼ + aᵢₙ (aⱼₙ / wₙ)` are connected: no nonempty proper
set of remaining indices has vanishing contracted intersection with its complement. -/
lemma contractedIntersection_connected (T : NumericalType)
    (I : Set (Fin (T.componentCount - 1))) (hI : I.Nonempty)
    (hIuniv : I ≠ Set.univ)
    (hz : ∀ i, i ∈ I → ∀ j, j ∉ I →
      T.intersection (remainingIndex T i) (remainingIndex T j) +
        T.intersection (remainingIndex T i) (lastIndex T) *
          (T.intersection (remainingIndex T j) (lastIndex T) /
            T.weight (lastIndex T)) = 0) : False := by
  let S : Set (Fin T.componentCount) := remainingIndex T '' I
  have hlast : lastIndex T ∉ S := by
    rintro ⟨i, _, hi⟩
    exact remainingIndex_ne_lastIndex T i hi
  by_cases hall : ∀ i, i ∈ I →
      T.intersection (remainingIndex T i) (lastIndex T) = 0
  · refine T.connected ⟨S, hI.image _, fun hs => hlast (hs ▸ Set.mem_univ _), ?_⟩
    intro x hx y hy
    obtain ⟨i, hi, rfl⟩ := hx
    rcases eq_lastIndex_or_eq_remainingIndex T y with rfl | ⟨j, rfl⟩
    · exact hall i hi
    · have hj : j ∉ I := fun hj => hy ⟨j, hj, rfl⟩
      exact (contractedIntersection_zero T i j (fun heq => hj (heq ▸ hi)) (hz i hi j hj)).1
  · push Not at hall
    obtain ⟨i₀, hi₀, hnonzero⟩ := hall
    have hother (j : Fin (T.componentCount - 1)) (hj : j ∉ I) :
        T.intersection (remainingIndex T j) (lastIndex T) = 0 :=
      (contractedIntersection_zero T i₀ j (fun heq => hj (heq ▸ hi₀))
        (hz i₀ hi₀ j hj)).2.resolve_left hnonzero
    refine T.connected ⟨insert (lastIndex T) S, ⟨lastIndex T, Set.mem_insert _ _⟩, ?_, ?_⟩
    · intro hs
      refine hIuniv (Set.eq_univ_of_forall fun j => ?_)
      have hj : remainingIndex T j ∈ insert (lastIndex T) S := hs ▸ Set.mem_univ _
      exact (Set.mem_insert_iff.mp hj).elim
        (fun h => absurd h (remainingIndex_ne_lastIndex T j))
        (remainingIndex_injective T).mem_set_image.mp
    · intro x hx y hy
      rcases eq_lastIndex_or_eq_remainingIndex T y with rfl | ⟨j, rfl⟩
      · exact False.elim (hy (Set.mem_insert _ _))
      · have hj : j ∉ I := fun hj =>
          hy (Set.mem_insert_iff.mpr (Or.inr ⟨j, hj, rfl⟩))
        rcases Set.mem_insert_iff.mp hx with rfl | hx'
        · rw [T.intersection_symm]
          exact hother j hj
        · obtain ⟨i, hi, rfl⟩ := hx'
          exact (contractedIntersection_zero T i j (fun heq => hj (heq ▸ hi)) (hz i hi j hj)).1

/-- For a minus-one last index `n`, `∑ⱼ (aⱼₙ / wₙ) mⱼ = mₙ`, the sum running over the remaining
indices. -/
lemma quotient_weighted_sum_eq_lastMultiplicity (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    (∑ j : Fin (T.componentCount - 1),
      (T.intersection (remainingIndex T j) (lastIndex T) /
        T.weight (lastIndex T)) * T.multiplicity (remainingIndex T j)) =
      T.multiplicity (lastIndex T) := by
  have hlast := T.intersection_mul_multiplicity (lastIndex T)
  rw [sum_remaining_add_last T] at hlast
  have hs :
      (∑ j : Fin (T.componentCount - 1),
        (T.intersection (remainingIndex T j) (lastIndex T) /
          T.weight (lastIndex T)) * T.multiplicity (remainingIndex T j)) *
        T.weight (lastIndex T) =
      ∑ j : Fin (T.componentCount - 1),
        T.intersection (lastIndex T) (remainingIndex T j) *
          T.multiplicity (remainingIndex T j) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by
      rw [T.intersection_symm (lastIndex T) (remainingIndex T j), mul_right_comm,
        intersection_remaining_last_quotient T j]
  rw [h.2] at hlast
  have hw : T.weight (lastIndex T) ≠ 0 := ne_of_gt (T.weight_pos _)
  have heq :
      ((∑ j : Fin (T.componentCount - 1),
        (T.intersection (remainingIndex T j) (lastIndex T) /
          T.weight (lastIndex T)) * T.multiplicity (remainingIndex T j)) -
        T.multiplicity (lastIndex T)) * T.weight (lastIndex T) = 0 := by
    nlinarith [hs, hlast]
  exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hw)

/-- For a minus-one last index `n`, `∑ᵢ mᵢ aᵢₙ = mₙ wₙ`, the sum running over the remaining
indices. -/
lemma lastIntersection_weighted_sum (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) :
    (∑ i : Fin (T.componentCount - 1),
      T.multiplicity (remainingIndex T i) *
        T.intersection (remainingIndex T i) (lastIndex T)) =
      T.multiplicity (lastIndex T) * T.weight (lastIndex T) := by
  have hlast := T.intersection_mul_multiplicity (lastIndex T)
  rw [sum_remaining_add_last T, h.2] at hlast
  have hs :
      (∑ i : Fin (T.componentCount - 1),
        T.multiplicity (remainingIndex T i) *
          T.intersection (remainingIndex T i) (lastIndex T)) =
      ∑ i : Fin (T.componentCount - 1),
        T.intersection (lastIndex T) (remainingIndex T i) *
          T.multiplicity (remainingIndex T i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [T.intersection_symm (lastIndex T) (remainingIndex T i)]
    ring
  rw [hs]
  nlinarith [hlast]

/-- For a minus-one last index `n`, the multiplicities of the remaining components lie in the
kernel of the contracted intersection matrix `aᵢⱼ + aᵢₙ (aⱼₙ / wₙ)`. -/
lemma contractedIntersection_mul_multiplicity (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T))
    (i : Fin (T.componentCount - 1)) :
    ∑ j : Fin (T.componentCount - 1),
      (T.intersection (remainingIndex T i) (remainingIndex T j) +
        T.intersection (remainingIndex T i) (lastIndex T) *
          (T.intersection (remainingIndex T j) (lastIndex T) /
            T.weight (lastIndex T))) * T.multiplicity (remainingIndex T j) = 0 := by
  have hrow := T.intersection_mul_multiplicity (remainingIndex T i)
  rw [sum_remaining_add_last T] at hrow
  have hquot := quotient_weighted_sum_eq_lastMultiplicity T h
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  conv_lhs => rhs; arg 2; ext j; rw [mul_assoc]
  rw [← Finset.mul_sum, hquot]
  omega

/-- Unless `b` is even and `c` is odd, the integer `c (b - 1)` is even. -/
lemma even_mul_pred_of_not_halving (b c : ℤ)
    (h : ¬ (Even b ∧ Odd c)) : Even (c * (b - 1)) := by
  rcases Int.even_or_odd b with hb | hb
  · exact (Int.not_odd_iff_even.mp fun hodd => h ⟨hb, hodd⟩).mul_right _
  · exact (hb.sub_odd (by norm_num : Odd (1 : ℤ))).mul_left _

/-- If `wₙ` and `w` divide `a`, with `a / wₙ` even and `a / w` odd, then `w` is even. -/
lemma halving_implies_even_weight (w wn a : ℤ)
    (hwnq : a / wn * wn = a) (hwq : a / w * w = a)
    (hpar : Even (a / wn) ∧ Odd (a / w)) : Even w := by
  have haeven : Even a := by
    rw [← hwnq]
    exact hpar.1.mul_right wn
  by_contra hn
  have hwodd : Odd w := Int.not_even_iff_odd.mp hn
  have haodd : Odd a := by
    rw [← hwq]
    exact hpar.2.mul hwodd
  exact (Int.not_odd_iff_even.mpr haeven) haodd

/-- If `w > 0` and `wₙ`, `w` divide `a`, with `a / wₙ` even and `a / w` odd, then `w / 2 > 0`. -/
lemma half_weight_pos (w wn a : ℤ) (hw : 0 < w)
    (hwnq : a / wn * wn = a) (hwq : a / w * w = a)
    (hpar : Even (a / wn) ∧ Odd (a / w)) : 0 < w / 2 := by
  obtain ⟨k, hk⟩ := halving_implies_even_weight w wn a hwnq hwq hpar
  omega

/-- For an even integer `w`, `w / 2` divides `w`. -/
lemma half_weight_dvd_weight (w : ℤ) (hw : Even w) : w / 2 ∣ w :=
  ⟨2, (Int.ediv_mul_cancel (even_iff_two_dvd.mp hw)).symm⟩

/-- The contracted weight `w'ᵢ`, equal to `wᵢ / 2` if `aᵢₙ / wₙ` is even and `aᵢₙ / wᵢ` is odd
and to `wᵢ` otherwise, divides the weight `wᵢ`. -/
private lemma contractedWeight_dvd_weight_aux (T : NumericalType)
    (i : Fin (T.componentCount - 1)) :
    (if Even (T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (lastIndex T)) ∧
        Odd (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) then
      T.weight (remainingIndex T i) / 2
    else T.weight (remainingIndex T i)) ∣ T.weight (remainingIndex T i) := by
  split_ifs with hp
  · exact half_weight_dvd_weight _ (halving_implies_even_weight _ _ _
      (intersection_remaining_last_quotient T i)
      (intersection_remaining_own_weight_quotient T i) hp)
  · exact dvd_refl _

/-- The contracted weight `w'ᵢ`, equal to `wᵢ / 2` if `aᵢₙ / wₙ` is even and `aᵢₙ / wᵢ` is odd
and to `wᵢ` otherwise, divides the contracted intersection number `aᵢⱼ + aᵢₙ (aⱼₙ / wₙ)`. -/
lemma contractedWeight_dvd_intersection (T : NumericalType)
    (i j : Fin (T.componentCount - 1)) :
    (if Even (T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (lastIndex T)) ∧
        Odd (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) then
      T.weight (remainingIndex T i) / 2
    else T.weight (remainingIndex T i)) ∣
      T.intersection (remainingIndex T i) (remainingIndex T j) +
        T.intersection (remainingIndex T i) (lastIndex T) *
          (T.intersection (remainingIndex T j) (lastIndex T) /
            T.weight (lastIndex T)) := by
  have hd := contractedWeight_dvd_weight_aux T i
  exact dvd_add (dvd_trans hd (T.weight_dvd_intersection _ _))
    (dvd_mul_of_dvd_left (dvd_trans hd (T.weight_dvd_intersection _ _)) _)

/-- The contracted weight `w'ᵢ`, equal to `wᵢ / 2` if `aᵢₙ / wₙ` is even and `aᵢₙ / wᵢ` is odd
and to `wᵢ` otherwise, is positive. -/
lemma contractedWeight_pos (T : NumericalType)
    (i : Fin (T.componentCount - 1)) :
    0 < if Even (T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (lastIndex T)) ∧
        Odd (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) then
      T.weight (remainingIndex T i) / 2
    else T.weight (remainingIndex T i) := by
  split_ifs with hp
  · exact half_weight_pos _ _ _ (T.weight_pos _) (intersection_remaining_last_quotient T i)
      (intersection_remaining_own_weight_quotient T i) hp
  · exact T.weight_pos _

/-- For `g, b, c ≥ 0` with `c = 0` whenever `b = 0`, the integer equal to `2g - 1 + c (b - 1)` if
`b` is even and `c` is odd, and to `g + c (b - 1) / 2` otherwise, is nonnegative. -/
lemma contractedComponentGenus_nonneg (g b c : ℤ)
    (hg : 0 ≤ g) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hzero : b = 0 → c = 0) :
    0 ≤ if Even b ∧ Odd c then 2 * g - 1 + c * (b - 1)
      else g + c * (b - 1) / 2 := by
  split_ifs with hp
  · have hcpos : 1 ≤ c := by
      obtain ⟨k, hk⟩ := hp.2
      omega
    have hbpos : 1 ≤ b := by
      by_contra hn
      have := hzero (by omega)
      omega
    have hbge : 2 ≤ b := by
      obtain ⟨k, hk⟩ := hp.1
      omega
    nlinarith [mul_nonneg (show 0 ≤ c - 1 by omega)
      (show 0 ≤ b - 1 by omega)]
  · by_cases hb0 : b = 0
    · simp [hb0, hzero hb0, hg]
    · exact add_nonneg hg (Int.ediv_nonneg (mul_nonneg hc (by omega)) (by norm_num))

/-- The contracted component genus `g'ᵢ`, equal to `2gᵢ - 1 + c (b - 1)` if `b` is even and `c`
is odd and to `gᵢ + c (b - 1) / 2` otherwise, where `b = aᵢₙ / wₙ` and `c = aᵢₙ / wᵢ`, is
nonnegative. -/
lemma contractedComponentGenus_nonneg_of_type (T : NumericalType)
    (i : Fin (T.componentCount - 1)) :
    0 ≤ if Even (T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (lastIndex T)) ∧
        Odd (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) then
      2 * T.componentGenus (remainingIndex T i) - 1 +
        (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) *
        (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (lastIndex T) - 1)
    else T.componentGenus (remainingIndex T i) +
      ((T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) *
        (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (lastIndex T) - 1)) / 2 := by
  apply contractedComponentGenus_nonneg
  · exact T.componentGenus_nonneg _
  · exact intersection_remaining_last_quotient_nonneg T i
  · exact intersection_remaining_own_weight_quotient_nonneg T i
  · intro hb
    have hq := intersection_remaining_last_quotient T i
    rw [hb, zero_mul] at hq
    simp [← hq]

/-- If `wₙ, w' > 0` and `wₙ`, `w` divide `a`, then in `ℚ`
`(a² - wₙ a) / (2 w' wₙ) = (w / w') (a / w) ((a / wₙ) - 1) / 2`, the quotients being taken in
`ℤ`. -/
lemma contractedGenusCorrection_cast (w wn a wp : ℤ)
    (hwn : 0 < wn) (hwp : 0 < wp)
    (hwnq : a / wn * wn = a) (hwq : a / w * w = a) :
    ((a : ℚ) ^ 2 - wn * a) / (2 * wp * wn) =
      (w : ℚ) / wp * (a / w : ℤ) * ((a / wn : ℤ) - 1) / 2 := by
  have hAwn : (a : ℚ) = (a / wn : ℤ) * wn := by
    exact_mod_cast hwnq.symm
  have hAw : (a : ℚ) = (a / w : ℤ) * w := by
    exact_mod_cast hwq.symm
  have hnum : (a : ℚ) ^ 2 - wn * a =
      (a / w : ℤ) * w * wn * ((a / wn : ℤ) - 1) := by
    linear_combination (a : ℚ) * hAwn + (wn : ℚ) * (((a / wn : ℤ) : ℚ) - 1) * hAw
  have hwn' : (wn : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hwn)
  have hwp' : (wp : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hwp)
  rw [hnum]
  field_simp

/-- Let `w, wₙ > 0` divide `a`, put `b = a / wₙ` and `c = a / w`, and let `w' = w / 2` if `b` is
even and `c` is odd, and `w' = w` otherwise. Then the integer equal to `2g - 1 + c (b - 1)` in the
first case and to `g + c (b - 1) / 2` in the second equals, in `ℚ`,
`(w / w') (g - 1) + 1 + (a² - wₙ a) / (2 w' wₙ)`. -/
lemma contractedComponentGenus_cast (g w wn a : ℤ)
    (hw : 0 < w) (hwn : 0 < wn)
    (hwnq : a / wn * wn = a) (hwq : a / w * w = a) :
    let b : ℤ := a / wn
    let c : ℤ := a / w
    let p : Prop := Even b ∧ Odd c
    let wp : ℤ := if p then w / 2 else w
    (((if p then 2 * g - 1 + c * (b - 1)
        else g + c * (b - 1) / 2 : ℤ) : ℚ) =
      (w : ℚ) / wp * ((g : ℚ) - 1) + 1 +
        ((a : ℚ) ^ 2 - wn * a) / (2 * wp * wn)) := by
  dsimp
  by_cases hp : Even (a / wn) ∧ Odd (a / w)
  · simp only [ite_eq_left hp]
    have he : Even w := halving_implies_even_weight w wn a hwnq hwq hp
    have hwp : 0 < w / 2 := half_weight_pos w wn a hw hwnq hwq hp
    have hwp2 : w / 2 * 2 = w := Int.ediv_mul_cancel (even_iff_two_dvd.mp he)
    have hwpq : ((w / 2 : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hwp)
    have hr : (w : ℚ) / (w / 2 : ℤ) = 2 := by
      apply (div_eq_iff hwpq).2
      exact_mod_cast (by nlinarith [hwp2] : w = 2 * (w / 2))
    rw [contractedGenusCorrection_cast w wn a (w / 2) hwn hwp hwnq hwq, hr]
    push_cast
    ring
  · simp only [ite_eq_right hp]
    have he : Even ((a / w) * (a / wn - 1)) :=
      even_mul_pred_of_not_halving _ _ hp
    have hcast : (((a / w) * (a / wn - 1) / 2 : ℤ) : ℚ) =
        ((a / w) * (a / wn - 1) : ℤ) / 2 :=
      Int.cast_div (even_iff_two_dvd.mp he) (by norm_num)
    rw [Int.cast_add, hcast, contractedGenusCorrection_cast w wn a w hwn hw hwnq hwq,
      div_self (by exact_mod_cast (ne_of_gt hw) : (w : ℚ) ≠ 0)]
    push_cast
    ring

/-- If `wₙ, w' > 0`, `wₙ` and `w` divide `a`, `g' = (w / w') (g - 1) + 1 + (a² - wₙ a) / (2 w' wₙ)`
and `a' = aᵢᵢ + a (a / wₙ)`, then `w' (g' - 1) - a' / 2 = w (g - 1) - aᵢᵢ / 2 - a / 2`. -/
lemma contractedGenusLocal (g aii w wn a wp gp ap : ℤ)
    (hwn : 0 < wn) (hwp : 0 < wp)
    (hwnq : a / wn * wn = a) (hwq : a / w * w = a)
    (hgp : (gp : ℚ) = (w : ℚ) / wp * ((g : ℚ) - 1) + 1 +
      ((a : ℚ) ^ 2 - wn * a) / (2 * wp * wn))
    (hap : ap = aii + a * (a / wn)) :
    (wp : ℚ) * ((gp : ℚ) - 1) - (ap : ℚ) / 2 =
      (w : ℚ) * ((g : ℚ) - 1) - (aii : ℚ) / 2 - (a : ℚ) / 2 := by
  have hcorr := contractedGenusCorrection_cast w wn a wp hwn hwp hwnq hwq
  have hA : (a : ℚ) = (a / w : ℤ) * w := by exact_mod_cast hwq.symm
  have hwp' : (wp : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hwp)
  rw [hgp, hap, hcorr]
  push_cast
  rw [hA]
  field_simp
  ring

/-- The complete specification of contracting the last component of a numerical
type. -/
public structure IsContraction (T T' : NumericalType) : Prop where
  /-- The contraction removes precisely one component. -/
  componentCount_eq : T'.componentCount = T.componentCount - 1
  /-- Multiplicities of the remaining components do not change. -/
  multiplicity_eq : ∀ i : Fin (T.componentCount - 1),
    T'.multiplicity (Fin.cast componentCount_eq.symm i) = T.multiplicity (remainingIndex T i)
  /-- The Schur-complement formula for the new intersection matrix. -/
  intersection_eq : ∀ i j : Fin (T.componentCount - 1),
    (T'.intersection (Fin.cast componentCount_eq.symm i)
        (Fin.cast componentCount_eq.symm j) : ℚ) =
      T.intersection (remainingIndex T i) (remainingIndex T j) -
        (T.intersection (remainingIndex T i) (lastIndex T) *
          T.intersection (remainingIndex T j) (lastIndex T) : ℚ) /
          T.intersection (lastIndex T) (lastIndex T)
  /-- The weight `wᵢ` is halved exactly when `aᵢₙ / wₙ` is even and `aᵢₙ / wᵢ` is odd. -/
  weight_eq : ∀ i : Fin (T.componentCount - 1),
    T'.weight (Fin.cast componentCount_eq.symm i) =
      if Even (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (lastIndex T)) ∧
          Odd (T.intersection (remainingIndex T i) (lastIndex T) /
            T.weight (remainingIndex T i)) then
        T.weight (remainingIndex T i) / 2
      else
        T.weight (remainingIndex T i)
  /-- The component-genus formula for a contracted numerical type. -/
  componentGenus_eq : ∀ i : Fin (T.componentCount - 1),
    (T'.componentGenus (Fin.cast componentCount_eq.symm i) : ℚ) =
      (T.weight (remainingIndex T i) : ℚ) /
          T'.weight (Fin.cast componentCount_eq.symm i) *
            ((T.componentGenus (remainingIndex T i) : ℚ) - 1) + 1 +
        ((T.intersection (remainingIndex T i) (lastIndex T) : ℚ) ^ 2 -
            T.weight (lastIndex T) *
              T.intersection (remainingIndex T i) (lastIndex T)) /
          (2 * T'.weight (Fin.cast componentCount_eq.symm i) * T.weight (lastIndex T))
  /-- Contracting a minus-one component preserves the genus. -/
  genus_eq : genus T' = genus T

/-- The contraction of a numerical type along its last component, together with
the defining formulas and invariance of its genus. -/
@[stacks 0C77]
public noncomputable def contractLast (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) : {T' : NumericalType // IsContraction T T'} := by
  classical
  have hn : 0 < T.componentCount - 1 := by
    have ht := one_lt_componentCount T h
    omega
  let A (i j : Fin (T.componentCount - 1)) : ℤ :=
    T.intersection (remainingIndex T i) (remainingIndex T j) +
      T.intersection (remainingIndex T i) (lastIndex T) *
        (T.intersection (remainingIndex T j) (lastIndex T) /
          T.weight (lastIndex T))
  let W (i : Fin (T.componentCount - 1)) : ℤ :=
    if Even (T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (lastIndex T)) ∧
        Odd (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) then
      T.weight (remainingIndex T i) / 2
    else T.weight (remainingIndex T i)
  let G (i : Fin (T.componentCount - 1)) : ℤ :=
    if Even (T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (lastIndex T)) ∧
        Odd (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) then
      2 * T.componentGenus (remainingIndex T i) - 1 +
        (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) *
          (T.intersection (remainingIndex T i) (lastIndex T) /
            T.weight (lastIndex T) - 1)
    else T.componentGenus (remainingIndex T i) +
      ((T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) *
        (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (lastIndex T) - 1)) / 2
  let T' : NumericalType := {
    componentCount := T.componentCount - 1
    componentCount_pos := hn
    multiplicity := fun i => T.multiplicity (remainingIndex T i)
    intersection := A
    weight := W
    componentGenus := G
    multiplicity_pos := fun i => T.multiplicity_pos (remainingIndex T i)
    weight_pos := contractedWeight_pos T
    componentGenus_nonneg := contractedComponentGenus_nonneg_of_type T
    intersection_symm := contractedIntersection_symm T h
    intersection_nonneg := contractedIntersection_nonneg T
    connected := fun ⟨I, hI, hIuniv, hz⟩ => contractedIntersection_connected T I hI hIuniv hz
    intersection_mul_multiplicity := contractedIntersection_mul_multiplicity T h
    weight_dvd_intersection := contractedWeight_dvd_intersection T
  }
  have hG (i : Fin (T.componentCount - 1)) := contractedComponentGenus_cast
    (T.componentGenus (remainingIndex T i)) (T.weight (remainingIndex T i))
    (T.weight (lastIndex T)) (T.intersection (remainingIndex T i) (lastIndex T))
    (T.weight_pos _) (T.weight_pos _)
    (intersection_remaining_last_quotient T i)
    (intersection_remaining_own_weight_quotient T i)
  refine ⟨T', ?_⟩
  refine {
    componentCount_eq := rfl
    multiplicity_eq := fun _ => rfl
    intersection_eq := contractedIntersection_cast T h
    weight_eq := fun _ => rfl
    componentGenus_eq := hG
    genus_eq := by
      have hlocal (i : Fin (T.componentCount - 1)) :=
        contractedGenusLocal (T.componentGenus (remainingIndex T i))
          (T.intersection (remainingIndex T i) (remainingIndex T i))
          (T.weight (remainingIndex T i)) (T.weight (lastIndex T))
          (T.intersection (remainingIndex T i) (lastIndex T))
          (W i) (G i) (A i i) (T.weight_pos _) (contractedWeight_pos T i)
          (intersection_remaining_last_quotient T i)
          (intersection_remaining_own_weight_quotient T i) (hG i) rfl
      have hweighted :
          (∑ i : Fin (T.componentCount - 1),
            (T.multiplicity (remainingIndex T i) : ℚ) *
              (T.intersection (remainingIndex T i) (lastIndex T) : ℚ)) =
            (T.multiplicity (lastIndex T) : ℚ) * T.weight (lastIndex T) := by
        exact_mod_cast lastIntersection_weighted_sum T h
      have hsumDiv :
          (∑ i : Fin (T.componentCount - 1),
            ((T.multiplicity (remainingIndex T i) : ℚ) *
              (T.intersection (remainingIndex T i) (lastIndex T) : ℚ)) / 2) =
            (T.multiplicity (lastIndex T) : ℚ) * T.weight (lastIndex T) / 2 := by
        rw [← hweighted, Finset.sum_div]
      have hsum :
          (∑ i : Fin (T.componentCount - 1),
            (T.multiplicity (remainingIndex T i) : ℚ) *
              ((W i : ℚ) * ((G i : ℚ) - 1) - (A i i : ℚ) / 2)) =
          (∑ i : Fin (T.componentCount - 1),
            (T.multiplicity (remainingIndex T i) : ℚ) *
              ((T.weight (remainingIndex T i) : ℚ) *
                  ((T.componentGenus (remainingIndex T i) : ℚ) - 1) -
                (T.intersection (remainingIndex T i) (remainingIndex T i) : ℚ) / 2)) -
            (T.multiplicity (lastIndex T) : ℚ) * T.weight (lastIndex T) / 2 := by
        rw [← hsumDiv, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [hlocal i]; ring
      have heq : (genus T' : ℚ) = (genus T : ℚ) := by
        rw [cast_genus T', cast_genus T]
        change 1 + (∑ i : Fin (T.componentCount - 1),
          (T.multiplicity (remainingIndex T i) : ℚ) *
            ((W i : ℚ) * ((G i : ℚ) - 1) - (A i i : ℚ) / 2)) =
          1 + (∑ i : Fin T.componentCount,
            (T.multiplicity i : ℚ) *
              ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
                (T.intersection i i : ℚ) / 2))
        rw [sum_remaining_add_last T, hsum, h.1, h.2]
        push_cast
        ring
      exact_mod_cast heq
  }

/-! ### Contractions with smaller weights -/

/-- At a positive divisor `d` of `w`, the genus formula of a contraction is an integer only if `d`
divides the weight chosen by the contraction of a numerical type. -/
lemma dvd_contractedWeight_of_isInt (g w wn a d : ℤ) (hwn : 0 < wn) (hd : 0 < d)
    (hwnq : a / wn * wn = a) (hwq : a / w * w = a) (hdw : d ∣ w)
    (hG : ∃ G : ℤ, (G : ℚ) = (w : ℚ) / d * ((g : ℚ) - 1) + 1 +
      ((a : ℚ) ^ 2 - wn * a) / (2 * d * wn)) :
    d ∣ if Even (a / wn) ∧ Odd (a / w) then w / 2 else w := by
  obtain ⟨G, hG⟩ := hG
  obtain ⟨q, rfl⟩ := hdw
  split_ifs with hp
  · rw [contractedGenusCorrection_cast (d * q) wn a d hwn hd hwnq hwq] at hG
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hq : ((d * q : ℤ) : ℚ) / d = q := by push_cast; field_simp
    rw [hq] at hG
    have h2 : q * ((a / (d * q)) * (a / wn - 1)) = 2 * (G - 1 - q * (g - 1)) := by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [hG]
      ring
    have hodd : Odd ((a / (d * q)) * (a / wn - 1)) :=
      hp.2.mul (hp.1.sub_odd odd_one)
    have hqeven : Even q := by
      have he : Even (q * ((a / (d * q)) * (a / wn - 1))) :=
        ⟨G - 1 - q * (g - 1), by rw [h2]; ring⟩
      exact (Int.even_mul.mp he).resolve_right (Int.not_even_iff_odd.mpr hodd)
    obtain ⟨r, rfl⟩ := hqeven
    refine ⟨r, ?_⟩
    rw [show d * (r + r) = 2 * (d * r) by ring, Int.mul_ediv_cancel_left _ two_ne_zero]
  · exact ⟨q, rfl⟩

/-- `T'` is the contraction of the last component of `T` in every datum except possibly the
weights: it has one component fewer, the same multiplicities, the Schur-complement intersection
matrix, each of its weights `w'ᵢ` divides `wᵢ`, and its component genera are given by the genus
formula of a contraction at the weights `w'ᵢ`. -/
public structure IsContractionUpToWeight (T T' : NumericalType) : Prop where
  /-- The contraction removes precisely one component. -/
  componentCount_eq : T'.componentCount = T.componentCount - 1
  /-- Multiplicities of the remaining components do not change. -/
  multiplicity_eq : ∀ i : Fin (T.componentCount - 1),
    T'.multiplicity (Fin.cast componentCount_eq.symm i) = T.multiplicity (remainingIndex T i)
  /-- The Schur-complement formula for the new intersection matrix. -/
  intersection_eq : ∀ i j : Fin (T.componentCount - 1),
    (T'.intersection (Fin.cast componentCount_eq.symm i)
        (Fin.cast componentCount_eq.symm j) : ℚ) =
      T.intersection (remainingIndex T i) (remainingIndex T j) -
        (T.intersection (remainingIndex T i) (lastIndex T) *
          T.intersection (remainingIndex T j) (lastIndex T) : ℚ) /
          T.intersection (lastIndex T) (lastIndex T)
  /-- Each new weight divides the old one. -/
  weight_dvd : ∀ i : Fin (T.componentCount - 1),
    T'.weight (Fin.cast componentCount_eq.symm i) ∣ T.weight (remainingIndex T i)
  /-- The component-genus formula of a contraction, at the new weights. -/
  componentGenus_eq : ∀ i : Fin (T.componentCount - 1),
    (T'.componentGenus (Fin.cast componentCount_eq.symm i) : ℚ) =
      (T.weight (remainingIndex T i) : ℚ) /
          T'.weight (Fin.cast componentCount_eq.symm i) *
            ((T.componentGenus (remainingIndex T i) : ℚ) - 1) + 1 +
        ((T.intersection (remainingIndex T i) (lastIndex T) : ℚ) ^ 2 -
            T.weight (lastIndex T) *
              T.intersection (remainingIndex T i) (lastIndex T)) /
          (2 * T'.weight (Fin.cast componentCount_eq.symm i) * T.weight (lastIndex T))

/-- The weight chosen by the contraction of a numerical type divides the old weight. -/
lemma contractedWeight_dvd_weight (T : NumericalType) (i : Fin (T.componentCount - 1)) :
    (if Even (T.intersection (remainingIndex T i) (lastIndex T) /
        T.weight (lastIndex T)) ∧
        Odd (T.intersection (remainingIndex T i) (lastIndex T) /
          T.weight (remainingIndex T i)) then
      T.weight (remainingIndex T i) / 2
    else T.weight (remainingIndex T i)) ∣ T.weight (remainingIndex T i) :=
  contractedWeight_dvd_weight_aux T i

/-- The contraction of a numerical type is a contraction up to weight. -/
public theorem IsContraction.isContractionUpToWeight {T T' : NumericalType}
    (hT : IsContraction T T') : IsContractionUpToWeight T T' where
  componentCount_eq := hT.componentCount_eq
  multiplicity_eq := hT.multiplicity_eq
  intersection_eq := hT.intersection_eq
  weight_dvd i := hT.weight_eq i ▸ contractedWeight_dvd_weight T i
  componentGenus_eq := hT.componentGenus_eq

/-- **The weight of the contraction of a numerical type is the largest admissible one.** For a
minus-one index `n`, the weight `w'ᵢ` chosen in Tag 0C77 is the largest positive integer dividing
`wᵢ` for which the genus formula `(wᵢ/w'ᵢ)(gᵢ - 1) + 1 + (aᵢₙ² - wₙaᵢₙ)/(2w'ᵢwₙ)` is an integer. -/
@[stacks 0CA9 "in the numerical case w'_i is the largest integer dividing w_i such that g'_i, as \
given by the formula, is an integer"]
public theorem isGreatest_contractLast_weight (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) (i : Fin (T.componentCount - 1)) :
    IsGreatest {d : ℤ | 0 < d ∧ d ∣ T.weight (remainingIndex T i) ∧
        ∃ G : ℤ, (G : ℚ) = (T.weight (remainingIndex T i) : ℚ) / d *
            ((T.componentGenus (remainingIndex T i) : ℚ) - 1) + 1 +
          ((T.intersection (remainingIndex T i) (lastIndex T) : ℚ) ^ 2 -
              T.weight (lastIndex T) * T.intersection (remainingIndex T i) (lastIndex T)) /
            (2 * d * T.weight (lastIndex T))}
      ((contractLast T h).val.weight
        (Fin.cast (contractLast T h).property.componentCount_eq.symm i)) := by
  have hT := (contractLast T h).property
  refine ⟨⟨(contractLast T h).val.weight_pos _,
      hT.isContractionUpToWeight.weight_dvd i, _, hT.componentGenus_eq i⟩, ?_⟩
  rintro d ⟨hd, hdw, hG⟩
  refine Int.le_of_dvd ((contractLast T h).val.weight_pos _) ?_
  rw [hT.weight_eq i]
  exact dvd_contractedWeight_of_isInt _ _ _ _ d (T.weight_pos _) hd
    (intersection_remaining_last_quotient T i) (intersection_remaining_own_weight_quotient T i)
    hdw hG

/-- **A component missing the minus-one component keeps its weight** under the contraction of
Tag 0C77: if `aᵢₙ = 0` then `w'ᵢ = wᵢ`. -/
public theorem contractLast_weight_eq_of_intersection_eq_zero (T : NumericalType)
    (h : IsMinusOneIndex T (lastIndex T)) (i : Fin (T.componentCount - 1))
    (hi : T.intersection (remainingIndex T i) (lastIndex T) = 0) :
    (contractLast T h).val.weight (Fin.cast (contractLast T h).property.componentCount_eq.symm i) =
      T.weight (remainingIndex T i) := by
  have hG := isGreatest_contractLast_weight T h i
  have hw := T.weight_pos (remainingIndex T i)
  refine le_antisymm (Int.le_of_dvd hw hG.1.2.1) (hG.2 ⟨hw, dvd_refl _, ?_⟩)
  refine ⟨T.componentGenus (remainingIndex T i), ?_⟩
  have hw' : (T.weight (remainingIndex T i) : ℚ) ≠ 0 := by exact_mod_cast hw.ne'
  rw [hi, div_self hw']
  push_cast
  ring

/-- **A component missing the minus-one component need not have weight dividing `wₙ`.** The
type `m = (1, 1, 1)`, `w = (1, 2, 1)`, `g = (0, 0, 0)` with intersection matrix
`((-3, 2, 1), (2, -2, 0), (1, 0, -1))` has the minus-one index `3`; the second component misses
it, its weight `2` does not divide `w₃ = 1`, and the contraction of Tag 0C77 keeps that weight. -/
public theorem exists_intersection_eq_zero_not_weight_dvd :
    ∃ (T : NumericalType) (h : IsMinusOneIndex T (lastIndex T)) (i : Fin (T.componentCount - 1)),
      T.intersection (remainingIndex T i) (lastIndex T) = 0 ∧
        ¬ T.weight (remainingIndex T i) ∣ T.weight (lastIndex T) ∧
        ¬ (contractLast T h).val.weight
            (Fin.cast (contractLast T h).property.componentCount_eq.symm i) ∣
          T.weight (lastIndex T) := by
  let A : Fin 3 → Fin 3 → ℤ := ![![-3, 2, 1], ![2, -2, 0], ![1, 0, -1]]
  let T : NumericalType :=
    { componentCount := 3
      componentCount_pos := by omega
      multiplicity := fun _ => 1
      intersection := A
      weight := ![1, 2, 1]
      componentGenus := fun _ => 0
      multiplicity_pos := fun _ => one_pos
      weight_pos := fun i => by fin_cases i <;> simp
      componentGenus_nonneg := fun _ => le_rfl
      intersection_symm := fun i j => by fin_cases i <;> fin_cases j <;> rfl
      intersection_nonneg := fun i j hij => by
        fin_cases i <;> fin_cases j <;> simp [A] at hij ⊢
      connected := by
        rintro ⟨I, ⟨i, hi⟩, hIuniv, hzero⟩
        have key : ∀ i ∈ I, ∀ j, A i j ≠ 0 → j ∈ I := fun i hi j hij => by
          by_contra hj
          exact hij (hzero i hi j hj)
        have h0 : (0 : Fin 3) ∈ I := by
          fin_cases i
          · exact hi
          · exact key _ hi 0 (by simp [A])
          · exact key _ hi 0 (by simp [A])
        refine hIuniv (Set.eq_univ_of_forall fun j => ?_)
        fin_cases j
        · exact h0
        · exact key 0 h0 _ (by simp [A])
        · exact key 0 h0 _ (by simp [A])
      intersection_mul_multiplicity := by
        intro i
        fin_cases i <;> simp [A, Fin.sum_univ_three]
      weight_dvd_intersection := by
        intro i j
        fin_cases i <;> fin_cases j <;> simp [A] }
  have h : IsMinusOneIndex T (lastIndex T) := ⟨rfl, rfl⟩
  have hi : T.intersection (remainingIndex T ⟨1, by decide⟩) (lastIndex T) = 0 := rfl
  have hw : ¬ T.weight (remainingIndex T ⟨1, by decide⟩) ∣ T.weight (lastIndex T) := by decide
  refine ⟨T, h, ⟨1, by decide⟩, hi, hw, ?_⟩
  rwa [contractLast_weight_eq_of_intersection_eq_zero T h _ hi]

/-- The weights of a contraction up to weight divide the weights of the contraction of
Tag 0C77. -/
public theorem IsContractionUpToWeight.weight_dvd_contractLast {T T' : NumericalType}
    (hT : IsContractionUpToWeight T T') (h : IsMinusOneIndex T (lastIndex T))
    (i : Fin (T.componentCount - 1)) :
    T'.weight (Fin.cast hT.componentCount_eq.symm i) ∣
      (contractLast T h).val.weight
        (Fin.cast (contractLast T h).property.componentCount_eq.symm i) := by
  rw [(contractLast T h).property.weight_eq i]
  exact dvd_contractedWeight_of_isInt _ _ _ _ _ (T.weight_pos _) (T'.weight_pos _)
    (intersection_remaining_last_quotient T i) (intersection_remaining_own_weight_quotient T i)
    (hT.weight_dvd i) ⟨_, hT.componentGenus_eq i⟩

/-- A contraction up to weight of a numerical type along a minus-one index has the same genus,
whatever its weights are. -/
public theorem IsContractionUpToWeight.genus_eq {T T' : NumericalType}
    (hT : IsContractionUpToWeight T T') (h : IsMinusOneIndex T (lastIndex T)) :
    genus T' = genus T := by
  let c : Fin (T.componentCount - 1) → Fin T'.componentCount :=
    Fin.cast hT.componentCount_eq.symm
  have hA (i : Fin (T.componentCount - 1)) : T'.intersection (c i) (c i) =
      T.intersection (remainingIndex T i) (remainingIndex T i) +
        T.intersection (remainingIndex T i) (lastIndex T) *
          (T.intersection (remainingIndex T i) (lastIndex T) / T.weight (lastIndex T)) := by
    have hq := hT.intersection_eq i i
    rw [← contractedIntersection_cast T h i i] at hq
    exact_mod_cast hq
  have hlocal (i : Fin (T.componentCount - 1)) :
      (T'.weight (c i) : ℚ) * ((T'.componentGenus (c i) : ℚ) - 1) -
          (T'.intersection (c i) (c i) : ℚ) / 2 =
        (T.weight (remainingIndex T i) : ℚ) *
            ((T.componentGenus (remainingIndex T i) : ℚ) - 1) -
          (T.intersection (remainingIndex T i) (remainingIndex T i) : ℚ) / 2 -
          (T.intersection (remainingIndex T i) (lastIndex T) : ℚ) / 2 :=
    contractedGenusLocal _ _ _ _ _ _ _ _ (T.weight_pos _) (T'.weight_pos _)
      (intersection_remaining_last_quotient T i) (intersection_remaining_own_weight_quotient T i)
      (hT.componentGenus_eq i) (hA i)
  have hweighted :
      (∑ i : Fin (T.componentCount - 1),
        (T.multiplicity (remainingIndex T i) : ℚ) *
          (T.intersection (remainingIndex T i) (lastIndex T) : ℚ)) =
        (T.multiplicity (lastIndex T) : ℚ) * T.weight (lastIndex T) := by
    exact_mod_cast lastIntersection_weighted_sum T h
  have hreindex :
      (∑ j : Fin T'.componentCount, (T'.multiplicity j : ℚ) *
          ((T'.weight j : ℚ) * ((T'.componentGenus j : ℚ) - 1) -
            (T'.intersection j j : ℚ) / 2)) =
        ∑ i : Fin (T.componentCount - 1), (T'.multiplicity (c i) : ℚ) *
          ((T'.weight (c i) : ℚ) * ((T'.componentGenus (c i) : ℚ) - 1) -
            (T'.intersection (c i) (c i) : ℚ) / 2) :=
    (Fintype.sum_equiv (finCongr hT.componentCount_eq.symm) _ _ (fun _ => rfl)).symm
  have heq : (genus T' : ℚ) = (genus T : ℚ) := by
    rw [cast_genus T', cast_genus T, hreindex, sum_remaining_add_last T]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hlocal i, hT.multiplicity_eq i])]
    rw [h.1, h.2]
    have hsplit : (∑ i : Fin (T.componentCount - 1),
        (T.multiplicity (remainingIndex T i) : ℚ) *
          ((T.weight (remainingIndex T i) : ℚ) *
              ((T.componentGenus (remainingIndex T i) : ℚ) - 1) -
            (T.intersection (remainingIndex T i) (remainingIndex T i) : ℚ) / 2 -
            (T.intersection (remainingIndex T i) (lastIndex T) : ℚ) / 2)) =
        (∑ i : Fin (T.componentCount - 1),
          (T.multiplicity (remainingIndex T i) : ℚ) *
            ((T.weight (remainingIndex T i) : ℚ) *
                ((T.componentGenus (remainingIndex T i) : ℚ) - 1) -
              (T.intersection (remainingIndex T i) (remainingIndex T i) : ℚ) / 2)) -
          (∑ i : Fin (T.componentCount - 1),
            (T.multiplicity (remainingIndex T i) : ℚ) *
              (T.intersection (remainingIndex T i) (lastIndex T) : ℚ)) / 2 := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hweighted]
    push_cast
    ring
  exact_mod_cast heq

/-- A contraction up to weight whose weights are those chosen in Tag 0C77 is the contraction of
Tag 0C77. -/
public theorem IsContractionUpToWeight.isContraction {T T' : NumericalType}
    (hT : IsContractionUpToWeight T T') (h : IsMinusOneIndex T (lastIndex T))
    (hw : ∀ i : Fin (T.componentCount - 1),
      T'.weight (Fin.cast hT.componentCount_eq.symm i) =
        if Even (T.intersection (remainingIndex T i) (lastIndex T) /
            T.weight (lastIndex T)) ∧
            Odd (T.intersection (remainingIndex T i) (lastIndex T) /
              T.weight (remainingIndex T i)) then
          T.weight (remainingIndex T i) / 2
        else
          T.weight (remainingIndex T i)) :
    IsContraction T T' where
  componentCount_eq := hT.componentCount_eq
  multiplicity_eq := hT.multiplicity_eq
  intersection_eq := hT.intersection_eq
  weight_eq := hw
  componentGenus_eq := hT.componentGenus_eq
  genus_eq := hT.genus_eq h

end AlgebraicGeometry.NumericalType
