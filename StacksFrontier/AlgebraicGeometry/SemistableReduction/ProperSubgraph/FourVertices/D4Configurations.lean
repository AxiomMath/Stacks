module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.TwoVertices
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.ThreeVertices
public import Mathlib
public import Mathlib.Data.Fin.VecNotation

/-!
# Four-vertex subgraphs: `D₄` configurations

Four minus-two indices, one of which meets the other three, give a `D₄` configuration.

## Main results

* `AlgebraicGeometry.NumericalType.exists_d4_configuration_of_four_isMinusTwoIndex`.

## References

* [Stacks Project, Tag 0C80](https://stacks.math.columbia.edu/tag/0C80)
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

/-! ### `D₄` configurations -/

private lemma sum_piecewise_four {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l : ι) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (f g h t : ι → ℚ) :
    (∑ x, if x = i then f x else if x = j then g x else
      if x = k then h x else if x = l then t x else 0) = f i + g j + h k + t l := by
  classical
  have hpt (x : ι) :
      (if x = i then f x else if x = j then g x else
        if x = k then h x else if x = l then t x else 0) =
        (if x = i then f x else 0) + (if x = j then g x else 0) +
          (if x = k then h x else 0) + (if x = l then t x else 0) := by
    split_ifs <;> simp_all
  simp_rw [hpt, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

private lemma four_coordinate_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (i j k l : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (u v w z : ℚ) :
    (fun a => if a = i then u else if a = j then v else
      if a = k then w else if a = l then z else 0) ⬝ᵥ
      (A *ᵥ fun a => if a = i then u else if a = j then v else
        if a = k then w else if a = l then z else 0) =
      u * (A i i * u + A i j * v + A i k * w + A i l * z) +
      v * (A j i * u + A j j * v + A j k * w + A j l * z) +
      w * (A k i * u + A k j * v + A k k * w + A k l * z) +
      z * (A l i * u + A l j * v + A l k * w + A l l * z) := by
  classical
  have hrow (a : ι) :
      ∑ b, (if b = i then A a b * u else if b = j then A a b * v else
        if b = k then A a b * w else if b = l then A a b * z else 0) =
      A a i * u + A a j * v + A a k * w + A a l * z :=
    sum_piecewise_four i j k l hij hik hil hjk hjl hkl
      (fun b => A a b * u) (fun b => A a b * v) (fun b => A a b * w)
      (fun b => A a b * z)
  simp only [dotProduct, Matrix.mulVec, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [sum_piecewise_four i j k l hij hik hil hjk hjl hkl
    (fun a => u * (∑ b, if b = i then A a b * u else if b = j then A a b * v else
      if b = k then A a b * w else if b = l then A a b * z else 0))
    (fun a => v * (∑ b, if b = i then A a b * u else if b = j then A a b * v else
      if b = k then A a b * w else if b = l then A a b * z else 0))
    (fun a => w * (∑ b, if b = i then A a b * u else if b = j then A a b * v else
      if b = k then A a b * w else if b = l then A a b * z else 0))
    (fun a => z * (∑ b, if b = i then A a b * u else if b = j then A a b * v else
      if b = k then A a b * w else if b = l then A a b * z else 0))]
  simp_rw [hrow]

/-- A sum of a function defined piecewise at five distinct points `i, j, k, l, m` and zero
elsewhere is the sum of its five values. -/
public lemma sum_piecewise_five {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j k l m : ι) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (f g h t s : ι → ℚ) :
    (∑ x, if x = i then f x else if x = j then g x else
      if x = k then h x else if x = l then t x else if x = m then s x else 0) =
      f i + g j + h k + t l + s m := by
  classical
  have hpt (x : ι) :
      (if x = i then f x else if x = j then g x else
        if x = k then h x else if x = l then t x else if x = m then s x else 0) =
        (if x = i then f x else 0) + (if x = j then g x else 0) +
          (if x = k then h x else 0) + (if x = l then t x else 0) +
          (if x = m then s x else 0) := by
    split_ifs <;> simp_all
  simp_rw [hpt, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

/-- The quadratic form of a matrix `A` on a vector supported on five distinct coordinates, expanded
in those coordinates. -/
public lemma five_coordinate_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (i j k l m : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (him : i ≠ m)
    (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (u v w z y : ℚ) :
    (fun a => if a = i then u else if a = j then v else if a = k then w else
      if a = l then z else if a = m then y else 0) ⬝ᵥ
      (A *ᵥ fun a => if a = i then u else if a = j then v else if a = k then w else
        if a = l then z else if a = m then y else 0) =
      u * (A i i * u + A i j * v + A i k * w + A i l * z + A i m * y) +
      v * (A j i * u + A j j * v + A j k * w + A j l * z + A j m * y) +
      w * (A k i * u + A k j * v + A k k * w + A k l * z + A k m * y) +
      z * (A l i * u + A l j * v + A l k * w + A l l * z + A l m * y) +
      y * (A m i * u + A m j * v + A m k * w + A m l * z + A m m * y) := by
  classical
  have hrow (a : ι) :
      ∑ b, (if b = i then A a b * u else if b = j then A a b * v else
        if b = k then A a b * w else if b = l then A a b * z else
          if b = m then A a b * y else 0) =
        A a i * u + A a j * v + A a k * w + A a l * z + A a m * y :=
    sum_piecewise_five i j k l m hij hik hil him hjk hjl hjm hkl hkm hlm
      (fun b => A a b * u) (fun b => A a b * v) (fun b => A a b * w)
      (fun b => A a b * z) (fun b => A a b * y)
  simp only [dotProduct, Matrix.mulVec, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [sum_piecewise_five i j k l m hij hik hil him hjk hjl hjm hkl hkm hlm
    (fun a => u * (∑ b, if b = i then A a b * u else if b = j then A a b * v else
      if b = k then A a b * w else if b = l then A a b * z else
        if b = m then A a b * y else 0))
    (fun a => v * (∑ b, if b = i then A a b * u else if b = j then A a b * v else
      if b = k then A a b * w else if b = l then A a b * z else
        if b = m then A a b * y else 0))
    (fun a => w * (∑ b, if b = i then A a b * u else if b = j then A a b * v else
      if b = k then A a b * w else if b = l then A a b * z else
        if b = m then A a b * y else 0))
    (fun a => z * (∑ b, if b = i then A a b * u else if b = j then A a b * v else
      if b = k then A a b * w else if b = l then A a b * z else
        if b = m then A a b * y else 0))
    (fun a => y * (∑ b, if b = i then A a b * u else if b = j then A a b * v else
      if b = k then A a b * w else if b = l then A a b * z else
        if b = m then A a b * y else 0))]
  simp_rw [hrow]

private lemma leaves_disjoint (T : NumericalType)
    (hn : 3 < T.componentCount) (i j k : Fin T.componentCount)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hk : IsMinusTwoIndex T k)
    (hijA : T.intersection i j ≠ 0) (hikA : T.intersection i k ≠ 0) :
    T.intersection j k = 0 := by
  obtain ⟨v, hv, hrange, hconfig⟩ :=
    exists_ordering_of_three_minus_two_indices T hn i j k hi hj hk
      hij hik hjk (Or.inl ⟨hijA, hikA⟩)
  have h02 : T.intersection (v 0) (v 2) = 0 := by
    rcases hconfig with
      ⟨w, _, _, _, _, _, hzero, _, _, _, _, _, _, _, _⟩ |
      ⟨w, _, _, _, _, _, hzero, _, _, _, _, _, _, _, _⟩ |
      ⟨w, _, _, _, _, _, hzero, _, _, _, _, _, _, _, _⟩
    · exact hzero
    · exact hzero
    · exact hzero
  have h20 : T.intersection (v 2) (v 0) = 0 := by
    rw [T.intersection_symm]
    exact h02
  obtain ⟨p, hp⟩ : ∃ p, v p = i := Set.mem_range.mp (by rw [hrange]; simp)
  obtain ⟨q, hq⟩ : ∃ q, v q = j := Set.mem_range.mp (by rw [hrange]; simp)
  obtain ⟨r, hr⟩ : ∃ r, v r = k := Set.mem_range.mp (by rw [hrange]; simp)
  fin_cases p <;> fin_cases q <;> fin_cases r <;>
    simp_all [T.intersection_symm]

private lemma edge_square_classification (T : NumericalType)
    (hn : 2 < T.componentCount) (i j : Fin T.componentCount)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (ha : 0 < T.intersection i j) :
    ∃ p : ℤ, (p = 1 ∨ p = 2 ∨ p = 3) ∧
      (T.intersection i j : ℚ) ^ 2 =
        (p : ℚ) * (T.weight i : ℚ) * (T.weight j : ℚ) ∧
      (p = 1 → T.weight i = T.weight j ∧ T.intersection i j = T.weight i) := by
  have key : ∀ a b, IsTwoVertexConfiguration T a b → ∃ p : ℤ, (p = 1 ∨ p = 2 ∨ p = 3) ∧
      (T.intersection a b : ℚ) ^ 2 = (p : ℚ) * (T.weight a : ℚ) * (T.weight b : ℚ) ∧
      (p = 1 → T.weight a = T.weight b ∧ T.intersection a b = T.weight a) := by
    rintro a b (⟨w, hwa, hwb, _, hab, _⟩ | ⟨w, hwa, hwb, _, hab, _⟩ | ⟨w, hwa, hwb, _, hab, _⟩)
    · refine ⟨1, Or.inl rfl, ?_, fun _ => ⟨hwa.trans hwb.symm, hab.trans hwa.symm⟩⟩
      exact_mod_cast (by rw [hab, hwa, hwb]; ring : T.intersection a b ^ 2 = 1 * T.weight a *
        T.weight b)
    · refine ⟨2, Or.inr (Or.inl rfl), ?_, fun h => by norm_num at h⟩
      exact_mod_cast (by rw [hab, hwa, hwb]; ring : T.intersection a b ^ 2 = 2 * T.weight a *
        T.weight b)
    · refine ⟨3, Or.inr (Or.inr rfl), ?_, fun h => by norm_num at h⟩
      exact_mod_cast (by rw [hab, hwa, hwb]; ring : T.intersection a b ^ 2 = 3 * T.weight a *
        T.weight b)
  rcases isTwoVertexConfiguration_or_swap T hn i j hi hj ha with h | h
  · exact key i j h
  · obtain ⟨p, hp, hsq, hprofile⟩ := key j i h
    refine ⟨p, hp, ?_, fun hp1 => ?_⟩
    · rw [T.intersection_symm, hsq]; ring
    · obtain ⟨hw, hint⟩ := hprofile hp1
      exact ⟨hw.symm, by rw [T.intersection_symm, hint, hw]⟩

private lemma multiplicity_row_subset_bound (T : NumericalType)
    (i : Fin T.componentCount) (S : Finset (Fin T.componentCount))
    (hS : S ⊆ Finset.univ.erase i)
    (hii : T.intersection i i = -2 * T.weight i) :
    ∑ j ∈ S, (T.intersection i j : ℚ) * (T.multiplicity j : ℚ) ≤
      2 * (T.weight i : ℚ) * (T.multiplicity i : ℚ) := by
  classical
  have hbalance := cast_intersection_balance T i
  rw [← Finset.add_sum_erase (s := Finset.univ)
    (f := fun j => (T.intersection i j : ℚ) * (T.multiplicity j : ℚ))
    (a := i) (by simp)] at hbalance
  have hdiag : (T.intersection i i : ℚ) = -2 * (T.weight i : ℚ) := by
    exact_mod_cast hii
  have hsum :
      ∑ j ∈ Finset.univ.erase i,
        (T.intersection i j : ℚ) * (T.multiplicity j : ℚ) =
          2 * (T.weight i : ℚ) * (T.multiplicity i : ℚ) := by
    rw [hdiag] at hbalance
    nlinarith
  calc
    ∑ j ∈ S, (T.intersection i j : ℚ) * (T.multiplicity j : ℚ) ≤
        ∑ j ∈ Finset.univ.erase i,
          (T.intersection i j : ℚ) * (T.multiplicity j : ℚ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro j hj hjS
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      exact mul_nonneg
        (by exact_mod_cast T.intersection_nonneg i j hji.symm)
        (by exact_mod_cast (le_of_lt (T.multiplicity_pos j)))
    _ = 2 * (T.weight i : ℚ) * (T.multiplicity i : ℚ) := hsum

/-- A minus-two index `j` of the same weight as a neighbour `i`, with `T.intersection j i` equal to
that weight, has multiplicity at least half that of `i`. -/
private lemma multiplicity_le_two_mul_of_leaf (T : NumericalType) (i j : Fin T.componentCount)
    (hij : i ≠ j) (hjj : T.intersection j j = -2 * T.weight j)
    (hw : T.weight j = T.weight i) (hji : T.intersection j i = T.weight i) :
    T.multiplicity i ≤ 2 * T.multiplicity j := by
  have hrow := multiplicity_row_subset_bound T j {i}
    (by simpa using Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) hjj
  have hwi : (0 : ℚ) < T.weight i := by exact_mod_cast T.weight_pos i
  rw [Finset.sum_singleton, hji, hw] at hrow
  exact_mod_cast le_of_mul_le_mul_left (by linarith : (T.weight i : ℚ) * T.multiplicity i ≤
    T.weight i * (2 * T.multiplicity j)) hwi

/-- Three edge types, each `1`, `2` or `3`, summing to less than `4`, are all
`1`. Pulled out of `exists_d4_configuration_of_four_isMinusTwoIndex` because
`omega` there was deciding this against that proof's whole mixed `ℚ`/`ℤ`
context, which the profiler showed costing 32 of the declaration's 53 seconds;
given just these four facts it is instant. -/
private lemma eq_one_of_three_edge_types_sum_lt_four {p q r : ℤ}
    (hp : p = 1 ∨ p = 2 ∨ p = 3) (hq : q = 1 ∨ q = 2 ∨ q = 3)
    (hr : r = 1 ∨ r = 2 ∨ r = 3) (h : p + q + r < 4) :
    p = 1 ∧ q = 1 ∧ r = 1 := by omega

/-- Four distinct minus-two components, with one component meeting the other
three, form a D4 configuration. -/
@[stacks 0C80]
public lemma exists_d4_configuration_of_four_isMinusTwoIndex
    (T : NumericalType) (hn : 4 < T.componentCount)
    (i j k l : Fin T.componentCount)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hk : IsMinusTwoIndex T k) (hl : IsMinusTwoIndex T l)
    (haij : T.intersection i j ≠ 0)
    (haik : T.intersection i k ≠ 0)
    (hail : T.intersection i l ≠ 0) :
    ∃ w : ℤ,
      0 < w ∧
      T.weight i = w ∧ T.weight j = w ∧
      T.weight k = w ∧ T.weight l = w ∧
      T.intersection i i = -2 * w ∧
      T.intersection j j = -2 * w ∧
      T.intersection k k = -2 * w ∧
      T.intersection l l = -2 * w ∧
      T.intersection i j = w ∧ T.intersection j i = w ∧
      T.intersection i k = w ∧ T.intersection k i = w ∧
      T.intersection i l = w ∧ T.intersection l i = w ∧
      T.intersection j k = 0 ∧ T.intersection k j = 0 ∧
      T.intersection j l = 0 ∧ T.intersection l j = 0 ∧
      T.intersection k l = 0 ∧ T.intersection l k = 0 ∧
      2 * T.multiplicity i ≥
        T.multiplicity j + T.multiplicity k + T.multiplicity l ∧
      2 * T.multiplicity j ≥ T.multiplicity i ∧
      2 * T.multiplicity k ≥ T.multiplicity i ∧
      2 * T.multiplicity l ≥ T.multiplicity i ∧
      T.multiplicity j ≤ T.multiplicity i ∧
      T.multiplicity k ≤ T.multiplicity i ∧
      T.multiplicity l ≤ T.multiplicity i := by
  classical
  have hii := hi.2
  have hjj := hj.2
  have hkk := hk.2
  have hll := hl.2
  have hjk0 := leaves_disjoint T (by omega) i j k hij hik hjk hi hj hk haij haik
  have hjl0 := leaves_disjoint T (by omega) i j l hij hil hjl hi hj hl haij hail
  have hkl0 := leaves_disjoint T (by omega) i k l hik hil hkl hi hk hl haik hail
  have hkj0 : T.intersection k j = 0 := (T.intersection_symm k j).trans hjk0
  have hlj0 : T.intersection l j = 0 := (T.intersection_symm l j).trans hjl0
  have hlk0 : T.intersection l k = 0 := (T.intersection_symm l k).trans hkl0
  obtain ⟨pij, hpij, hsqij, hprofileij⟩ :=
    edge_square_classification T (by omega) i j hi hj
      ((T.intersection_nonneg i j hij).lt_of_ne (Ne.symm haij))
  obtain ⟨pik, hpik, hsqik, hprofileik⟩ :=
    edge_square_classification T (by omega) i k hi hk
      ((T.intersection_nonneg i k hik).lt_of_ne (Ne.symm haik))
  obtain ⟨pil, hpil, hsqil, hprofileil⟩ :=
    edge_square_classification T (by omega) i l hi hl
      ((T.intersection_nonneg i l hil).lt_of_ne (Ne.symm hail))
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun a b => (T.intersection a b : ℚ)
  let m : Fin T.componentCount → ℚ := fun a => (T.multiplicity a : ℚ)
  let wi : ℚ := (T.weight i : ℚ)
  let wj : ℚ := (T.weight j : ℚ)
  let wk : ℚ := (T.weight k : ℚ)
  let wl : ℚ := (T.weight l : ℚ)
  let aij : ℚ := (T.intersection i j : ℚ)
  let aik : ℚ := (T.intersection i k : ℚ)
  let ail : ℚ := (T.intersection i l : ℚ)
  let mj : ℚ := (T.multiplicity j : ℚ)
  let mk : ℚ := (T.multiplicity k : ℚ)
  let ml : ℚ := (T.multiplicity l : ℚ)
  let mi : ℚ := (T.multiplicity i : ℚ)
  have hAsymm : A.IsSymm := by
    ext a b
    change (T.intersection b a : ℚ) = (T.intersection a b : ℚ)
    exact_mod_cast (T.intersection_symm a b).symm
  have hAoff : ∀ a b, a ≠ b → 0 ≤ A a b := by
    intro a b hab
    change 0 ≤ (T.intersection a b : ℚ)
    exact_mod_cast T.intersection_nonneg a b hab
  have hmpos : ∀ a, 0 < m a := by
    intro a
    change 0 < (T.multiplicity a : ℚ)
    exact_mod_cast T.multiplicity_pos a
  have hAm : A *ᵥ m = 0 := by
    ext a
    change ∑ b, (T.intersection a b : ℚ) * (T.multiplicity b : ℚ) = 0
    exact cast_intersection_balance T a
  have hconn : ∀ I : Set (Fin T.componentCount), I.Nonempty → I ≠ Set.univ →
      ¬ ∀ a ∈ I, ∀ b ∉ I, A a b = 0 := by
    intro I hI hIne hcross
    apply T.connected
    refine ⟨I, hI, hIne, ?_⟩
    intro a ha b hb
    have hab := hcross a ha b hb
    change (T.intersection a b : ℚ) = 0 at hab
    exact_mod_cast hab
  have hwpos : ∀ a, 0 < (T.weight a : ℚ) := fun a => by exact_mod_cast T.weight_pos a
  have hwi : 0 < wi := hwpos i
  have hwj : 0 < wj := hwpos j
  have hwk : 0 < wk := hwpos k
  have hwl : 0 < wl := hwpos l
  have hsqijQ : aij ^ 2 = (pij : ℚ) * wi * wj := by
    simpa [aij, wi, wj] using hsqij
  have hsqikQ : aik ^ 2 = (pik : ℚ) * wi * wk := by
    simpa [aik, wi, wk] using hsqik
  have hsqilQ : ail ^ 2 = (pil : ℚ) * wi * wl := by
    simpa [ail, wi, wl] using hsqil
  let x : Fin T.componentCount → ℚ := fun a =>
    if a = i then 1 else if a = j then aij / (2 * wj) else
      if a = k then aik / (2 * wk) else if a = l then ail / (2 * wl) else 0
  have hquadRaw :
      x ⬝ᵥ (A *ᵥ x) =
        -2 * wi + aij ^ 2 / (2 * wj) + aik ^ 2 / (2 * wk) + ail ^ 2 / (2 * wl) := by
    have hquad := four_coordinate_quadratic A i j k l hij hik hil hjk hjl hkl
      (1 : ℚ) (aij / (2 * wj)) (aik / (2 * wk)) (ail / (2 * wl))
    have hdiagQ : ∀ a, T.intersection a a = -2 * T.weight a → A a a = -2 * (T.weight a : ℚ) :=
      fun a h => by
        change (T.intersection a a : ℚ) = _
        exact_mod_cast h
    have hzeroQ : ∀ a b, T.intersection a b = 0 → A a b = 0 := fun a b h => by simp [A, h]
    have hiiQ : A i i = -2 * wi := hdiagQ i hii
    have hjjQ : A j j = -2 * wj := hdiagQ j hjj
    have hkkQ : A k k = -2 * wk := hdiagQ k hkk
    have hllQ : A l l = -2 * wl := hdiagQ l hll
    have hijQ : A i j = aij := rfl
    have hikQ : A i k = aik := rfl
    have hilQ : A i l = ail := rfl
    have hjiQ : A j i = aij := hAsymm.apply i j
    have hkiQ : A k i = aik := hAsymm.apply i k
    have hliQ : A l i = ail := hAsymm.apply i l
    have hjkQ := hzeroQ j k hjk0
    have hjlQ := hzeroQ j l hjl0
    have hklQ := hzeroQ k l hkl0
    have hkjQ := hzeroQ k j hkj0
    have hljQ := hzeroQ l j hlj0
    have hlkQ := hzeroQ l k hlk0
    calc
      _ = (1 : ℚ) * (A i i * 1 + A i j * (aij / (2 * wj)) +
            A i k * (aik / (2 * wk)) + A i l * (ail / (2 * wl))) +
          (aij / (2 * wj)) * (A j i * 1 + A j j * (aij / (2 * wj)) +
            A j k * (aik / (2 * wk)) + A j l * (ail / (2 * wl))) +
          (aik / (2 * wk)) * (A k i * 1 + A k j * (aij / (2 * wj)) +
            A k k * (aik / (2 * wk)) + A k l * (ail / (2 * wl))) +
          (ail / (2 * wl)) * (A l i * 1 + A l j * (aij / (2 * wj)) +
            A l k * (aik / (2 * wk)) + A l l * (ail / (2 * wl))) := by
              simpa using hquad
      _ = -2 * wi + aij ^ 2 / (2 * wj) + aik ^ 2 / (2 * wk) +
          ail ^ 2 / (2 * wl) := by
        simp only [hiiQ, hjjQ, hkkQ, hllQ, hijQ, hikQ, hilQ, hjiQ, hkiQ,
          hliQ, hjkQ, hjlQ, hklQ, hkjQ, hljQ, hlkQ]
        field_simp [ne_of_gt hwj, ne_of_gt hwk, ne_of_gt hwl]
        ring
  have hterm : ∀ (a w p : ℚ), 0 < w → a ^ 2 = p * wi * w → a ^ 2 / (2 * w) = p * wi / 2 := by
    intro a w p hw h
    field_simp
    nlinarith [h]
  have htermJ := hterm _ _ _ hwj hsqijQ
  have htermK := hterm _ _ _ hwk hsqikQ
  have htermL := hterm _ _ _ hwl hsqilQ
  have hxquad : x ⬝ᵥ (A *ᵥ x) =
        (wi / 2) * ((pij : ℚ) + (pik : ℚ) + (pil : ℚ) - 4) := by
    rw [hquadRaw, htermJ, htermK, htermL]
    ring
  have hxle : x ⬝ᵥ (A *ᵥ x) ≤ 0 :=
    dotProduct_mulVec_nonpos_of_positive_kernel hAsymm hAoff hmpos hAm x
  let v4 : Fin 4 → Fin T.componentCount := fun t =>
    if t = 0 then i else if t = 1 then j else if t = 2 then k else l
  have hv4 : Function.Injective v4 := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [v4, hij, hij.symm, hik, hik.symm, hil, hil.symm,
        hjk, hjk.symm, hjl, hjl.symm, hkl, hkl.symm] at hab ⊢
  have hnotSurj : ¬ Function.Surjective v4 := by
    intro hsurj
    have hcard := Fintype.card_congr (Equiv.ofBijective v4 ⟨hv4, hsurj⟩)
    simp at hcard
    omega
  obtain ⟨z, hz⟩ : ∃ z : Fin T.componentCount, z ∉ Set.range v4 := by
    by_contra h
    exact hnotSurj fun z => Classical.byContradiction fun hz => h ⟨z, hz⟩
  have hzi : z ≠ i := fun h => hz ⟨0, by simp [v4, h]⟩
  have hzj : z ≠ j := fun h => hz ⟨1, by simp [v4, h]⟩
  have hzk : z ≠ k := fun h => hz ⟨2, by simp [v4, h]⟩
  have hzl : z ≠ l := fun h => hz ⟨3, by simp [v4, h]⟩
  have hxz : x z = 0 := by simp [x, hzi, hzj, hzk, hzl]
  have hxne : x ⬝ᵥ (A *ᵥ x) ≠ 0 := by
    intro hzero
    obtain ⟨c, hscale⟩ :=
      (dotProduct_mulVec_eq_zero_iff_of_positive_kernel hAsymm hAoff hmpos hAm hconn
        (x := x)).mp hzero
    have hcz := congrFun hscale z
    change x z = c * m z at hcz
    rw [hxz] at hcz
    have hc : c = 0 := by nlinarith [hmpos z]
    have hci := congrFun hscale i
    have hxi : x i = 1 := by simp [x]
    change x i = c * m i at hci
    rw [hxi, hc] at hci
    norm_num at hci
  have hxlt : x ⬝ᵥ (A *ᵥ x) < 0 := lt_of_le_of_ne hxle hxne
  have hsumLt : (pij : ℚ) + (pik : ℚ) + (pil : ℚ) < 4 := by
    rw [hxquad] at hxlt
    have hhalf : 0 < wi / 2 := by positivity
    nlinarith
  have hsumInt : pij + pik + pil < 4 := by exact_mod_cast hsumLt
  have ⟨hpijOne, hpikOne, hpilOne⟩ :=
    eq_one_of_three_edge_types_sum_lt_four hpij hpik hpil hsumInt
  obtain ⟨hweightj, hinterij⟩ := hprofileij hpijOne
  obtain ⟨hweightk, hinterik⟩ := hprofileik hpikOne
  obtain ⟨hweightl, hinteril⟩ := hprofileil hpilOne
  have hjj' : T.intersection j j = -2 * T.weight i := by rw [hjj, hweightj]
  have hkk' : T.intersection k k = -2 * T.weight i := by rw [hkk, hweightk]
  have hll' : T.intersection l l = -2 * T.weight i := by rw [hll, hweightl]
  have hji' : T.intersection j i = T.weight i := by
    rw [T.intersection_symm, hinterij]
  have hki' : T.intersection k i = T.weight i := by
    rw [T.intersection_symm, hinterik]
  have hli' : T.intersection l i = T.weight i := by
    rw [T.intersection_symm, hinteril]
  let S : Finset (Fin T.componentCount) := {j, k, l}
  have hS : S ⊆ Finset.univ.erase i := by
    intro a ha
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr ⟨Ne.symm hil, Finset.mem_univ _⟩
  have hrowI := multiplicity_row_subset_bound T i S hS hii
  have hrowI' :
      (T.weight i : ℚ) * ((T.multiplicity j : ℚ) +
        (T.multiplicity k : ℚ) + (T.multiplicity l : ℚ)) ≤
        2 * (T.weight i : ℚ) * (T.multiplicity i : ℚ) := by
    simpa [S, hinterij, hinterik, hinteril, Finset.sum_insert, hjk, hkl, hjl,
      Finset.sum_singleton, mul_add, add_assoc] using hrowI
  have hmultI : 2 * (T.multiplicity i : ℚ) ≥
      (T.multiplicity j : ℚ) + (T.multiplicity k : ℚ) +
        (T.multiplicity l : ℚ) := by
    apply le_of_mul_le_mul_left ?_ hwi
    calc
      (T.weight i : ℚ) * ((T.multiplicity j : ℚ) +
          (T.multiplicity k : ℚ) + (T.multiplicity l : ℚ)) ≤
          2 * (T.weight i : ℚ) * (T.multiplicity i : ℚ) := hrowI'
      _ = (T.weight i : ℚ) * (2 * (T.multiplicity i : ℚ)) := by ring
  have hmultI' : 2 * T.multiplicity i ≥
      T.multiplicity j + T.multiplicity k + T.multiplicity l := by
    exact_mod_cast hmultI
  have hmultJ' := multiplicity_le_two_mul_of_leaf T i j hij hjj hweightj.symm hji'
  have hmultK' := multiplicity_le_two_mul_of_leaf T i k hik hkk hweightk.symm hki'
  have hmultL' := multiplicity_le_two_mul_of_leaf T i l hil hll hweightl.symm hli'
  refine ⟨T.weight i, T.weight_pos i, rfl, hweightj.symm, hweightk.symm,
    hweightl.symm, hii, hjj', hkk', hll', hinterij, hji', hinterik, hki',
    hinteril, hli', hjk0, hkj0, hjl0, hlj0, hkl0, hlk0, hmultI', hmultJ',
    hmultK', hmultL', ?_, ?_, ?_⟩ <;> omega

end AlgebraicGeometry.NumericalType
