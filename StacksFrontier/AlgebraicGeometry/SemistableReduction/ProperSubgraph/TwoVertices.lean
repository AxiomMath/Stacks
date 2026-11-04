module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import Mathlib

/-!
# Two-vertex subgraphs

Two distinct minus-two indices with nonzero intersection form, after possibly
swapping them, one of the configurations `A₂`, `B₂` or `G₂`: the product of the
edge intersection numbers is one, two or three.

## Main definitions

* `AlgebraicGeometry.NumericalType.IsA2Pair`,
  `AlgebraicGeometry.NumericalType.IsB2Pair`,
  `AlgebraicGeometry.NumericalType.IsG2Pair` and
  `AlgebraicGeometry.NumericalType.IsTwoVertexConfiguration`.

## Main results

* `AlgebraicGeometry.NumericalType.isTwoVertexConfiguration_or_swap`.

## References

* [Stacks Project, Tag 0C7M](https://stacks.math.columbia.edu/tag/0C7M)
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

/-- The ordered rank-two configuration of type `A₂`. -/
public abbrev IsA2Pair (T : NumericalType)
    (i j : Fin T.componentCount) : Prop :=
  ∃ w : ℤ,
    T.weight i = w ∧
      T.weight j = w ∧
      T.intersection i i = -2 * w ∧
      T.intersection i j = w ∧
      T.intersection j i = w ∧
      T.intersection j j = -2 * w ∧
      T.multiplicity j ≤ 2 * T.multiplicity i ∧
      T.multiplicity i ≤ 2 * T.multiplicity j

/-- The ordered rank-two configuration of type `B₂`, with the shorter root first. -/
public abbrev IsB2Pair (T : NumericalType)
    (i j : Fin T.componentCount) : Prop :=
  ∃ w : ℤ,
    T.weight i = w ∧
      T.weight j = 2 * w ∧
      T.intersection i i = -2 * w ∧
      T.intersection i j = 2 * w ∧
      T.intersection j i = 2 * w ∧
      T.intersection j j = -4 * w ∧
      T.multiplicity j ≤ T.multiplicity i ∧
      T.multiplicity i ≤ 2 * T.multiplicity j

/-- The ordered rank-two configuration of type `G₂`, with the shorter root first. -/
public abbrev IsG2Pair (T : NumericalType)
    (i j : Fin T.componentCount) : Prop :=
  ∃ w : ℤ,
    T.weight i = w ∧
      T.weight j = 3 * w ∧
      T.intersection i i = -2 * w ∧
      T.intersection i j = 3 * w ∧
      T.intersection j i = 3 * w ∧
      T.intersection j j = -6 * w ∧
      3 * T.multiplicity j ≤ 2 * T.multiplicity i ∧
      T.multiplicity i ≤ 2 * T.multiplicity j

/-- One of the three possible ordered two-vertex configurations. -/
public abbrev IsTwoVertexConfiguration (T : NumericalType)
    (i j : Fin T.componentCount) : Prop :=
  IsA2Pair T i j ∨ IsB2Pair T i j ∨ IsG2Pair T i j

/-- A sum over `ι` of a function supported on two distinct points `a` and `b`, given by `f`
at `a` and by `g` at `b`, equals `f a + g b`. -/
public lemma sum_piecewise_two {ι R : Type*} [Fintype ι]
    [DecidableEq ι] [AddCommMonoid R]
    (a b : ι) (hab : a ≠ b) (f g : ι → R) :
    (∑ x, if x = a then f x else if x = b then g x else 0) = f a + g b := by
  have hpt (x : ι) : (if x = a then f x else if x = b then g x else 0) =
      (if x = a then f x else 0) + (if x = b then g x else 0) := by
    by_cases hxa : x = a
    · subst x
      simp [hab]
    · by_cases hxb : x = b
      · subst x
        simp [Ne.symm hab]
      · simp [hxa, hxb]
  simp_rw [hpt, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

private lemma two_coordinate_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℚ) (i j : ι) (hij : i ≠ j) (u v : ℚ) :
    (fun k => if k = i then u else if k = j then v else 0) ⬝ᵥ
      (A *ᵥ fun k => if k = i then u else if k = j then v else 0) =
      u * (A i i * u + A i j * v) + v * (A j i * u + A j j * v) := by
  have hrow (x : ι) :
      ∑ k, (if k = i then A x k * u else if k = j then A x k * v else 0) =
        A x i * u + A x j * v :=
    sum_piecewise_two i j hij (fun k => A x k * u) (fun k => A x k * v)
  simp only [dotProduct, Matrix.mulVec, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [sum_piecewise_two i j hij
      (fun x => u * (∑ k, if k = i then A x k * u else if k = j then A x k * v else 0))
      (fun x => v * (∑ k, if k = i then A x k * u else if k = j then A x k * v else 0))]
  simp_rw [hrow]

/-- The balancing identity `∑ⱼ aᵢⱼ mⱼ = 0` of a numerical type, cast to `ℚ`. -/
public lemma cast_intersection_balance (T : NumericalType) (i : Fin T.componentCount) :
    ∑ j, (T.intersection i j : ℚ) * (T.multiplicity j : ℚ) = 0 := by
  exact_mod_cast T.intersection_mul_multiplicity i

private lemma multiplicity_row_bound_singleton (T : NumericalType)
    (i j : Fin T.componentCount) (hij : i ≠ j)
    (hii : T.intersection i i = -2 * T.weight i) :
    (T.intersection i j : ℚ) * (T.multiplicity j : ℚ) ≤
      2 * (T.weight i : ℚ) * (T.multiplicity i : ℚ) := by
  have hbalance := cast_intersection_balance T i
  rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun k => (T.intersection i k : ℚ) * (T.multiplicity k : ℚ))
      (a := i) (by simp)] at hbalance
  have hsum : (T.intersection i j : ℚ) * (T.multiplicity j : ℚ) ≤
      ∑ k ∈ Finset.univ.erase i,
        (T.intersection i k : ℚ) * (T.multiplicity k : ℚ) := by
    refine Finset.single_le_sum
      (f := fun k => (T.intersection i k : ℚ) * (T.multiplicity k : ℚ))
      (s := Finset.univ.erase i) (fun k hk => ?_)
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩)
    exact mul_nonneg
      (by exact_mod_cast T.intersection_nonneg i k (Finset.mem_erase.mp hk).1.symm)
      (by exact_mod_cast (T.multiplicity_pos k).le)
  rw [show (T.intersection i i : ℚ) = -2 * (T.weight i : ℚ) by exact_mod_cast hii] at hbalance
  linarith

private lemma positive_integer_factors_lt_four {p q : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p * q < 4) :
    (p = 1 ∧ q = 1) ∨ (p = 2 ∧ q = 1) ∨ (p = 1 ∧ q = 2) ∨
      (p = 3 ∧ q = 1) ∨ (p = 1 ∧ q = 3) := by
  have : p ≤ 3 := by nlinarith
  have : q ≤ 3 := by nlinarith
  interval_cases p <;> interval_cases q <;> omega

/-- Numerical consequences for two minus-two indices `i`, `j` whose intersection number is
`c` times the weight of `i` and equals the weight of `j`. -/
private lemma two_vertex_relations (T : NumericalType) (i j : Fin T.componentCount)
    (hne : i ≠ j) (hii : T.intersection i i = -2 * T.weight i)
    (hjj : T.intersection j j = -2 * T.weight j) (c : ℤ)
    (h1 : T.intersection i j = c * T.weight i) (h2 : T.intersection i j = T.weight j) :
    T.weight j = c * T.weight i ∧ T.intersection j i = c * T.weight i ∧
      T.intersection j j = -2 * c * T.weight i ∧
      c * T.multiplicity j ≤ 2 * T.multiplicity i ∧ T.multiplicity i ≤ 2 * T.multiplicity j := by
  have hji : T.intersection j i = T.intersection i j := (T.intersection_symm i j).symm
  have hw : T.weight j = c * T.weight i := h2.symm.trans h1
  have hrowI := multiplicity_row_bound_singleton T i j hne hii
  have hrowJ := multiplicity_row_bound_singleton T j i hne.symm hjj
  rw [hji, show (T.intersection i j : ℚ) = T.weight j by exact_mod_cast h2] at hrowJ
  rw [show (T.intersection i j : ℚ) = c * T.weight i by exact_mod_cast h1] at hrowI
  have hwi : (0 : ℚ) < T.weight i := by exact_mod_cast T.weight_pos i
  have hwj : (0 : ℚ) < T.weight j := by exact_mod_cast T.weight_pos j
  refine ⟨hw, hji.trans h1, by rw [hjj, hw]; ring, ?_, ?_⟩
  · have : (c : ℚ) * T.multiplicity j ≤ 2 * T.multiplicity i :=
      le_of_mul_le_mul_left (by nlinarith) hwi
    exact_mod_cast this
  · have : (T.multiplicity i : ℚ) ≤ 2 * T.multiplicity j :=
      le_of_mul_le_mul_left (by nlinarith) hwj
    exact_mod_cast this

/-- A positively intersecting pair of minus-two indices in a numerical type with
more than two components has type `A₂`, `B₂`, or `G₂`, up to exchanging the
indices. -/
@[stacks 0C7M]
public lemma isTwoVertexConfiguration_or_swap (T : NumericalType)
    (hn : 2 < T.componentCount) (i j : Fin T.componentCount)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hij : 0 < T.intersection i j) :
    IsTwoVertexConfiguration T i j ∨ IsTwoVertexConfiguration T j i := by
  classical
  rcases hi with ⟨_, hii⟩
  rcases hj with ⟨_, hjj⟩
  have hne : i ≠ j := by
    rintro rfl
    linarith [T.weight_pos i]
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun k l => (T.intersection k l : ℚ)
  let m : Fin T.componentCount → ℚ := fun k => (T.multiplicity k : ℚ)
  have hA : A.IsSymm := by
    ext k l
    change (T.intersection l k : ℚ) = (T.intersection k l : ℚ)
    exact_mod_cast (T.intersection_symm k l).symm
  have hoff : ∀ k l, k ≠ l → 0 ≤ A k l := by
    intro k l hkl
    change 0 ≤ (T.intersection k l : ℚ)
    exact_mod_cast T.intersection_nonneg k l hkl
  have hmpos : ∀ k, 0 < m k := by
    intro k
    change 0 < (T.multiplicity k : ℚ)
    exact_mod_cast T.multiplicity_pos k
  have hAm : A *ᵥ m = 0 := by
    ext k
    exact cast_intersection_balance T k
  have hconn : ∀ I : Set (Fin T.componentCount), I.Nonempty → I ≠ Set.univ →
      ¬ ∀ k ∈ I, ∀ l ∉ I, A k l = 0 := by
    intro I hI hIne hcross
    refine T.connected ⟨I, hI, hIne, fun k hk l hl => ?_⟩
    have h := hcross k hk l hl
    change (T.intersection k l : ℚ) = 0 at h
    exact_mod_cast h
  let wi : ℚ := (T.weight i : ℚ)
  let wj : ℚ := (T.weight j : ℚ)
  let a : ℚ := (T.intersection i j : ℚ)
  have hwi : 0 < wi := by
    change 0 < (T.weight i : ℚ)
    exact_mod_cast T.weight_pos i
  have hwj : 0 < wj := by
    change 0 < (T.weight j : ℚ)
    exact_mod_cast T.weight_pos j
  have ha : 0 < a := by
    change 0 < (T.intersection i j : ℚ)
    exact_mod_cast hij
  let x : Fin T.componentCount → ℚ :=
    fun k => if k = i then a else if k = j then 2 * wi else 0
  have hquad := two_coordinate_quadratic A i j hne a (2 * wi)
  have hxquad : x ⬝ᵥ (A *ᵥ x) = 2 * wi * (a ^ 2 - 4 * wi * wj) := by
    calc
      x ⬝ᵥ (A *ᵥ x) =
          a * (A i i * a + A i j * (2 * wi)) +
            (2 * wi) * (A j i * a + A j j * (2 * wi)) := by
              simpa [x] using hquad
      _ = 2 * wi * (a ^ 2 - 4 * wi * wj) := by
        simp [A, a, wi, wj, hii, hjj, T.intersection_symm]
        ring
  have hxle : x ⬝ᵥ (A *ᵥ x) ≤ 0 :=
    dotProduct_mulVec_nonpos_of_positive_kernel hA hoff hmpos hAm x
  have hxne : x ⬝ᵥ (A *ᵥ x) ≠ 0 := by
    intro hzero
    obtain ⟨c, hscale⟩ :=
      (dotProduct_mulVec_eq_zero_iff_of_positive_kernel hA hoff hmpos hAm hconn).mp hzero
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
    have hxk : x k = 0 := by simp [x, hki, hkj]
    have hck : x k = c * m k := by simpa [m] using congrFun hscale k
    have hc : c = 0 := by
      rw [hxk] at hck
      nlinarith [hmpos k]
    have hci : x i = c * m i := by
      simpa [m] using congrFun hscale i
    have hxi : x i = a := by simp [x]
    rw [hxi, hc] at hci
    have hca : a = 0 := by simpa [hc] using hci
    exact (ne_of_gt ha) hca
  have hxlt : x ⬝ᵥ (A *ᵥ x) < 0 := lt_of_le_of_ne hxle hxne
  have hdet : a ^ 2 < 4 * wi * wj := by
    have hinner : a ^ 2 - 4 * wi * wj < 0 := by
      by_contra hninner
      have hnonneg : 0 ≤ 2 * wi * (a ^ 2 - 4 * wi * wj) :=
        mul_nonneg (by positivity) (le_of_not_gt hninner)
      rw [← hxquad] at hnonneg
      linarith
    linarith
  have hsym : T.intersection j i = T.intersection i j :=
    (T.intersection_symm i j).symm
  obtain ⟨p, hpi⟩ := T.weight_dvd_intersection i j
  obtain ⟨q, hqj⟩ := T.weight_dvd_intersection j i
  have hp : 0 < p :=
    pos_of_mul_pos_right (show 0 < T.weight i * p by rwa [hpi] at hij) (T.weight_pos i).le
  have hq : 0 < q :=
    pos_of_mul_pos_right (show 0 < T.weight j * q by rwa [← hsym, hqj] at hij)
      (T.weight_pos j).le
  have hprod : a ^ 2 = (p : ℚ) * (q : ℚ) * (wi * wj) := by
    have hpcast : (T.intersection i j : ℚ) = (T.weight i : ℚ) * (p : ℚ) := by
      exact_mod_cast hpi
    have hqcast : (T.intersection i j : ℚ) = (T.weight j : ℚ) * (q : ℚ) := by
      exact_mod_cast (hsym.symm.trans hqj)
    calc
      (T.intersection i j : ℚ) ^ 2 =
          ((T.weight i : ℚ) * (p : ℚ)) * (T.intersection i j : ℚ) := by
            rw [hpcast]
            ring
      _ = ((T.weight i : ℚ) * (p : ℚ)) * ((T.weight j : ℚ) * (q : ℚ)) := by
        rw [hqcast]
      _ = (p : ℚ) * (q : ℚ) * ((T.weight i : ℚ) * (T.weight j : ℚ)) := by ring
  have hpqQ : (p : ℚ) * (q : ℚ) < 4 := by
    by_contra hnot
    have hge : 4 ≤ (p : ℚ) * (q : ℚ) := le_of_not_gt hnot
    have hnonneg : 0 ≤ ((p : ℚ) * (q : ℚ) - 4) * (wi * wj) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [hprod, hdet]
  have hpq : p * q < 4 := by exact_mod_cast hpqQ
  rcases positive_integer_factors_lt_four hp hq hpq with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := two_vertex_relations T i j hne hii hjj 1 (by omega) (by omega)
    exact Or.inl (Or.inl ⟨_, rfl, by omega, hii, by omega, by omega, by omega, by omega, by omega⟩)
  · obtain ⟨h1, h2, h3, h4, h5⟩ := two_vertex_relations T i j hne hii hjj 2 (by omega) (by omega)
    exact Or.inl (Or.inr (Or.inl
      ⟨_, rfl, by omega, hii, by omega, by omega, by omega, by omega, by omega⟩))
  · obtain ⟨h1, h2, h3, h4, h5⟩ :=
      two_vertex_relations T j i hne.symm hjj hii 2 (by omega) (by omega)
    exact Or.inr (Or.inr (Or.inl
      ⟨_, rfl, by omega, hjj, by omega, by omega, by omega, by omega, by omega⟩))
  · obtain ⟨h1, h2, h3, h4, h5⟩ := two_vertex_relations T i j hne hii hjj 3 (by omega) (by omega)
    exact Or.inl (Or.inr (Or.inr
      ⟨_, rfl, by omega, hii, by omega, by omega, by omega, by omega, by omega⟩))
  · obtain ⟨h1, h2, h3, h4, h5⟩ :=
      two_vertex_relations T j i hne.symm hjj hii 3 (by omega) (by omega)
    exact Or.inr (Or.inr (Or.inr
      ⟨_, rfl, by omega, hjj, by omega, by omega, by omega, by omega, by omega⟩))

end AlgebraicGeometry.NumericalType
