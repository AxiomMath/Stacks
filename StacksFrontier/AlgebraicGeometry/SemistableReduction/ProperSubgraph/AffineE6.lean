module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.D5
public import Mathlib
public import Mathlib.Data.Matrix.Basic

/-!
# The affine `E₆` configuration

The affine `E₆` diagram on seven vertices cannot occur as a proper subgraph of
minus-two indices of a numerical type. This file sets up the `E₆` incidence data
and derives the nonexistence from the `D₅` bounds.

## Main definitions

* `AlgebraicGeometry.NumericalType.IsE6ForwardEdge`,
  `AlgebraicGeometry.NumericalType.IsE6Adjacent` and
  `AlgebraicGeometry.NumericalType.e6IntersectionMatrix`.

## Main results

* `AlgebraicGeometry.NumericalType.weight_eq_of_e6`,
  `AlgebraicGeometry.NumericalType.intersection_eq_e6Matrix` and
  `AlgebraicGeometry.NumericalType.e6_neighborMultiplicity_le`.
* `AlgebraicGeometry.NumericalType.not_exists_seven_minusTwoIndices_with_affineE6_edges`.

## References

* [Stacks Project, Tag 0C8F](https://stacks.math.columbia.edu/tag/0C8F)
* [Stacks Project, Tag 0C8I](https://stacks.math.columbia.edu/tag/0C8I)
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace AlgebraicGeometry.NumericalType

/-! ### The `E₆` incidence data -/

private def e6LeftPos : Fin 5 → Fin 6 := ![0, 1, 2, 3, 5]

private def e6RightPos : Fin 5 → Fin 6 := ![4, 3, 2, 1, 5]

private def e6LeftIndex (r : Fin 6) : Fin 5 :=
  if r = 0 then 0 else if r = 1 then 1 else if r = 2 then 2 else
    if r = 3 then 3 else 4

private def e6RightIndex (r : Fin 6) : Fin 5 :=
  if r = 4 then 0 else if r = 3 then 1 else if r = 2 then 2 else
    if r = 1 then 3 else 4

private lemma e6LeftPos_leftIndex (r : Fin 6) (hr : r ≠ 4) :
    e6LeftPos (e6LeftIndex r) = r := by
  fin_cases r <;> simp_all [e6LeftPos, e6LeftIndex]

private lemma e6RightPos_rightIndex (r : Fin 6) (hr : r ≠ 0) :
    e6RightPos (e6RightIndex r) = r := by
  fin_cases r <;> simp_all [e6RightPos, e6RightIndex]

private lemma e6LeftPos_injective : Function.Injective e6LeftPos := by
  decide

private lemma e6RightPos_injective : Function.Injective e6RightPos := by
  decide

private def e6LeftEmbedding {α : Type*} (i : Fin 6 → α)
    (hi : Function.Injective i) : Fin 5 ↪ α where
  toFun := i ∘ e6LeftPos
  inj' := hi.comp e6LeftPos_injective

private def e6RightEmbedding {α : Type*} (i : Fin 6 → α)
    (hi : Function.Injective i) : Fin 5 ↪ α where
  toFun := i ∘ e6RightPos
  inj' := hi.comp e6RightPos_injective

/-- The five oriented edges `01`, `12`, `23`, `34`, and `25` in the displayed
E6 diagram. -/
public def IsE6ForwardEdge (r s : Fin 6) : Prop :=
  (r = 0 ∧ s = 1) ∨ (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 3) ∨
    (r = 3 ∧ s = 4) ∨ (r = 2 ∧ s = 5)

/-- Adjacency in the (undirected) E6 diagram. -/
public def IsE6Adjacent (r s : Fin 6) : Prop :=
  IsE6ForwardEdge r s ∨ IsE6ForwardEdge s r

/-- Adjacency in the E6 diagram is decidable. -/
public instance (r s : Fin 6) : Decidable (IsE6Adjacent r s) := by
  unfold IsE6Adjacent IsE6ForwardEdge
  infer_instance

/-- The E6 intersection matrix with common weight `w`. -/
public def e6IntersectionMatrix (w : ℤ) : Matrix (Fin 6) (Fin 6) ℤ := fun r s =>
  if r = s then -2 * w else if IsE6Adjacent r s then w else 0

private lemma e6_d5_left_edges {T : NumericalType} (i : Fin 6 → Fin T.componentCount)
    (hi : Function.Injective i) (hminus : ∀ r, IsMinusTwoIndex T (i r))
    (hedge : ∀ r s, IsE6ForwardEdge r s → T.intersection (i r) (i s) ≠ 0) :
    let v := e6LeftEmbedding i hi
    (∀ r, IsMinusTwoIndex T (v r)) ∧ T.intersection (v 0) (v 1) ≠ 0 ∧
      T.intersection (v 1) (v 2) ≠ 0 ∧
      T.intersection (v 2) (v 3) ≠ 0 ∧
      T.intersection (v 2) (v 4) ≠ 0 := by
  classical
  dsimp
  refine ⟨fun r => ?_, ?_, ?_, ?_, ?_⟩
  · simpa [e6LeftEmbedding, e6LeftPos] using hminus (e6LeftPos r)
  · simpa [e6LeftEmbedding, e6LeftPos] using hedge 0 1 (by simp [IsE6ForwardEdge])
  · simpa [e6LeftEmbedding, e6LeftPos] using hedge 1 2 (by simp [IsE6ForwardEdge])
  · simpa [e6LeftEmbedding, e6LeftPos] using hedge 2 3 (by simp [IsE6ForwardEdge])
  · simpa [e6LeftEmbedding, e6LeftPos] using hedge 2 5 (by simp [IsE6ForwardEdge])

private lemma e6_d5_right_edges {T : NumericalType} (i : Fin 6 → Fin T.componentCount)
    (hi : Function.Injective i) (hminus : ∀ r, IsMinusTwoIndex T (i r))
    (hedge : ∀ r s, IsE6ForwardEdge r s → T.intersection (i r) (i s) ≠ 0) :
    let v := e6RightEmbedding i hi
    (∀ r, IsMinusTwoIndex T (v r)) ∧ T.intersection (v 0) (v 1) ≠ 0 ∧
      T.intersection (v 1) (v 2) ≠ 0 ∧
      T.intersection (v 2) (v 3) ≠ 0 ∧
      T.intersection (v 2) (v 4) ≠ 0 := by
  classical
  dsimp
  refine ⟨fun r => ?_, ?_, ?_, ?_, ?_⟩
  · simpa [e6RightEmbedding, e6RightPos] using hminus (e6RightPos r)
  · simpa [e6RightEmbedding, e6RightPos, T.intersection_symm] using
      hedge 3 4 (by simp [IsE6ForwardEdge])
  · simpa [e6RightEmbedding, e6RightPos, T.intersection_symm] using
      hedge 2 3 (by simp [IsE6ForwardEdge])
  · simpa [e6RightEmbedding, e6RightPos, T.intersection_symm] using
      hedge 1 2 (by simp [IsE6ForwardEdge])
  · simpa [e6RightEmbedding, e6RightPos] using hedge 2 5 (by simp [IsE6ForwardEdge])

/-- The weights at six distinct minus-two indices containing the five edges of an
E6 diagram are all equal. -/
@[stacks 0C8F "weights"]
public lemma weight_eq_of_e6 (T : NumericalType) (hcount : 6 < T.componentCount)
    (i : Fin 6 → Fin T.componentCount) (hi : Function.Injective i)
    (hminus : ∀ r, IsMinusTwoIndex T (i r))
    (hedge : ∀ r s, IsE6ForwardEdge r s → T.intersection (i r) (i s) ≠ 0) :
    ∀ r, T.weight (i r) = T.weight (i 0) := by
  classical
  let vL := e6LeftEmbedding i hi
  let vR := e6RightEmbedding i hi
  obtain ⟨hLminus, hL01, hL12, hL23, hL24⟩ := e6_d5_left_edges i hi hminus hedge
  obtain ⟨hRminus, hR01, hR12, hR23, hR24⟩ := e6_d5_right_edges i hi hminus hedge
  obtain ⟨wL, hwL, _⟩ := exists_weight_eq_d5_of_isMinusTwoIndex
    T (by omega) vL hLminus hL01 hL12 hL23 hL24
  obtain ⟨wR, hwR, _⟩ := exists_weight_eq_d5_of_isMinusTwoIndex
    T (by omega) vR hRminus hR01 hR12 hR23 hR24
  have hLtwo : T.weight (i 2) = wL := by
    simpa [vL, e6LeftEmbedding, e6LeftPos] using congrFun hwL (2 : Fin 5)
  have hRtwo : T.weight (i 2) = wR := by
    simpa [vR, e6RightEmbedding, e6RightPos] using congrFun hwR (2 : Fin 5)
  have hweight : ∀ r, T.weight (i r) = wL := by
    intro r
    fin_cases r
    · simpa [vL, e6LeftEmbedding, e6LeftPos] using congrFun hwL (0 : Fin 5)
    · simpa [vL, e6LeftEmbedding, e6LeftPos] using congrFun hwL (1 : Fin 5)
    · exact hLtwo
    · simpa [vL, e6LeftEmbedding, e6LeftPos] using congrFun hwL (3 : Fin 5)
    · simpa [vR, e6RightEmbedding, e6RightPos, hLtwo.symm.trans hRtwo] using
        congrFun hwR (0 : Fin 5)
    · simpa [vL, e6LeftEmbedding, e6LeftPos] using congrFun hwL (4 : Fin 5)
  exact fun r => (hweight r).trans (hweight 0).symm

/-- The rational intersection matrix and multiplicity vector satisfy the hypotheses of the
positive-kernel quadratic form lemmas. -/
private lemma intersection_positive_kernel (T : NumericalType)
    (A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ) (m : Fin T.componentCount → ℚ)
    (hA : A = fun a b => (T.intersection a b : ℚ)) (hm : m = fun a => (T.multiplicity a : ℚ)) :
    A.IsSymm ∧ (∀ a b, a ≠ b → 0 ≤ A a b) ∧ (∀ a, 0 < m a) ∧ A *ᵥ m = 0 ∧
      ∀ I : Set (Fin T.componentCount), I.Nonempty → I ≠ Set.univ →
        ¬ ∀ a ∈ I, ∀ b ∉ I, A a b = 0 := by
  subst hA hm
  refine ⟨?_, fun a b hab => ?_, fun a => ?_, ?_, fun I hIne hIproper hcut => ?_⟩
  · ext a b
    change (T.intersection b a : ℚ) = (T.intersection a b : ℚ)
    exact_mod_cast (T.intersection_symm a b).symm
  · change 0 ≤ (T.intersection a b : ℚ)
    exact_mod_cast T.intersection_nonneg a b hab
  · change 0 < (T.multiplicity a : ℚ)
    exact_mod_cast T.multiplicity_pos a
  · ext a
    change (∑ b, (T.intersection a b : ℚ) * (T.multiplicity b : ℚ)) = 0
    exact_mod_cast T.intersection_mul_multiplicity a
  · refine T.connected ⟨I, hIne, hIproper, fun a ha b hb => ?_⟩
    have hab : (T.intersection a b : ℚ) = 0 := hcut a ha b hb
    exact_mod_cast hab

/-- The intersection matrix on six distinct minus-two indices containing the five
edges of an E6 diagram is the standard weighted E6 matrix. -/
@[stacks 0C8F "intersection matrix"]
public lemma intersection_eq_e6Matrix (T : NumericalType) (hcount : 6 < T.componentCount)
    (i : Fin 6 → Fin T.componentCount) (hi : Function.Injective i)
    (hminus : ∀ r, IsMinusTwoIndex T (i r))
    (hedge : ∀ r s, IsE6ForwardEdge r s → T.intersection (i r) (i s) ≠ 0) :
    (fun r s => T.intersection (i r) (i s)) = e6IntersectionMatrix (T.weight (i 0)) := by
  classical
  let vL := e6LeftEmbedding i hi
  let vR := e6RightEmbedding i hi
  obtain ⟨hLminus, hL01, hL12, hL23, hL24⟩ := e6_d5_left_edges i hi hminus hedge
  obtain ⟨hRminus, hR01, hR12, hR23, hR24⟩ := e6_d5_right_edges i hi hminus hedge
  obtain ⟨wL, hwL, haL⟩ := exists_weight_eq_d5_of_isMinusTwoIndex
    T (by omega) vL hLminus hL01 hL12 hL23 hL24
  obtain ⟨wR, hwR, haR⟩ := exists_weight_eq_d5_of_isMinusTwoIndex
    T (by omega) vR hRminus hR01 hR12 hR23 hR24
  have hLentry (r s : Fin 6) (hr : r ≠ 4) (hs : s ≠ 4) :
      T.intersection (i r) (i s) =
        (!![-2 * wL, wL, 0, 0, 0; wL, -2 * wL, wL, 0, 0;
            0, wL, -2 * wL, wL, wL; 0, 0, wL, -2 * wL, 0;
            0, 0, wL, 0, -2 * wL] : Matrix (Fin 5) (Fin 5) ℤ)
          (e6LeftIndex r) (e6LeftIndex s) := by
    have h := congrFun (congrFun haL (e6LeftIndex r)) (e6LeftIndex s)
    change T.intersection (i (e6LeftPos (e6LeftIndex r)))
      (i (e6LeftPos (e6LeftIndex s))) = _ at h
    rwa [e6LeftPos_leftIndex r hr, e6LeftPos_leftIndex s hs] at h
  have hRentry (r s : Fin 6) (hr : r ≠ 0) (hs : s ≠ 0) :
      T.intersection (i r) (i s) =
        (!![-2 * wR, wR, 0, 0, 0; wR, -2 * wR, wR, 0, 0;
            0, wR, -2 * wR, wR, wR; 0, 0, wR, -2 * wR, 0;
            0, 0, wR, 0, -2 * wR] : Matrix (Fin 5) (Fin 5) ℤ)
          (e6RightIndex r) (e6RightIndex s) := by
    have h := congrFun (congrFun haR (e6RightIndex r)) (e6RightIndex s)
    change T.intersection (i (e6RightPos (e6RightIndex r)))
      (i (e6RightPos (e6RightIndex s))) = _ at h
    rwa [e6RightPos_rightIndex r hr, e6RightPos_rightIndex s hs] at h
  have hLtwo : T.weight (i 2) = wL := by
    simpa [vL, e6LeftEmbedding, e6LeftPos] using congrFun hwL (2 : Fin 5)
  have hw : wL = wR := hLtwo.symm.trans <| by
    simpa [vR, e6RightEmbedding, e6RightPos] using congrFun hwR (2 : Fin 5)
  have hwL0 : T.weight (i 0) = wL := by
    simpa [vL, e6LeftEmbedding, e6LeftPos] using congrFun hwL (0 : Fin 5)
  let p : ℤ := T.intersection (i 0) (i 4)
  have htable (r s : Fin 6) : T.intersection (i r) (i s) =
      if (r = 0 ∧ s = 4) ∨ (r = 4 ∧ s = 0) then p
      else e6IntersectionMatrix wL r s := by
    fin_cases r <;> fin_cases s <;>
      simp [p, e6LeftIndex, e6RightIndex, e6IntersectionMatrix,
        IsE6Adjacent, IsE6ForwardEdge, hLentry, hRentry, hw,
        T.intersection_symm]
  have hp_nonneg : 0 ≤ p := by
    apply T.intersection_nonneg
    intro h
    have h' := hi h
    omega
  have hp_zero : p = 0 := by
    by_contra hpne
    have hp_pos : 0 < p := by omega
    have hdiv : T.weight (i 0) ∣ p := by
      simpa [p] using T.weight_dvd_intersection (i 0) (i 4)
    have hwpos : 0 < T.weight (i 0) := T.weight_pos (i 0)
    have hwle : T.weight (i 0) ≤ p := Int.le_of_dvd hp_pos hdiv
    let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
      fun a b => (T.intersection a b : ℚ)
    let m : Fin T.componentCount → ℚ := fun a => (T.multiplicity a : ℚ)
    obtain ⟨hA, hoff, hm, hAm, -⟩ := intersection_positive_kernel T A m rfl rfl
    let x : Fin T.componentCount → ℚ :=
      (2 : ℚ) • Pi.single (i 0) 1 + (3 : ℚ) • Pi.single (i 1) 1 +
      (4 : ℚ) • Pi.single (i 2) 1 + (3 : ℚ) • Pi.single (i 3) 1 +
      (2 : ℚ) • Pi.single (i 4) 1 + (2 : ℚ) • Pi.single (i 5) 1
    have hq := dotProduct_mulVec_nonpos_of_positive_kernel
      hA hoff hm hAm x
    have hquad : x ⬝ᵥ (A *ᵥ x) = -4 * (wL : ℚ) + 8 * (p : ℚ) := by
      simp only [x, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_single_one, Matrix.col_apply, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, single_dotProduct]
      simp [A, htable, e6IntersectionMatrix, IsE6Adjacent,
        IsE6ForwardEdge, hw]
      ring_nf
    have hwLpos : 0 < (wL : ℚ) := by
      rw [← hwL0]
      exact_mod_cast hwpos
    have hpleInt : wL ≤ p := by
      rw [← hwL0]
      exact hwle
    have hple : (wL : ℚ) ≤ (p : ℚ) := by exact_mod_cast hpleInt
    rw [hquad] at hq
    nlinarith
  funext r s
  rw [htable r s]
  by_cases hcross : (r = 0 ∧ s = 4) ∨ (r = 4 ∧ s = 0)
  · rcases hcross with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hp_zero, e6IntersectionMatrix, IsE6Adjacent, IsE6ForwardEdge]
  · simp [hcross, hwL0]

/-- At each vertex of an E6 configuration, the sum of the multiplicities at its
neighbors is at most twice its own multiplicity. -/
@[stacks 0C8F "multiplicity inequalities"]
public lemma e6_neighborMultiplicity_le (T : NumericalType) (hcount : 6 < T.componentCount)
    (i : Fin 6 → Fin T.componentCount) (hi : Function.Injective i)
    (hminus : ∀ r, IsMinusTwoIndex T (i r))
    (hedge : ∀ r s, IsE6ForwardEdge r s → T.intersection (i r) (i s) ≠ 0) :
    ∀ r, ∑ s with IsE6Adjacent r s, T.multiplicity (i s) ≤ 2 * T.multiplicity (i r) := by
  classical
  let vL := e6LeftEmbedding i hi
  let vR := e6RightEmbedding i hi
  obtain ⟨hLminus, hL01, hL12, hL23, hL24⟩ := e6_d5_left_edges i hi hminus hedge
  obtain ⟨hRminus, hR01, hR12, hR23, hR24⟩ := e6_d5_right_edges i hi hminus hedge
  intro r
  fin_cases r
  · have h := multiplicity_le_of_d5_at_zero T (by omega) vL
      hLminus hL01 hL12 hL23 hL24
    simp [IsE6Adjacent, IsE6ForwardEdge, Finset.sum_filter,
      vL, e6LeftEmbedding, e6LeftPos] at h ⊢
    omega
  · have h := multiplicity_le_of_d5_at_one T (by omega) vL
      hLminus hL01 hL12 hL23 hL24
    simp [IsE6Adjacent, IsE6ForwardEdge, Finset.sum_filter, Fin.sum_univ_succ,
      vL, e6LeftEmbedding, e6LeftPos] at h ⊢
    omega
  · have h := multiplicity_le_of_d5_at_two T (by omega) vL
      hLminus hL01 hL12 hL23 hL24
    simp [IsE6Adjacent, IsE6ForwardEdge, Finset.sum_filter, Fin.sum_univ_succ,
      vL, e6LeftEmbedding, e6LeftPos] at h ⊢
    omega
  · have h := multiplicity_le_of_d5_at_one T (by omega) vR
      hRminus hR01 hR12 hR23 hR24
    simp [IsE6Adjacent, IsE6ForwardEdge, Finset.sum_filter, Fin.sum_univ_succ,
      vR, e6RightEmbedding, e6RightPos] at h ⊢
    omega
  · have h := multiplicity_le_of_d5_at_zero T (by omega) vR
      hRminus hR01 hR12 hR23 hR24
    simp [IsE6Adjacent, IsE6ForwardEdge, Finset.sum_filter,
      vR, e6RightEmbedding, e6RightPos] at h ⊢
    omega
  · have h := multiplicity_le_of_d5_at_four T (by omega) vL
      hLminus hL01 hL12 hL23 hL24
    simp [IsE6Adjacent, IsE6ForwardEdge, Finset.sum_filter,
      vL, e6LeftEmbedding, e6LeftPos] at h ⊢
    omega

/-! ### No proper affine `E₆` subgraph -/

/-- **Stacks Project, Tag 0C8I.** A numerical type with more than seven components has no
seven distinct minus-two indices whose indicated intersections form the edges of the affine
E6 diagram. -/
@[stacks 0C8I]
public theorem not_exists_seven_minusTwoIndices_with_affineE6_edges
    (T : NumericalType) (hn : 7 < T.componentCount) :
    ¬ ∃ f g h i j k l : Fin T.componentCount,
      List.Pairwise (· ≠ ·) [f, g, h, i, j, k, l] ∧
      IsMinusTwoIndex T f ∧ IsMinusTwoIndex T g ∧ IsMinusTwoIndex T h ∧
      IsMinusTwoIndex T i ∧ IsMinusTwoIndex T j ∧ IsMinusTwoIndex T k ∧
      IsMinusTwoIndex T l ∧
      T.intersection f g ≠ 0 ∧ T.intersection g h ≠ 0 ∧
      T.intersection i j ≠ 0 ∧ T.intersection j h ≠ 0 ∧
      T.intersection k l ≠ 0 ∧ T.intersection l h ≠ 0 := by
  classical
  intro hex
  obtain ⟨f, g, h, i, j, k, l, hpair, hmf, hmg, hmh, hmi, hmj, hmk, hml,
    hfg0, hgh0, hij0, hjh0, hkl0, hlh0⟩ := hex
  let : Std.Irrefl (fun a b : Fin T.componentCount => a ≠ b) :=
    ⟨fun _ hab => hab rfl⟩
  have hgh : T.intersection h g ≠ 0 := by
    rw [T.intersection_symm]
    exact hgh0
  have hhl : T.intersection h l ≠ 0 := by
    rw [T.intersection_symm]
    exact hlh0
  have hhj : T.intersection h j ≠ 0 := by
    rw [T.intersection_symm]
    exact hjh0
  let indices : List (Fin T.componentCount) := [f, g, h, i, j, k, l]
  have hindices : indices.Nodup := hpair.nodup
  have hmin (r : Fin 7) : IsMinusTwoIndex T (indices.get r) := by
    fin_cases r <;> simpa [indices]
  obtain ⟨⟨dfg, dfh, dfi, dfj, dfk, dfl⟩, ⟨dgh, dgi, dgj, dgk, dgl⟩, ⟨dhi, dhj, dhk, dhl⟩,
    ⟨dij, dik, dil⟩, ⟨djk, djl⟩, dkl⟩ := by simpa using hpair
  let p₁ : Fin 5 → Fin 7 := ![0, 1, 2, 4, 6]
  let p₂ : Fin 5 → Fin 7 := ![3, 4, 2, 1, 6]
  let p₃ : Fin 5 → Fin 7 := ![5, 6, 2, 1, 4]
  have hp₁ : Function.Injective p₁ := by decide
  have hp₂ : Function.Injective p₂ := by decide
  have hp₃ : Function.Injective p₃ := by decide
  let v₁ : Fin 5 → Fin T.componentCount := fun r => indices.get (p₁ r)
  let v₂ : Fin 5 → Fin T.componentCount := fun r => indices.get (p₂ r)
  let v₃ : Fin 5 → Fin T.componentCount := fun r => indices.get (p₃ r)
  have hv₁ : Function.Injective v₁ := hindices.injective_get.comp hp₁
  have hv₂ : Function.Injective v₂ := hindices.injective_get.comp hp₂
  have hv₃ : Function.Injective v₃ := hindices.injective_get.comp hp₃
  obtain ⟨w₁, hw₁, hmat₁⟩ :=
    exists_weight_eq_d5_of_isMinusTwoIndex T (by omega) ⟨v₁, hv₁⟩ (fun r => hmin (p₁ r))
      (by simpa [v₁, indices, p₁] using hfg0) (by simpa [v₁, indices, p₁] using hgh0)
      (by simpa [v₁, indices, p₁] using hhj) (by simpa [v₁, indices, p₁] using hhl)
  obtain ⟨w₂, hw₂, hmat₂⟩ :=
    exists_weight_eq_d5_of_isMinusTwoIndex T (by omega) ⟨v₂, hv₂⟩ (fun r => hmin (p₂ r))
      (by simpa [v₂, indices, p₂] using hij0) (by simpa [v₂, indices, p₂] using hjh0)
      (by simpa [v₂, indices, p₂] using hgh) (by simpa [v₂, indices, p₂] using hhl)
  obtain ⟨w₃, hw₃, hmat₃⟩ :=
    exists_weight_eq_d5_of_isMinusTwoIndex T (by omega) ⟨v₃, hv₃⟩ (fun r => hmin (p₃ r))
      (by simpa [v₃, indices, p₃] using hkl0) (by simpa [v₃, indices, p₃] using hlh0)
      (by simpa [v₃, indices, p₃] using hgh) (by simpa [v₃, indices, p₃] using hhj)
  have hh₁ : T.weight h = w₁ := by simpa [v₁, indices, p₁] using congrFun hw₁ (2 : Fin 5)
  have hw₁_eq_w₂ : w₁ = w₂ := hh₁.symm.trans <| by
    simpa [v₂, indices, p₂] using congrFun hw₂ (2 : Fin 5)
  have hw₁_eq_w₃ : w₁ = w₃ := hh₁.symm.trans <| by
    simpa [v₃, indices, p₃] using congrFun hw₃ (2 : Fin 5)
  have hweight (a : Fin T.componentCount)
      (ha : a = f ∨ a = g ∨ a = h ∨ a = i ∨ a = j ∨ a = k ∨ a = l) :
      T.weight a = w₁ := by
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [v₁, indices, p₁] using congrFun hw₁ (0 : Fin 5)
    · simpa [v₁, indices, p₁] using congrFun hw₁ (1 : Fin 5)
    · exact hh₁
    · simpa [v₂, indices, p₂, hw₁_eq_w₂] using congrFun hw₂ (0 : Fin 5)
    · simpa [v₁, indices, p₁] using congrFun hw₁ (3 : Fin 5)
    · simpa [v₃, indices, p₃, hw₁_eq_w₃] using congrFun hw₃ (0 : Fin 5)
    · simpa [v₁, indices, p₁] using congrFun hw₁ (4 : Fin 5)
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun a b => (T.intersection a b : ℚ)
  let m : Fin T.componentCount → ℚ := fun a => (T.multiplicity a : ℚ)
  let x : Fin T.componentCount → ℚ :=
    Pi.single f 1 + Pi.single g 2 + Pi.single h 3 +
    Pi.single i 1 + Pi.single j 2 + Pi.single k 1 + Pi.single l 2
  obtain ⟨hAsymm, hAoff, hmpos, hAm, hconn⟩ := intersection_positive_kernel T A m rfl rfl
  have hdiag (a : Fin T.componentCount)
      (ha : a = f ∨ a = g ∨ a = h ∨ a = i ∨ a = j ∨ a = k ∨ a = l) :
      A a a = -2 * (w₁ : ℚ) := by
    have hm : IsMinusTwoIndex T a := by
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    change (T.intersection a a : ℚ) = _
    rw [hm.2, hweight a ha]
    push_cast
    ring
  have hedge (a b : Fin T.componentCount) (hab : T.intersection a b = w₁) :
      A a b = w₁ ∧ A b a = w₁ := by
    have h' : (T.intersection a b : ℚ) = w₁ := by exact_mod_cast hab
    exact ⟨h', by rw [hAsymm.apply]; exact h'⟩
  have e₁ : T.intersection f g = w₁ := by
    simpa [v₁, indices, p₁] using congrFun (congrFun hmat₁ (0 : Fin 5)) (1 : Fin 5)
  have e₂ : T.intersection g h = w₁ := by
    simpa [v₁, indices, p₁] using congrFun (congrFun hmat₁ (1 : Fin 5)) (2 : Fin 5)
  have e₃ : T.intersection i j = w₁ := by
    simpa [v₂, indices, p₂, hw₁_eq_w₂] using congrFun (congrFun hmat₂ (0 : Fin 5)) (1 : Fin 5)
  have e₄ : T.intersection j h = w₁ := by
    simpa [v₂, indices, p₂, hw₁_eq_w₂] using congrFun (congrFun hmat₂ (1 : Fin 5)) (2 : Fin 5)
  have e₅ : T.intersection k l = w₁ := by
    simpa [v₃, indices, p₃, hw₁_eq_w₃] using congrFun (congrFun hmat₃ (0 : Fin 5)) (1 : Fin 5)
  have e₆ : T.intersection l h = w₁ := by
    simpa [v₃, indices, p₃, hw₁_eq_w₃] using congrFun (congrFun hmat₃ (1 : Fin 5)) (2 : Fin 5)
  have hxquad_nonneg : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    simp [x, Matrix.mulVec_add, Matrix.mulVec_single, dotProduct_add, single_dotProduct,
      hdiag, hedge _ _ e₁, hedge _ _ e₂, hedge _ _ e₃, hedge _ _ e₄, hedge _ _ e₅,
      hedge _ _ e₆]
    linarith [hAoff _ _ dfh, hAoff _ _ (Ne.symm dfh), hAoff _ _ dfi, hAoff _ _ (Ne.symm dfi),
      hAoff _ _ dfj, hAoff _ _ (Ne.symm dfj), hAoff _ _ dfk, hAoff _ _ (Ne.symm dfk),
      hAoff _ _ dfl, hAoff _ _ (Ne.symm dfl), hAoff _ _ dgi, hAoff _ _ (Ne.symm dgi),
      hAoff _ _ dgj, hAoff _ _ (Ne.symm dgj), hAoff _ _ dgk, hAoff _ _ (Ne.symm dgk),
      hAoff _ _ dgl, hAoff _ _ (Ne.symm dgl), hAoff _ _ dhi, hAoff _ _ (Ne.symm dhi),
      hAoff _ _ dhk, hAoff _ _ (Ne.symm dhk), hAoff _ _ dik, hAoff _ _ (Ne.symm dik),
      hAoff _ _ dil, hAoff _ _ (Ne.symm dil), hAoff _ _ djk, hAoff _ _ (Ne.symm djk),
      hAoff _ _ djl, hAoff _ _ (Ne.symm djl)]
  have hxquad : x ⬝ᵥ (A *ᵥ x) = 0 :=
    le_antisymm (dotProduct_mulVec_nonpos_of_positive_kernel hAsymm hAoff hmpos hAm x)
      hxquad_nonneg
  obtain ⟨q, hxq⟩ := (dotProduct_mulVec_eq_zero_iff_of_positive_kernel hAsymm hAoff hmpos hAm
    hconn (x := x)).mp hxquad
  obtain ⟨z, hz⟩ : ∃ z : Fin T.componentCount, z ∉ indices.toFinset := by
    by_contra! hall
    have hcard := Finset.card_le_card (fun z _ => hall z : Finset.univ ⊆ indices.toFinset)
    rw [Finset.card_univ, List.toFinset_card_of_nodup hindices] at hcard
    simp [indices] at hcard
    omega
  have ⟨hzf, hzg, hzh, hzi, hzj, hzk, hzl⟩ :
      z ≠ f ∧ z ≠ g ∧ z ≠ h ∧ z ≠ i ∧ z ≠ j ∧ z ≠ k ∧ z ≠ l := by
    simpa [indices] using hz
  have hxz : x z = 0 := by
    simp [x, hzf, hzg, hzh, hzi, hzj, hzk, hzl]
  have hqzero : q = 0 := by
    have hzq := congrFun hxq z
    rw [hxz] at hzq
    change 0 = q * m z at hzq
    exact (mul_eq_zero.mp hzq.symm).resolve_right (ne_of_gt (hmpos z))
  have hxf : x f = 1 := by
    simp [x, dfg, dfh, dfi, dfj, dfk, dfl]
  have hxfq := congrFun hxq f
  rw [hxf, hqzero] at hxfq
  norm_num [Pi.smul_apply] at hxfq

end AlgebraicGeometry.NumericalType
