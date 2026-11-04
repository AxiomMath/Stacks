module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.ThreeVertices
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FourVertices
public import Mathlib
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Five-vertex chains: edge and weight shapes

Combinatorial and numerical input for the classification of five-vertex chains
of minus-two indices: the possible edge shapes of a chain, the weight shapes of
four- and five-vertex chains, the quadratic form of a five-vertex path, the
ruling out of the affine weight profiles, the base value of the quadratic form,
and the edge patterns of four-vertex chains.
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

private lemma fin4_path_order (a b c d : Fin 4)
    (hinj : Function.Injective ![a, b, c, d])
    (hab : (a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a)
    (hbc : (b : ℕ) + 1 = c ∨ (c : ℕ) + 1 = b)
    (hcd : (c : ℕ) + 1 = d ∨ (d : ℕ) + 1 = c) :
    (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3) ∨
      (a = 3 ∧ b = 2 ∧ c = 1 ∧ d = 0) := by
  have ha : (a : ℕ) < 4 := a.isLt
  have hb : (b : ℕ) < 4 := b.isLt
  have hc : (c : ℕ) < 4 := c.isLt
  have hd : (d : ℕ) < 4 := d.isLt
  have hab' : a ≠ b := by simpa using hinj.ne (show (0 : Fin 4) ≠ 1 by decide)
  have hac' : a ≠ c := by simpa using hinj.ne (show (0 : Fin 4) ≠ 2 by decide)
  have had' : a ≠ d := by simpa using hinj.ne (show (0 : Fin 4) ≠ 3 by decide)
  have hbc' : b ≠ c := by simpa using hinj.ne (show (1 : Fin 4) ≠ 2 by decide)
  have hbd' : b ≠ d := by simpa using hinj.ne (show (1 : Fin 4) ≠ 3 by decide)
  have hcd' : c ≠ d := by simpa using hinj.ne (show (2 : Fin 4) ≠ 3 by decide)
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc <;>
    rcases hcd with hcd | hcd <;> omega

private lemma fin4_sigma_path_order (σ : Equiv.Perm (Fin 4))
    (horder : (σ.symm 0 = 0 ∧ σ.symm 1 = 1 ∧
        σ.symm 2 = 2 ∧ σ.symm 3 = 3) ∨
      (σ.symm 0 = 3 ∧ σ.symm 1 = 2 ∧
        σ.symm 2 = 1 ∧ σ.symm 3 = 0)) :
    (∀ x : Fin 4, σ x = x) ∨
      (∀ x : Fin 4, σ x = ⟨3 - x.val, by omega⟩) := by
  rcases horder with h | h
  · left
    intro x
    fin_cases x
    · simpa using (congrArg σ h.1).symm
    · simpa using (congrArg σ h.2.1).symm
    · simpa using (congrArg σ h.2.2.1).symm
    · simpa using (congrArg σ h.2.2.2).symm
  · right
    intro x
    fin_cases x
    · simpa using (congrArg σ h.2.2.2).symm
    · simpa using (congrArg σ h.2.2.1).symm
    · simpa using (congrArg σ h.2.1).symm
    · simpa using (congrArg σ h.1).symm

def EdgeOne (T : NumericalType) (i j : Fin T.componentCount) : Prop :=
  ∃ w : ℤ, T.weight i = w ∧ T.weight j = w ∧ T.intersection i j = w

def EdgeDoubleRight (T : NumericalType)
    (i j : Fin T.componentCount) : Prop :=
  ∃ w : ℤ, T.weight i = w ∧ T.weight j = 2 * w ∧
    T.intersection i j = 2 * w

def EdgeDoubleLeft (T : NumericalType)
    (i j : Fin T.componentCount) : Prop :=
  ∃ w : ℤ, T.weight i = 2 * w ∧ T.weight j = w ∧
    T.intersection i j = 2 * w

def EdgeShape (T : NumericalType)
    (i j : Fin T.componentCount) : Prop :=
  EdgeOne T i j ∨ EdgeDoubleRight T i j ∨ EdgeDoubleLeft T i j

lemma edgeShape_intersection_eq_max (T : NumericalType)
    (i j : Fin T.componentCount) (h : EdgeShape T i j) :
    T.intersection i j = max (T.weight i) (T.weight j) := by
  rcases h with h | h | h
  · rcases h with ⟨w, hwi, hwj, hint⟩
    rw [hwi, hwj, hint]
    simp
  · rcases h with ⟨w, hwi, hwj, hint⟩
    have hw : 0 < w := by rw [← hwi]; exact T.weight_pos i
    rw [hwi, hwj, hint]
    exact (max_eq_right (show w ≤ 2 * w by omega)).symm
  · rcases h with ⟨w, hwi, hwj, hint⟩
    have hw : 0 < w := by rw [← hwj]; exact T.weight_pos j
    rw [hwi, hwj, hint]
    exact (max_eq_left (show w ≤ 2 * w by omega)).symm

def FourEdgePattern (T : NumericalType)
    (i j k l : Fin T.componentCount) : Prop :=
  ∃ w : ℤ,
    (fun r : Fin 4 => T.weight (![i, j, k, l] r)) = ![w, w, w, w] ∨
    (fun r : Fin 4 => T.weight (![i, j, k, l] r)) = ![w, w, w, 2 * w] ∨
    (fun r : Fin 4 => T.weight (![i, j, k, l] r)) = ![2 * w, w, w, w] ∨
    (fun r : Fin 4 => T.weight (![i, j, k, l] r)) = ![2 * w, 2 * w, 2 * w, w] ∨
    (fun r : Fin 4 => T.weight (![i, j, k, l] r)) = ![w, 2 * w, 2 * w, 2 * w] ∨
    (fun r : Fin 4 => T.weight (![i, j, k, l] r)) = ![w, w, 2 * w, 2 * w] ∨
    (fun r : Fin 4 => T.weight (![i, j, k, l] r)) = ![2 * w, 2 * w, w, w]

def FourWeightShape (a b c d : ℤ) : Prop :=
  (a = b ∧ b = c ∧ c = d) ∨
  (a = b ∧ b = c ∧ d = 2 * c) ∨
  (a = 2 * b ∧ b = c ∧ c = d) ∨
  (a = b ∧ b = c ∧ c = 2 * d) ∨
  (b = 2 * a ∧ b = c ∧ c = d) ∨
  (a = b ∧ c = 2 * b ∧ c = d) ∨
  (a = b ∧ a = 2 * c ∧ c = d)

def FiveWeightShape (a b c d e : ℤ) : Prop :=
  (a = b ∧ b = c ∧ c = d ∧ d = e) ∨
  (a = b ∧ b = c ∧ c = d ∧ e = 2 * d) ∨
  (a = 2 * b ∧ b = c ∧ c = d ∧ d = e) ∨
  (a = b ∧ b = c ∧ c = d ∧ d = 2 * e) ∨
  (b = 2 * a ∧ b = c ∧ c = d ∧ d = e) ∨
  (a = 2 * b ∧ b = c ∧ c = d ∧ d = 2 * e) ∨
  (a = 2 * b ∧ b = c ∧ c = d ∧ e = 2 * d) ∨
  (a = b ∧ b = 2 * c ∧ c = d ∧ d = e) ∨
  (a = b ∧ b = c ∧ c = 2 * d ∧ d = e) ∨
  (a = b ∧ b = c ∧ d = 2 * c ∧ d = e) ∨
  (a = b ∧ c = 2 * b ∧ c = d ∧ d = e) ∨
  (b = 2 * a ∧ b = c ∧ c = d ∧ d = 2 * e) ∨
  (b = 2 * a ∧ b = c ∧ c = d ∧ e = 2 * d)

def fivePathMatrix (a b c d e : ℤ) : Fin 5 → Fin 5 → ℤ :=
  !![-2 * a, max a b, 0, 0, 0;
     max a b, -2 * b, max b c, 0, 0;
     0, max b c, -2 * c, max c d, 0;
     0, 0, max c d, -2 * d, max d e;
     0, 0, 0, max d e, -2 * e]

def reverseFive : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 4 * Equiv.swap 1 3

def fivePathQuadraticForm (a b c d e : ℤ)
    (x0 x1 x2 x3 x4 : ℚ) : ℚ :=
  -2 * (a : ℚ) * x0 ^ 2 - 2 * (b : ℚ) * x1 ^ 2 -
    2 * (c : ℚ) * x2 ^ 2 - 2 * (d : ℚ) * x3 ^ 2 -
    2 * (e : ℚ) * x4 ^ 2 +
    2 * (max a b : ℚ) * x0 * x1 + 2 * (max b c : ℚ) * x1 * x2 +
    2 * (max c d : ℚ) * x2 * x3 + 2 * (max d e : ℚ) * x3 * x4

def fiveSupport {α : Type*} [DecidableEq α]
    (v : Fin 5 → α) (c : Fin 5 → ℚ) : α → ℚ := fun s =>
  (if s = v 0 then c 0 else 0) + (if s = v 1 then c 1 else 0) +
    (if s = v 2 then c 2 else 0) + (if s = v 3 then c 3 else 0) +
    (if s = v 4 then c 4 else 0)

def FiveFiniteWeightShape (a b c d e : ℤ) : Prop :=
  (a = b ∧ b = c ∧ c = d ∧ d = e) ∨
  (a = b ∧ b = c ∧ c = d ∧ e = 2 * d) ∨
  (a = 2 * b ∧ b = c ∧ c = d ∧ d = e) ∨
  (a = b ∧ b = c ∧ c = d ∧ d = 2 * e) ∨
  (b = 2 * a ∧ b = c ∧ c = d ∧ d = e)

/-! ### Ruling out the affine profiles

Eight of the thirteen weight shapes are affine: the chain's quadratic form
vanishes on an explicit nonzero vector, contradicting `hstrict`. The original
proof established that by unfolding `max_def` and running
`split_ifs <;> norm_cast at * <;> push_cast at * <;> nlinarith` in each case,
i.e. sixteen `nlinarith` calls per case and about two hundred in the
declaration, which is what overran the heartbeat budget.

At a *numeral* coordinate vector the form is the cast of an integer expression
that is linear in the five weights and the four `max`es, and `omega` decides
`max` on `ℤ`. So each case becomes a single `omega`. -/

/-- A strictly negative form cannot vanish at an integer point with `x0 ≠ 0`. -/
private lemma false_of_form_zero {a b c d e : ℤ}
    (hstrict : ∀ x0 x1 x2 x3 x4 : ℚ, x0 ≠ 0 →
      fivePathQuadraticForm a b c d e x0 x1 x2 x3 x4 < 0)
    (x0 x1 x2 x3 x4 : ℤ) (hx0 : x0 ≠ 0)
    (h : -2 * a * x0 ^ 2 - 2 * b * x1 ^ 2 - 2 * c * x2 ^ 2 - 2 * d * x3 ^ 2 -
      2 * e * x4 ^ 2 + 2 * max a b * (x0 * x1) + 2 * max b c * (x1 * x2) +
      2 * max c d * (x2 * x3) + 2 * max d e * (x3 * x4) = 0) : False := by
  have hneg := hstrict x0 x1 x2 x3 x4 (by exact_mod_cast hx0)
  unfold fivePathQuadraticForm at hneg
  have h' := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at h' hneg
  linarith

lemma negative_path_form_classification (a b c d e : ℤ)
    (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hstrict : ∀ x0 x1 x2 x3 x4 : ℚ, x0 ≠ 0 →
      fivePathQuadraticForm a b c d e x0 x1 x2 x3 x4 < 0)
    (hshape : FiveWeightShape a b c d e) : FiveFiniteWeightShape a b c d e := by
  rcases hshape with hshape | hshape | hshape | hshape | hshape | hshape |
    hshape | hshape | hshape | hshape | hshape | hshape | hshape
  · exact Or.inl hshape
  · exact Or.inr (Or.inl hshape)
  · exact Or.inr (Or.inr (Or.inl hshape))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hshape)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hshape)))
  · exact (false_of_form_zero hstrict 1 2 2 2 2 (by norm_num) (by omega)).elim
  · exact (false_of_form_zero hstrict 1 2 2 2 1 (by norm_num) (by omega)).elim
  · exact (false_of_form_zero hstrict 1 2 3 2 1 (by norm_num) (by omega)).elim
  · exact (false_of_form_zero hstrict 1 2 3 4 2 (by norm_num) (by omega)).elim
  · exact (false_of_form_zero hstrict 1 2 3 2 1 (by norm_num) (by omega)).elim
  · exact (false_of_form_zero hstrict 2 4 3 2 1 (by norm_num) (by omega)).elim
  · exact (false_of_form_zero hstrict 1 1 1 1 1 (by norm_num) (by omega)).elim
  · exact (false_of_form_zero hstrict 2 2 2 2 1 (by norm_num) (by omega)).elim

def fivePathQuadraticBase (a b c d e : ℤ) : ℚ :=
  -2 * ((a : ℚ) + b + c + d + e) +
    2 * ((max a b : ℚ) + max b c + max c d + max d e)

/-! ### The base value of the quadratic form

Same reduction: `fivePathQuadraticBase` is the cast of an integer expression
linear in the weights and the `max`es, so each of the thirteen shapes needs one
`omega` rather than a sixteen-way `split_ifs <;> nlinarith`. -/

private lemma base_eq_neg_two_mul {a b c d e w : ℤ}
    (h : -2 * (a + b + c + d + e) +
      2 * (max a b + max b c + max c d + max d e) = -2 * w) :
    fivePathQuadraticBase a b c d e = -2 * (w : ℚ) := by
  unfold fivePathQuadraticBase
  have h' := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at h' ⊢
  linarith [h']

lemma path_quadratic_base_shape (a b c d e : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hshape : FiveWeightShape a b c d e) :
    (∃ w : ℤ, 0 < w ∧ w ≤ a ∧
      fivePathQuadraticBase a b c d e = -2 * (w : ℚ)) ∨
      fivePathQuadraticBase a b c d e = 0 := by
  unfold FiveWeightShape at hshape
  rcases hshape with h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    first
    | exact Or.inl ⟨a, ha, le_rfl, base_eq_neg_two_mul (by omega)⟩
    | exact Or.inl ⟨b, hb, by omega, base_eq_neg_two_mul (by omega)⟩
    | exact Or.inl ⟨c, hc, by omega, base_eq_neg_two_mul (by omega)⟩
    | exact Or.inl ⟨d, hd, by omega, base_eq_neg_two_mul (by omega)⟩
    | exact Or.inl ⟨e, he, by omega, base_eq_neg_two_mul (by omega)⟩
    | exact Or.inr (by simpa using base_eq_neg_two_mul (w := 0) (by omega))

/-! ### Overlapping four-chains -/

lemma overlap_weight_shapes (a b c d e : ℤ)
    (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c) (_hd : 0 < d) (_he : 0 < e)
    (hleft : FourWeightShape a b c d)
    (hright : FourWeightShape b c d e) : FiveWeightShape a b c d e := by
  unfold FourWeightShape at hleft hright
  unfold FiveWeightShape
  rcases hleft with h | h | h | h | h | h | h <;>
    rcases hright with k | k | k | k | k | k | k <;> omega

lemma fourEdgePattern_weights (T : NumericalType)
    (i j k l : Fin T.componentCount)
    (h : FourEdgePattern T i j k l) :
    FourWeightShape (T.weight i) (T.weight j) (T.weight k) (T.weight l) := by
  rcases h with ⟨w, h | h | h | h | h | h | h⟩
  all_goals
    have h0 := congrFun h (0 : Fin 4)
    have h1 := congrFun h (1 : Fin 4)
    have h2 := congrFun h (2 : Fin 4)
    have h3 := congrFun h (3 : Fin 4)
    simp at h0 h1 h2 h3
    simp only [FourWeightShape]
    omega

lemma three_chain_edge_shapes (T : NumericalType)
    (hn : 3 < T.componentCount) (i j k : Fin T.componentCount)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hk : IsMinusTwoIndex T k) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hij0 : T.intersection i j ≠ 0)
    (hjk0 : T.intersection j k ≠ 0) :
    EdgeShape T i j ∧ EdgeShape T j k := by
  obtain ⟨v, hv, hr, hform⟩ :=
    exists_ordering_of_three_minus_two_indices T hn i j k hi hj hk
      hij hik hjk (Or.inr (Or.inl ⟨hij0, hjk0⟩))
  have hzero : T.intersection (v 0) (v 2) = 0 := by
    rcases hform with hA | hC | hB
    · rcases hA with ⟨_, _, _, _, _, _, h02, _, _, _, _, _, _, _, _⟩
      exact h02
    · rcases hC with ⟨_, _, _, _, _, _, h02, _, _, _, _, _, _, _, _⟩
      exact h02
    · rcases hB with ⟨_, _, _, _, _, _, h02, _, _, _, _, _, _, _, _⟩
      exact h02
  have horder := fin3_chain_order T i j k v hv hr hzero hij0 hjk0
  rcases hform with hA | hC | hB
  · rcases hA with ⟨w, hw0, hw1, hw2, _, h01, _, h10, _, h12, _, h21, _, _, _, _⟩
    rcases horder with h | h
    · exact ⟨Or.inl ⟨w, by simpa [h.1] using hw0,
          by simpa [h.2.1] using hw1, by simpa [h.1, h.2.1] using h01⟩,
        Or.inl ⟨w, by simpa [h.2.1] using hw1,
          by simpa [h.2.2] using hw2, by simpa [h.2.1, h.2.2] using h12⟩⟩
    · exact ⟨Or.inl ⟨w, by simpa [h.2.2] using hw2,
          by simpa [h.2.1] using hw1, by simpa [h.2.2, h.2.1] using h21⟩,
        Or.inl ⟨w, by simpa [h.2.1] using hw1,
          by simpa [h.1] using hw0, by simpa [h.2.1, h.1] using h10⟩⟩
  · rcases hC with ⟨w, hw0, hw1, hw2, _, h01, _, h10, _, h12, _, h21, _, _, _, _⟩
    rcases horder with h | h
    · exact ⟨Or.inl ⟨w, by simpa [h.1] using hw0,
          by simpa [h.2.1] using hw1, by simpa [h.1, h.2.1] using h01⟩,
        Or.inr (Or.inl ⟨w, by simpa [h.2.1] using hw1,
          by simpa [h.2.2] using hw2, by simpa [h.2.1, h.2.2] using h12⟩)⟩
    · exact ⟨Or.inr (Or.inr ⟨w, by simpa [h.2.2] using hw2,
          by simpa [h.2.1] using hw1, by simpa [h.2.2, h.2.1] using h21⟩),
        Or.inl ⟨w, by simpa [h.2.1] using hw1,
          by simpa [h.1] using hw0, by simpa [h.2.1, h.1] using h10⟩⟩
  · rcases hB with ⟨w, hw0, hw1, hw2, _, h01, _, h10, _, h12, _, h21, _, _, _, _⟩
    rcases horder with h | h
    · exact ⟨Or.inl ⟨2 * w, by simpa [h.1] using hw0,
          by simpa [h.2.1] using hw1, by simpa [h.1, h.2.1] using h01⟩,
        Or.inr (Or.inr ⟨w, by simpa [h.2.1] using hw1,
          by simpa [h.2.2] using hw2, by simpa [h.2.1, h.2.2] using h12⟩)⟩
    · exact ⟨Or.inr (Or.inl ⟨w, by simpa [h.2.2] using hw2,
          by simpa [h.2.1] using hw1, by simpa [h.2.2, h.2.1] using h21⟩),
        Or.inl ⟨2 * w, by simpa [h.2.1] using hw1,
          by simpa [h.1] using hw0, by simpa [h.2.1, h.1] using h10⟩⟩

private lemma four_chain_form (T : NumericalType)
    (hn : 4 < T.componentCount) (i j k l : Fin T.componentCount)
    (hdistinct : Function.Injective ![i, j, k, l])
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hk : IsMinusTwoIndex T k) (hl : IsMinusTwoIndex T l)
    (hij : T.intersection i j ≠ 0) (hjk : T.intersection j k ≠ 0)
    (hkl : T.intersection k l ≠ 0) :
    ∃ (σ : Equiv.Perm (Fin 4)) (w : ℤ),
      ((σ.symm 0 = 0 ∧ σ.symm 1 = 1 ∧ σ.symm 2 = 2 ∧ σ.symm 3 = 3) ∨
        (σ.symm 0 = 3 ∧ σ.symm 1 = 2 ∧ σ.symm 2 = 1 ∧ σ.symm 3 = 0)) ∧
      (∀ p q : Fin 4, (p : ℕ) + 2 ≤ q ∨ (q : ℕ) + 2 ≤ p →
        T.intersection (![i, j, k, l] (σ p)) (![i, j, k, l] (σ q)) = 0) ∧
      ((fun p => T.weight (![i, j, k, l] (σ p))) = ![w, w, w, w] ∨
        (fun p => T.weight (![i, j, k, l] (σ p))) = ![w, w, w, 2 * w] ∨
        (fun p => T.weight (![i, j, k, l] (σ p))) = ![2 * w, 2 * w, 2 * w, w] ∨
        (fun p => T.weight (![i, j, k, l] (σ p))) = ![w, w, 2 * w, 2 * w]) := by
  obtain ⟨σ, w, hform⟩ :=
    four_minus_two_indices T hn i j k l hdistinct hi hj hk hl hij hjk hkl
  have hadj (p q : Fin 4) (hpq : p ≠ q)
      (hne : T.intersection (![i, j, k, l] (σ p)) (![i, j, k, l] (σ q)) ≠ 0) :
      (p : ℕ) + 1 = q ∨ (q : ℕ) + 1 = p := by
    rcases hform with ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩ <;>
      · have h := congrFun (congrFun hm p) q
        fin_cases p <;> fin_cases q <;> simp_all
  have hvec : ![σ.symm 0, σ.symm 1, σ.symm 2, σ.symm 3] = σ.symm := by
    ext x
    fin_cases x <;> rfl
  have horder := fin4_path_order _ _ _ _ (hvec ▸ σ.symm.injective)
    (hadj _ _ (σ.symm.injective.ne (by decide)) (by simpa using hij))
    (hadj _ _ (σ.symm.injective.ne (by decide)) (by simpa using hjk))
    (hadj _ _ (σ.symm.injective.ne (by decide)) (by simpa using hkl))
  refine ⟨σ, w, horder, ?_, ?_⟩
  · intro p q hpq
    rcases hform with ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩ <;>
      · have h := congrFun (congrFun hm p) q
        fin_cases p <;> fin_cases q <;> simp_all
  · rcases hform with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
    exacts [Or.inl hw, Or.inr (Or.inl hw), Or.inr (Or.inr (Or.inl hw)),
      Or.inr (Or.inr (Or.inr hw))]

lemma four_chain_endpoint_intersection_zero (T : NumericalType)
    (hn : 4 < T.componentCount) (i j k l : Fin T.componentCount)
    (hdistinct : Function.Injective ![i, j, k, l])
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hk : IsMinusTwoIndex T k) (hl : IsMinusTwoIndex T l)
    (hij : T.intersection i j ≠ 0) (hjk : T.intersection j k ≠ 0)
    (hkl : T.intersection k l ≠ 0) :
    T.intersection i k = 0 ∧ T.intersection i l = 0 ∧
      T.intersection j l = 0 := by
  obtain ⟨σ, w, horder, hzero, -⟩ :=
    four_chain_form T hn i j k l hdistinct hi hj hk hl hij hjk hkl
  have h02 := hzero (σ.symm 0) (σ.symm 2)
  have h03 := hzero (σ.symm 0) (σ.symm 3)
  have h13 := hzero (σ.symm 1) (σ.symm 3)
  simp only [Equiv.apply_symm_apply] at h02 h03 h13
  rcases horder with h | h <;>
    simpa [h.1, h.2.1, h.2.2.1, h.2.2.2] using And.intro h02 (And.intro h03 h13)

/-- A weight profile read through `σ` is the profile itself, or its reversal when `σ` reverses. -/
private lemma weight_profile_of_sigma (T : NumericalType)
    (base : Fin 4 → Fin T.componentCount) (σ : Equiv.Perm (Fin 4))
    (hσ : (∀ x : Fin 4, σ x = x) ∨ (∀ x : Fin 4, σ x = ⟨3 - x.val, by omega⟩))
    (source target : Fin 4 → ℤ) (hsource : (fun p => T.weight (base (σ p))) = source)
    (hrev : ∀ p, source (Fin.rev p) = target p) :
    (fun p => T.weight (base p)) = source ∨ (fun p => T.weight (base p)) = target := by
  rcases hσ with hσ | hσ
  · left
    ext p
    simpa [hσ p] using congrFun hsource p
  · right
    ext p
    have hh := congrFun hsource (Fin.rev p)
    rw [show σ (Fin.rev p) = p from by rw [hσ]; ext; simp [Fin.rev]; omega] at hh
    exact hh.trans (hrev p)

lemma four_chain_edge_pattern (T : NumericalType)
    (hn : 4 < T.componentCount) (i j k l : Fin T.componentCount)
    (hdistinct : Function.Injective ![i, j, k, l])
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hk : IsMinusTwoIndex T k) (hl : IsMinusTwoIndex T l)
    (hij : T.intersection i j ≠ 0) (hjk : T.intersection j k ≠ 0)
    (hkl : T.intersection k l ≠ 0) : FourEdgePattern T i j k l := by
  obtain ⟨σ, w, horder, -, hw⟩ :=
    four_chain_form T hn i j k l hdistinct hi hj hk hl hij hjk hkl
  have hσ := fin4_sigma_path_order σ horder
  refine ⟨w, ?_⟩
  rcases hw with hw | hw | hw | hw
  · obtain hp | hp := weight_profile_of_sigma T _ σ hσ _ ![w, w, w, w] hw
      (fun p => by fin_cases p <;> simp [Fin.rev])
    exacts [Or.inl hp, Or.inl hp]
  · obtain hp | hp := weight_profile_of_sigma T _ σ hσ _ ![2 * w, w, w, w] hw
      (fun p => by fin_cases p <;> simp [Fin.rev])
    exacts [Or.inr (Or.inl hp), Or.inr (Or.inr (Or.inl hp))]
  · obtain hp | hp := weight_profile_of_sigma T _ σ hσ _ ![w, 2 * w, 2 * w, 2 * w] hw
      (fun p => by fin_cases p <;> simp [Fin.rev])
    exacts [Or.inr (Or.inr (Or.inr (Or.inl hp))), Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))]
  · obtain hp | hp := weight_profile_of_sigma T _ σ hσ _ ![2 * w, 2 * w, w, w] hw
      (fun p => by fin_cases p <;> simp [Fin.rev])
    exacts [Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))),
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp)))))]

end AlgebraicGeometry.NumericalType
