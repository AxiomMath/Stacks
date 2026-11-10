module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Genus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.TwoVertices
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.ThreeVertices
public import Mathlib
public import Mathlib.Data.Fin.VecNotation

/-!
# Four-vertex chains: overlapping triples

The five ordered shapes `TripleA`, `TripleC`, `TripleCr`, `TripleB`, `TripleBr` of a chain of
three minus-two indices, the classification of how two consecutive triples of a four-vertex
chain can overlap, the expansion of the quadratic form on a vector supported on four
coordinates, and the nonexistence of a nonzero isotropic vector supported on four components
of a numerical type with more than four components.
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

/-! ### Four-vertex chains -/

/-- An injective `v : Fin 3 → α` with range `{i, j, k}` lists `i`, `j`, `k` in one of the six
orders. -/
public lemma fin3_range_enum {α : Type*} {i j k : α}
    {v : Fin 3 → α} (hv : Function.Injective v)
    (hr : Set.range v = {i, j, k}) :
    (v 0 = i ∧ v 1 = j ∧ v 2 = k) ∨
    (v 0 = i ∧ v 1 = k ∧ v 2 = j) ∨
    (v 0 = j ∧ v 1 = i ∧ v 2 = k) ∨
    (v 0 = j ∧ v 1 = k ∧ v 2 = i) ∨
    (v 0 = k ∧ v 1 = i ∧ v 2 = j) ∨
    (v 0 = k ∧ v 1 = j ∧ v 2 = i) := by
  have hm (x : Fin 3) : v x = i ∨ v x = j ∨ v x = k := by
    have hx : v x ∈ Set.range v := ⟨x, rfl⟩
    rw [hr] at hx
    simpa using hx
  have hval (x y : Fin 3) (hne : x ≠ y) : v x ≠ v y := fun h => hne (hv h)
  rcases hm 0 with h0 | h0 | h0 <;>
  rcases hm 1 with h1 | h1 | h1 <;>
    rcases hm 2 with h2 | h2 | h2 <;> aesop

/-- If `v` enumerates the components `i`, `j`, `k`, the intersection number of `v 0` and `v 2`
vanishes and those of `i, j` and of `j, k` do not, then `v` lists them as `i, j, k` or
`k, j, i`. -/
public lemma fin3_chain_order (T : NumericalType)
    (i j k : Fin T.componentCount) (v : Fin 3 → Fin T.componentCount)
    (hv : Function.Injective v) (hr : Set.range v = {i, j, k})
    (hzero : T.intersection (v 0) (v 2) = 0)
    (hij : T.intersection i j ≠ 0) (hjk : T.intersection j k ≠ 0) :
    (v 0 = i ∧ v 1 = j ∧ v 2 = k) ∨
    (v 0 = k ∧ v 1 = j ∧ v 2 = i) := by
  rcases fin3_range_enum hv hr with h | h | h | h | h | h <;>
    rcases h with ⟨h0, h1, h2⟩ <;>
    simp_all [NumericalType.intersection_symm]

def TripleA (T : NumericalType) (a b c : Fin T.componentCount)
    (w : ℤ) : Prop :=
  T.weight a = w ∧ T.weight b = w ∧ T.weight c = w ∧
  T.intersection a a = -2 * w ∧ T.intersection a b = w ∧
  T.intersection a c = 0 ∧ T.intersection b a = w ∧
  T.intersection b b = -2 * w ∧ T.intersection b c = w ∧
  T.intersection c a = 0 ∧ T.intersection c b = w ∧
  T.intersection c c = -2 * w ∧
  2 * T.multiplicity a ≥ T.multiplicity b ∧
  2 * T.multiplicity b ≥ T.multiplicity a + T.multiplicity c ∧
  2 * T.multiplicity c ≥ T.multiplicity b

def TripleC (T : NumericalType) (a b c : Fin T.componentCount)
    (w : ℤ) : Prop :=
  T.weight a = w ∧ T.weight b = w ∧ T.weight c = 2 * w ∧
  T.intersection a a = -2 * w ∧ T.intersection a b = w ∧
  T.intersection a c = 0 ∧ T.intersection b a = w ∧
  T.intersection b b = -2 * w ∧ T.intersection b c = 2 * w ∧
  T.intersection c a = 0 ∧ T.intersection c b = 2 * w ∧
  T.intersection c c = -4 * w ∧
  2 * T.multiplicity a ≥ T.multiplicity b ∧
  2 * T.multiplicity b ≥ T.multiplicity a + 2 * T.multiplicity c ∧
  2 * T.multiplicity c ≥ T.multiplicity b

def TripleCr (T : NumericalType) (a b c : Fin T.componentCount)
    (w : ℤ) : Prop :=
  T.weight a = 2 * w ∧ T.weight b = w ∧ T.weight c = w ∧
  T.intersection a a = -4 * w ∧ T.intersection a b = 2 * w ∧
  T.intersection a c = 0 ∧ T.intersection b a = 2 * w ∧
  T.intersection b b = -2 * w ∧ T.intersection b c = w ∧
  T.intersection c a = 0 ∧ T.intersection c b = w ∧
  T.intersection c c = -2 * w ∧
  2 * T.multiplicity c ≥ T.multiplicity b ∧
  2 * T.multiplicity b ≥ T.multiplicity c + 2 * T.multiplicity a ∧
  2 * T.multiplicity a ≥ T.multiplicity b

def TripleB (T : NumericalType) (a b c : Fin T.componentCount)
    (w : ℤ) : Prop :=
  T.weight a = 2 * w ∧ T.weight b = 2 * w ∧ T.weight c = w ∧
  T.intersection a a = -4 * w ∧ T.intersection a b = 2 * w ∧
  T.intersection a c = 0 ∧ T.intersection b a = 2 * w ∧
  T.intersection b b = -4 * w ∧ T.intersection b c = 2 * w ∧
  T.intersection c a = 0 ∧ T.intersection c b = 2 * w ∧
  T.intersection c c = -2 * w ∧
  2 * T.multiplicity a ≥ T.multiplicity b ∧
  2 * T.multiplicity b ≥ T.multiplicity a + T.multiplicity c ∧
  T.multiplicity c ≥ T.multiplicity b

def TripleBr (T : NumericalType) (a b c : Fin T.componentCount)
    (w : ℤ) : Prop :=
  T.weight a = w ∧ T.weight b = 2 * w ∧ T.weight c = 2 * w ∧
  T.intersection a a = -2 * w ∧ T.intersection a b = 2 * w ∧
  T.intersection a c = 0 ∧ T.intersection b a = 2 * w ∧
  T.intersection b b = -4 * w ∧ T.intersection b c = 2 * w ∧
  T.intersection c a = 0 ∧ T.intersection c b = 2 * w ∧
  T.intersection c c = -4 * w ∧
  2 * T.multiplicity c ≥ T.multiplicity b ∧
  2 * T.multiplicity b ≥ T.multiplicity a + T.multiplicity c ∧
  T.multiplicity a ≥ T.multiplicity b

inductive TripleShape (T : NumericalType)
    (a b c : Fin T.componentCount) : Prop where
  | a (w : ℤ) : TripleA T a b c w → TripleShape T a b c
  | c (w : ℤ) : TripleC T a b c w → TripleShape T a b c
  | cr (w : ℤ) : TripleCr T a b c w → TripleShape T a b c
  | b (w : ℤ) : TripleB T a b c w → TripleShape T a b c
  | br (w : ℤ) : TripleBr T a b c w → TripleShape T a b c

theorem tripleShapeOfOr (T : NumericalType) (a b c : Fin T.componentCount)
    (h : (∃ w, TripleA T a b c w) ∨ (∃ w, TripleC T a b c w) ∨
      (∃ w, TripleCr T a b c w) ∨ (∃ w, TripleB T a b c w) ∨
      (∃ w, TripleBr T a b c w)) : TripleShape T a b c := by
  rcases h with ⟨w, hw⟩ | ⟨w, hw⟩ | ⟨w, hw⟩ | ⟨w, hw⟩ | ⟨w, hw⟩
  · exact .a w hw
  · exact .c w hw
  · exact .cr w hw
  · exact .b w hw
  · exact .br w hw

theorem ordered_triple_shape (T : NumericalType)
    (hn : 3 < T.componentCount) (a b c : Fin T.componentCount)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : IsMinusTwoIndex T a) (hb : IsMinusTwoIndex T b)
    (hc : IsMinusTwoIndex T c)
    (hab0 : T.intersection a b ≠ 0) (hbc0 : T.intersection b c ≠ 0) :
    (∃ w, TripleA T a b c w) ∨ (∃ w, TripleC T a b c w) ∨
    (∃ w, TripleCr T a b c w) ∨ (∃ w, TripleB T a b c w) ∨
    (∃ w, TripleBr T a b c w) := by
  obtain ⟨v, hv, hr, hform⟩ :=
    exists_ordering_of_three_minus_two_indices T hn a b c ha hb hc hab hac hbc
      (Or.inr (Or.inl ⟨hab0, hbc0⟩))
  have hzero : T.intersection (v 0) (v 2) = 0 := by
    rcases hform with ⟨_, -, -, -, -, -, h, -⟩ | ⟨_, -, -, -, -, -, h, -⟩ |
      ⟨_, -, -, -, -, -, h, -⟩ <;> exact h
  have horder := fin3_chain_order T a b c v hv hr hzero hab0 hbc0
  rcases horder with horder | horder
  · rcases hform with ⟨w, hA⟩ | ⟨w, hC⟩ | ⟨w, hB⟩
    · exact Or.inl ⟨w, by simpa [TripleA, horder.1, horder.2.1, horder.2.2] using hA⟩
    · exact Or.inr (Or.inl ⟨w, by simpa [TripleC, horder.1, horder.2.1, horder.2.2] using hC⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨w, by simpa [TripleB, horder.1, horder.2.1, horder.2.2]
      using hB⟩)))
  · rcases hform with ⟨w, hA⟩ | ⟨w, hC⟩ | ⟨w, hB⟩
    · refine Or.inl ⟨w, ?_⟩
      simp only [TripleA, horder.1, horder.2.1, horder.2.2] at hA ⊢
      omega
    · refine Or.inr (Or.inr (Or.inl ⟨w, ?_⟩))
      simp only [TripleCr, horder.1, horder.2.1, horder.2.2] at hC ⊢
      omega
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨w, ?_⟩)))
      simp only [TripleBr, horder.1, horder.2.1, horder.2.2] at hB ⊢
      omega

theorem overlapping_triples (T : NumericalType)
    (i j k l : Fin T.componentCount)
    (hL : TripleShape T i j k) (hR : TripleShape T j k l) :
    (∃ w, TripleA T i j k w ∧ TripleA T j k l w) ∨
    (∃ w, TripleA T i j k w ∧ TripleC T j k l w) ∨
    (∃ w, TripleA T i j k (2 * w) ∧ TripleB T j k l w) ∨
    (∃ w, TripleC T i j k w ∧ TripleBr T j k l w) ∨
    (∃ w, TripleCr T i j k w ∧ TripleA T j k l w) ∨
    (∃ w, TripleB T i j k w ∧ TripleCr T j k l w) ∨
    (∃ w, TripleBr T i j k w ∧ TripleA T j k l (2 * w)) ∨
    (∃ w, TripleCr T i j k w ∧ TripleC T j k l w) ∨
    (∃ w, TripleBr T i j k w ∧ TripleB T j k l w) ∨
    (∃ w, TripleBr T i j k w ∧ TripleC T j k l (2 * w)) ∨
    (∃ w, TripleCr T i j k (2 * w) ∧ TripleB T j k l w) := by
  cases hL <;> cases hR
  case a.a u hL v hR =>
    obtain rfl : u = v := by simp only [TripleA] at hL hR; omega
    exact .inl ⟨_, hL, hR⟩
  case a.c u hL v hR =>
    obtain rfl : u = v := by simp only [TripleA, TripleC] at hL hR; omega
    right
    exact .inl ⟨_, hL, hR⟩
  case a.b u hL v hR =>
    obtain rfl : u = 2 * v := by simp only [TripleA, TripleB] at hL hR; omega
    iterate 2 right
    exact .inl ⟨_, hL, hR⟩
  case c.br u hL v hR =>
    obtain rfl : u = v := by simp only [TripleC, TripleBr] at hL hR; omega
    iterate 3 right
    exact .inl ⟨_, hL, hR⟩
  case cr.a u hL v hR =>
    obtain rfl : u = v := by simp only [TripleCr, TripleA] at hL hR; omega
    iterate 4 right
    exact .inl ⟨_, hL, hR⟩
  case b.cr u hL v hR =>
    obtain rfl : u = v := by simp only [TripleB, TripleCr] at hL hR; omega
    iterate 5 right
    exact .inl ⟨_, hL, hR⟩
  case br.a u hL v hR =>
    obtain rfl : v = 2 * u := by simp only [TripleBr, TripleA] at hL hR; omega
    iterate 6 right
    exact .inl ⟨_, hL, hR⟩
  case cr.c u hL v hR =>
    obtain rfl : u = v := by simp only [TripleCr, TripleC] at hL hR; omega
    iterate 7 right
    exact .inl ⟨_, hL, hR⟩
  case br.b u hL v hR =>
    obtain rfl : u = v := by simp only [TripleBr, TripleB] at hL hR; omega
    iterate 8 right
    exact .inl ⟨_, hL, hR⟩
  case br.c u hL v hR =>
    obtain rfl : v = 2 * u := by simp only [TripleBr, TripleC] at hL hR; omega
    iterate 9 right
    exact .inl ⟨_, hL, hR⟩
  case cr.b u hL v hR =>
    obtain rfl : u = 2 * v := by simp only [TripleCr, TripleB] at hL hR; omega
    iterate 10 right
    exact ⟨_, hL, hR⟩
  all_goals
    simp only [TripleA, TripleC, TripleCr, TripleB, TripleBr] at *
    have := T.weight_pos i
    have := T.weight_pos j
    exfalso
    omega

theorem dotProduct_mulVec_four_formula {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℚ) (hA : A.IsSymm)
    (a b c d : α) (_hab : a ≠ b) (_hac : a ≠ c) (_had : a ≠ d)
    (_hbc : b ≠ c) (_hbd : b ≠ d) (_hcd : c ≠ d)
    (c0 c1 c2 c3 : ℚ) :
    let x : α → ℚ := fun s =>
      (if s = a then c0 else 0) + (if s = b then c1 else 0) +
        (if s = c then c2 else 0) + (if s = d then c3 else 0)
    x ⬝ᵥ (A *ᵥ x) =
      c0*c0*A a a + c0*c1*A a b + c0*c2*A a c + c0*c3*A a d +
      c1*c0*A b a + c1*c1*A b b + c1*c2*A b c + c1*c3*A b d +
      c2*c0*A c a + c2*c1*A c b + c2*c2*A c c + c2*c3*A c d +
      c3*c0*A d a + c3*c1*A d b + c3*c2*A d c + c3*c3*A d d := by
  dsimp
  simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, add_mul, mul_add, hA.apply]
  ring

theorem no_affine_four_chain (T : NumericalType)
    (hn : 4 < T.componentCount)
    (v : Fin 4 → Fin T.componentCount) (hv : Function.Injective v)
    (c : Fin 4 → ℚ) (hc0 : c 0 ≠ 0)
    (hlocal :
      c 0 * c 0 * (T.intersection (v 0) (v 0) : ℚ) +
      c 0 * c 1 * (T.intersection (v 0) (v 1) : ℚ) +
      c 0 * c 2 * (T.intersection (v 0) (v 2) : ℚ) +
      c 0 * c 3 * (T.intersection (v 0) (v 3) : ℚ) +
      c 1 * c 0 * (T.intersection (v 1) (v 0) : ℚ) +
      c 1 * c 1 * (T.intersection (v 1) (v 1) : ℚ) +
      c 1 * c 2 * (T.intersection (v 1) (v 2) : ℚ) +
      c 1 * c 3 * (T.intersection (v 1) (v 3) : ℚ) +
      c 2 * c 0 * (T.intersection (v 2) (v 0) : ℚ) +
      c 2 * c 1 * (T.intersection (v 2) (v 1) : ℚ) +
      c 2 * c 2 * (T.intersection (v 2) (v 2) : ℚ) +
      c 2 * c 3 * (T.intersection (v 2) (v 3) : ℚ) +
      c 3 * c 0 * (T.intersection (v 3) (v 0) : ℚ) +
      c 3 * c 1 * (T.intersection (v 3) (v 1) : ℚ) +
      c 3 * c 2 * (T.intersection (v 3) (v 2) : ℚ) +
      c 3 * c 3 * (T.intersection (v 3) (v 3) : ℚ) = 0) :
    False := by
  classical
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun i j => (T.intersection i j : ℚ)
  let m : Fin T.componentCount → ℚ := fun i => (T.multiplicity i : ℚ)
  let x : Fin T.componentCount → ℚ := fun t =>
    (if t = v 0 then c 0 else 0) + (if t = v 1 then c 1 else 0) +
      (if t = v 2 then c 2 else 0) + (if t = v 3 then c 3 else 0)
  have hsymm : A.IsSymm := by
    ext i j
    rw [Matrix.transpose_apply]
    simp [A, T.intersection_symm]
  have hne (p q : Fin 4) (h : p ≠ q) : v p ≠ v q := fun he => h (hv he)
  have h01 := hne 0 1 (by decide)
  have h02 := hne 0 2 (by decide)
  have h03 := hne 0 3 (by decide)
  have h12 := hne 1 2 (by decide)
  have h13 := hne 1 3 (by decide)
  have h23 := hne 2 3 (by decide)
  have hq : x ⬝ᵥ (A *ᵥ x) = 0 := by
    have hf := dotProduct_mulVec_four_formula A hsymm (v 0) (v 1) (v 2) (v 3)
      h01 h02 h03 h12 h13 h23 (c 0) (c 1) (c 2) (c 3)
    rw [hf]
    simpa [A] using hlocal
  have hAoff : ∀ i j, i ≠ j → 0 ≤ A i j := by
    intro i j hij
    change 0 ≤ (T.intersection i j : ℚ)
    exact_mod_cast T.intersection_nonneg i j hij
  have hmpos : ∀ i, 0 < m i := by
    intro i
    change 0 < (T.multiplicity i : ℚ)
    exact_mod_cast T.multiplicity_pos i
  have hAm : A *ᵥ m = 0 := by
    ext i
    have hrow : (∑ j, (T.intersection i j : ℚ) * (T.multiplicity j : ℚ)) = 0 := by
      exact_mod_cast T.intersection_mul_multiplicity i
    change (∑ j, A i j * m j) = 0
    simpa [A, m] using hrow
  have hconnected : ∀ I : Set (Fin T.componentCount), I.Nonempty →
      I ≠ Set.univ → ¬ ∀ i ∈ I, ∀ j ∉ I, A i j = 0 := by
    intro I hI hne hcut
    apply T.connected
    refine ⟨I, hI, hne, ?_⟩
    intro i hi j hj
    have hh := hcut i hi j hj
    change (T.intersection i j : ℚ) = 0 at hh
    exact_mod_cast hh
  have hscalar :=
    (dotProduct_mulVec_eq_zero_iff_of_positive_kernel hsymm hAoff hmpos hAm
      hconnected).mp hq
  rcases hscalar with ⟨q, hx⟩
  have hnotSurj : ¬ Function.Surjective v := by
    intro hs
    have hle : Fintype.card (Fin T.componentCount) ≤ Fintype.card (Fin 4) :=
      Fintype.card_le_of_surjective v hs
    have hle' : T.componentCount ≤ 4 := by simpa using hle
    omega
  obtain ⟨u, hu⟩ : ∃ u, ∀ p : Fin 4, v p ≠ u := by
    by_contra hno
    apply hnotSurj
    intro u
    by_contra hnot
    apply hno
    refine ⟨u, ?_⟩
    intro p hp
    exact hnot ⟨p, hp⟩
  have hxzero : x u = 0 := by
    have hu' : ∀ p : Fin 4, u ≠ v p := fun p => (hu p).symm
    simp [x, hu']
  have hqzero : q = 0 := by
    have heq := congrFun hx u
    have hmul : q * m u = 0 := by
      simpa [smul_eq_mul, hxzero, m] using heq
    rcases mul_eq_zero.mp hmul with hq | hmu
    · exact hq
    · have : (0 : ℚ) < m u := hmpos u
      linarith
  have hxone : x (v 0) = c 0 := by
    simp [x, h01, h02, h03]
  have heq0 := congrFun hx (v 0)
  rw [hxone, hqzero] at heq0
  have hc0zero : c 0 = 0 := by simpa [m] using heq0
  exact hc0 hc0zero

end AlgebraicGeometry.NumericalType
