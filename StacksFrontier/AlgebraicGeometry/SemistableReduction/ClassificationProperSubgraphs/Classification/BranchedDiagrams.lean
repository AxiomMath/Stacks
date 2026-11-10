module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic.Tauto
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.AffineE7
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.ChainDiagrams
import all StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.ChainDiagrams
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.IncidenceGraph
import all StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.IncidenceGraph
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.TreeShape
import all StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.TreeShape
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Dynkin
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.E8
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.AffineE6
public import StacksCore.Tactic.StacksAttribute

/-!
# Classification of connected proper subgraphs of minus-two indices

Every connected proper set of at least two minus-two indices in a numerical
type is, after reordering, one of the finite Dynkin configurations: types `A`,
`B`, `C`, `D` on any admissible number of vertices, and the exceptional types
`E₆`, `E₇`, `E₈`, `F₄`, `G₂`.

Knowing that the incidence graph is a tree of maximum degree three with at most
one trivalent vertex, the branched shapes are matched against the diagram
families, one case per vertex count and branch position, using the `D₅`, `E₆`,
`E₇` and `E₈` classifications and the nonexistence of the affine diagrams `Ẽ₆`,
`Ẽ₇` and `Ẽ₈`.

## Main results

* `AlgebraicGeometry.NumericalType.classify_connected_proper_minusTwo_subgraph`:
  the classification.
* `AlgebraicGeometry.NumericalType.connected_erase_leaf`: deleting a leaf from a connected set of
  components leaves it connected.

## Implementation notes

An ordering of the subset is an injective map from `Fin I.card` with range
exactly `I`. The genus is not fixed, since its value plays no part in the
classification.

## References

* [Stacks Project, Tag 0C8Q](https://stacks.math.columbia.edu/tag/0C8Q)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

open Matrix

private lemma no_four_neighbors_of_degree_le_three {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x : V, G.degree x ≤ 3) :
    ∀ (x a b c d : V), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      G.Adj x a → G.Adj x b → G.Adj x c → G.Adj x d → False := by
  classical
  intro x a b c d hab hac had hbc hbd hcd hxa hxb hxc hxd
  let : Fintype (G.neighborSet x) := Subtype.fintype _
  let f : Fin 4 → G.neighborSet x := ![
    ⟨a, (G.mem_neighborSet x a).mpr hxa⟩,
    ⟨b, (G.mem_neighborSet x b).mpr hxb⟩,
    ⟨c, (G.mem_neighborSet x c).mpr hxc⟩,
    ⟨d, (G.mem_neighborSet x d).mpr hxd⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hcard := Fintype.card_le_of_injective f hf
  rw [G.card_neighborSet_eq_degree] at hcard
  have hcard' : 4 ≤ G.degree x := by simpa [Fintype.card_fin] using hcard
  have : 4 ≤ 3 := hcard'.trans (hdeg x)
  omega

/-- A family of distinct elements of `I`, indexed by `Fin I.card`, is an ordering of `I` by
minus-two indices. -/
private lemma subtype_family_facts (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hminus : ∀ i ∈ I, IsMinusTwoIndex T i) {n : ℕ}
    (hn : I.card = n) (q : Fin n → {i // i ∈ I}) (hq : Function.Injective q) :
    Function.Injective (fun r => (q r).val) ∧
      Set.range (fun r => (q r).val) = (I : Set (Fin T.componentCount)) ∧
        ∀ r, IsMinusTwoIndex T (q r).val := by
  have hv : Function.Injective (fun r => (q r).val) := Subtype.val_injective.comp hq
  refine ⟨hv, ?_, fun r => hminus _ (q r).property⟩
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ I.finite_toSet
  · rintro _ ⟨r, rfl⟩
    exact (q r).property
  · rw [Set.ncard_range_of_injective hv]
    simp [hn]

private lemma dynkin_of_d5_subtypes (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hfive : I.card = 5)
    (hproper : I.card < T.componentCount)
    (hminus : ∀ i ∈ I, IsMinusTwoIndex T i)
    (z a x b c : {i // i ∈ I})
    (hzx : z ≠ x) (hzb : z ≠ b) (hzc : z ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (eza : (minusTwoGraph T I).Adj z a)
    (eax : (minusTwoGraph T I).Adj a x)
    (exb : (minusTwoGraph T I).Adj x b)
    (exc : (minusTwoGraph T I).Adj x c) :
    ∃ v : Fin 5 → Fin T.componentCount,
      Function.Injective v ∧ Set.range v = (I : Set (Fin T.componentCount)) ∧
        ∃ d w, IsDynkinConfiguration T v d w := by
  obtain ⟨hv, hvRange, hminusV⟩ := subtype_family_facts T I hminus hfive ![z, a, x, b, c]
    (by
      intro r s hrs
      fin_cases r <;> fin_cases s <;> simp_all [eza.ne, eax.ne, exb.ne, exc.ne,
        eza.ne.symm, eax.ne.symm, exb.ne.symm, exc.ne.symm])
  obtain ⟨d, w, hcfg⟩ := dynkin_of_d5_ordering T (by omega) _ hv hminusV
    eza.2 eax.2 exb.2 exc.2
  exact ⟨_, hv, hvRange, d, w, hcfg⟩

private lemma dynkin_of_fork {t : ℕ} (T : NumericalType)
    (ht : 4 < t) (hn : t + 1 < T.componentCount)
    (v : Fin (t + 1) → Fin T.componentCount) (hv : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hchain : ∀ r s : Fin (t + 1), s.val = r.val + 1 → s.val < t →
      T.intersection (v r) (v s) ≠ 0)
    (hbranch : T.intersection (v ⟨t - 2, by omega⟩) (v ⟨t, by omega⟩) ≠ 0) :
    ∃ d w, IsDynkinConfiguration T v d w := by
  classical
  obtain ⟨w, hw, he, hb, hz⟩ := eq_fork_of_isMinusTwoIndex
    T t ht hn v hv hminus
    (fun j => hchain _ _ (by simp) (by simpa using Nat.add_lt_of_lt_sub j.isLt))
    hbranch
  have hpos : 0 < w := (hw 0) ▸ T.weight_pos (v 0)
  have hweight : ∀ r, T.weight (v r) = DynkinShape.D.weightFactor r * w := by
    simpa [DynkinShape.weightFactor] using hw
  have hupper (r s : Fin (t + 1)) (hrs : r < s) :
      T.intersection (v r) (v s) = if DynkinShape.D.Edge r s then w else 0 := by
    by_cases hcon : s.val = r.val + 1 ∧ r.val < t - 1
    · have hh := he ⟨r.val, hcon.2⟩
      have heq : (⟨r.val + 1, by omega⟩ : Fin (t + 1)) = s := Fin.ext hcon.1.symm
      dsimp at hh
      rw [heq] at hh
      rw [hh, ite_eq_left]
      simp only [DynkinShape.Edge]
      left
      exact ⟨Or.inl hcon.1.symm, by omega, by omega⟩
    · by_cases hbr : s.val = t ∧ r.val = t - 2
      · have hr : r = ⟨t - 2, by omega⟩ := Fin.ext hbr.2
        have hs : s = ⟨t, by omega⟩ := Fin.ext hbr.1
        have hed : DynkinShape.D.Edge r s := by
          simp only [DynkinShape.Edge]
          right; left; constructor <;> omega
        rw [ite_eq_left hed]
        simpa only [hr, hs] using hb
      · have hh := hz s r hrs hcon hbr
        rw [T.intersection_symm, hh, ite_eq_right]
        simp only [DynkinShape.Edge]
        intro h
        rcases h with ⟨h | h, h1, h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  have hentry : ∀ r s, T.intersection (v r) (v s) =
      if r = s then -2 * DynkinShape.D.weightFactor r * w
      else if DynkinShape.D.Edge r s then
        max (DynkinShape.D.weightFactor r) (DynkinShape.D.weightFactor s) * w else 0 := by
    intro r s
    simp only [DynkinShape.weightFactor, max_self, mul_one, one_mul]
    rcases lt_trichotomy r s with h | rfl | h
    · rw [ite_eq_right (ne_of_lt h)]
      exact hupper r s h
    · rw [ite_eq_left rfl, (hminus r).2, hw r]
    · rw [ite_eq_right (ne_of_gt h), T.intersection_symm, hupper s r h]
      congr 1
      apply propext
      simp only [DynkinShape.Edge]
      tauto
  have ha : DynkinShape.D.Allows (t + 1) := by simp [DynkinShape.Allows]; omega
  exact ⟨.D, w, ha, hpos, hweight, hentry,
    multiplicity_row_bound_of_matrix T v hv .D w hpos ha hweight hentry⟩

private lemma dynkin_of_e6_ordering (T : NumericalType) (hn : 6 < T.componentCount)
    (v : Fin 6 → Fin T.componentCount) (hv : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hchain : ∀ r s : Fin 6, s.val = r.val + 1 → s.val < 5 →
      T.intersection (v r) (v s) ≠ 0)
    (hbranch : T.intersection (v 2) (v 5) ≠ 0) :
    ∃ d w, IsDynkinConfiguration T v d w := by
  classical
  have he : ∀ r s, IsE6ForwardEdge r s →
      T.intersection (v r) (v s) ≠ 0 := by
    intro r s h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals first | exact hbranch | exact hchain _ _ rfl (by decide)
  have hw := weight_eq_of_e6 T hn v hv hminus he
  have hm := intersection_eq_e6Matrix T hn v hv hminus he
  let w := T.weight (v 0)
  have hweight : ∀ r, T.weight (v r) = DynkinShape.E6.weightFactor r * w := by
    simpa [DynkinShape.weightFactor, w] using hw
  have hentry : ∀ r s, T.intersection (v r) (v s) =
      if r = s then -2 * DynkinShape.E6.weightFactor r * w
      else if DynkinShape.E6.Edge r s then
        max (DynkinShape.E6.weightFactor r) (DynkinShape.E6.weightFactor s) * w else 0 := by
    intro r s
    have h := congrFun (congrFun hm r) s
    fin_cases r <;> fin_cases s <;>
      simpa [e6IntersectionMatrix, IsE6Adjacent,
        IsE6ForwardEdge, DynkinShape.weightFactor, DynkinShape.Edge, w] using h
  have ha : DynkinShape.E6.Allows 6 := rfl
  exact ⟨.E6, w, ha, T.weight_pos _, hweight, hentry,
    multiplicity_row_bound_of_matrix T v hv .E6 w (T.weight_pos _) ha hweight hentry⟩

private lemma dynkin_of_e7_ordering (T : NumericalType) (hn : 7 < T.componentCount)
    (v : Fin 7 → Fin T.componentCount) (hv : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hchain : ∀ r s : Fin 7, s.val = r.val + 1 → s.val < 6 →
      T.intersection (v r) (v s) ≠ 0)
    (hbranch : T.intersection (v 3) (v 6) ≠ 0) :
    ∃ d w, IsDynkinConfiguration T v d w := by
  classical
  let e : Fin 7 ↪ Fin T.componentCount := ⟨v, hv⟩
  have he : T.intersection (e 0) (e 1) ≠ 0 ∧ T.intersection (e 1) (e 2) ≠ 0 ∧
      T.intersection (e 2) (e 3) ≠ 0 ∧ T.intersection (e 3) (e 4) ≠ 0 ∧
      T.intersection (e 4) (e 5) ≠ 0 ∧ T.intersection (e 3) (e 6) ≠ 0 :=
    ⟨hchain _ _ rfl (by decide), hchain _ _ rfl (by decide),
      hchain _ _ rfl (by decide), hchain _ _ rfl (by decide),
      hchain _ _ rfl (by decide), hbranch⟩
  have hw := e7_subgraph_weight_eq T hn e hminus he
  have hm := e7_subgraph_classification T hn e hminus he
  let w := T.weight (v 0)
  have hweight : ∀ r, T.weight (v r) = DynkinShape.E7.weightFactor r * w := by
    intro r
    have h := congrFun hw r
    fin_cases r <;>
      first
        | (simp [DynkinShape.weightFactor, w]; done)
        | simpa [DynkinShape.weightFactor, w, e] using h
  have hentry : ∀ r s, T.intersection (v r) (v s) =
      if r = s then -2 * DynkinShape.E7.weightFactor r * w
      else if DynkinShape.E7.Edge r s then
        max (DynkinShape.E7.weightFactor r) (DynkinShape.E7.weightFactor s) * w else 0 := by
    intro r s
    have h := congrFun (congrFun hm r) s
    fin_cases r <;> fin_cases s <;>
      simpa [DynkinShape.weightFactor, DynkinShape.Edge, w, e] using h
  have ha : DynkinShape.E7.Allows 7 := rfl
  exact ⟨.E7, w, ha, T.weight_pos _, hweight, hentry,
    multiplicity_row_bound_of_matrix T v hv .E7 w (T.weight_pos _) ha hweight hentry⟩

private lemma dynkin_of_e8_ordering (T : NumericalType) (hn : 8 < T.componentCount)
    (v : Fin 8 → Fin T.componentCount) (hv : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hchain : ∀ r s : Fin 8, s.val = r.val + 1 → s.val < 7 →
      T.intersection (v r) (v s) ≠ 0)
    (hbranch : T.intersection (v 4) (v 7) ≠ 0) :
    ∃ d w, IsDynkinConfiguration T v d w := by
  classical
  obtain ⟨w, hw, hm⟩ := e8_submatrix_of_minus_two_indices T hn v hv hminus
    (hchain _ _ rfl (by decide)) (hchain _ _ rfl (by decide))
    (hchain _ _ rfl (by decide)) (hchain _ _ rfl (by decide))
    (hchain _ _ rfl (by decide)) (hchain _ _ rfl (by decide)) hbranch
  have hpos : 0 < w := (hw 0) ▸ T.weight_pos (v 0)
  have hweight : ∀ r, T.weight (v r) = DynkinShape.E8.weightFactor r * w := by
    simpa [DynkinShape.weightFactor] using hw
  have hentry : ∀ r s, T.intersection (v r) (v s) =
      if r = s then -2 * DynkinShape.E8.weightFactor r * w
      else if DynkinShape.E8.Edge r s then
        max (DynkinShape.E8.weightFactor r) (DynkinShape.E8.weightFactor s) * w else 0 := by
    intro r s
    have h := congrFun (congrFun hm r) s
    fin_cases r <;> fin_cases s <;>
      simpa [e8IntersectionMatrix, DynkinShape.weightFactor, DynkinShape.Edge] using h
  have ha : DynkinShape.E8.Allows 8 := rfl
  exact ⟨.E8, w, ha, hpos, hweight, hentry,
    multiplicity_row_bound_of_matrix T v hv .E8 w hpos ha hweight hentry⟩

private lemma submatrix_quadratic_neg {t : ℕ} (T : NumericalType)
    (v : Fin t → Fin T.componentCount) (hv : Function.Injective v)
    (ht : t < T.componentCount) (c : Fin t → ℚ) (hc : c ≠ 0) :
    (∑ r, ∑ s, c r * (T.intersection (v r) (v s) : ℚ) * c s) < 0 := by
  classical
  let x : Fin T.componentCount → ℚ := ∑ r, Pi.single (v r) (c r)
  let I : Finset (Fin T.componentCount) := Finset.univ.image v
  have hx (r : Fin t) : x (v r) = c r := by
    simp [x, Pi.single_apply, hv.eq_iff]
  have hnonzero : x ≠ 0 := by
    intro h
    apply hc
    funext r
    simpa [h] using (hx r).symm
  have hproper : I.card < T.componentCount := by
    simpa [I, Finset.card_image_of_injective _ hv] using ht
  have hsupport : ∀ i, i ∉ I → x i = 0 := by
    intro i hi
    simp only [x, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro r _
    apply Pi.single_eq_of_ne
    intro h
    exact hi (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, h.symm⟩)
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun i j => T.intersection i j
  have hmul (r : Fin t) : (A *ᵥ x) (v r) = ∑ s, A (v r) (v s) * c s := by
    change (A.mulVec (∑ s, Pi.single (v s) (c s))) (v r) = _
    rw [Matrix.mulVec_sum]
    simp [Finset.sum_apply, Matrix.mulVec_single, mul_comm]
  have h := quadraticForm_neg_of_supported_proper_finset T I hproper x hsupport hnonzero
  change (∑ r, Pi.single (v r) (c r)) ⬝ᵥ (A *ᵥ x) < 0 at h
  rw [sum_dotProduct] at h
  simp only [single_dotProduct, hmul, Finset.mul_sum] at h
  simpa only [A, mul_assoc] using h

private lemma no_affine_e8_ordering (T : NumericalType) (hn : 9 < T.componentCount)
    (v : Fin 9 → Fin T.componentCount) (hv : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hchain : ∀ r s : Fin 9, s.val = r.val + 1 → s.val < 8 →
      T.intersection (v r) (v s) ≠ 0)
    (hbranch : T.intersection (v 5) (v 8) ≠ 0) : False := by
  classical
  let f : Fin 8 → Fin 9 := ![0,1,2,3,4,5,6,8]
  let g : Fin 8 → Fin 9 := ![1,2,3,4,5,6,7,8]
  have hf : Function.Injective f := by decide
  have hg : Function.Injective g := by decide
  have hfc : ∀ j : Fin 6, T.intersection (v (f ⟨j, by omega⟩))
      (v (f ⟨j + 1, by omega⟩)) ≠ 0 := by
    intro j
    fin_cases j <;> apply hchain <;> norm_num [f]
  obtain ⟨w, hw, _, _, _⟩ := eq_fork_of_isMinusTwoIndex T 7 (by decide)
    (by omega) (v ∘ f) (hv.comp hf) (fun r => hminus _) hfc
    (by simpa [f, Function.comp_def] using hbranch)
  have hgc : ∀ r s : Fin 8, s.val = r.val + 1 → s.val < 7 →
      T.intersection (v (g r)) (v (g s)) ≠ 0 := by
    intro r s hrs hs
    fin_cases r <;> fin_cases s <;> simp_all only [Fin.reduceFinMk,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff]
    all_goals exact hchain _ _ rfl (by decide)
  obtain ⟨w', hw', _⟩ := e8_submatrix_of_minus_two_indices T (by omega)
    (v ∘ g) (hv.comp hg) (fun r => hminus _)
    (hgc _ _ rfl (by decide)) (hgc _ _ rfl (by decide))
    (hgc _ _ rfl (by decide)) (hgc _ _ rfl (by decide))
    (hgc _ _ rfl (by decide)) (hgc _ _ rfl (by decide)) hbranch
  have hww : w' = w := (hw' 0).symm.trans (hw 1)
  have hweights : ∀ r, T.weight (v r) = w := by
    intro r
    fin_cases r
    · exact hw 0
    · exact hw 1
    · exact hw 2
    · exact hw 3
    · exact hw 4
    · exact hw 5
    · exact hw 6
    · exact (hw' 6).trans hww
    · exact hw 7
  have hpos : 0 < w := (hweights 0) ▸ T.weight_pos (v 0)
  let E : Fin 9 → Fin 9 → Prop := fun r s =>
    ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < 8 ∧ s.val < 8) ∨
      (r = 5 ∧ s = 8) ∨ (r = 8 ∧ s = 5)
  have hedge (r s : Fin 9) (h : E r s) : T.intersection (v r) (v s) ≠ 0 := by
    rcases h with ⟨h | h, hr, hs⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hchain _ _ h.symm hs
    · rw [T.intersection_symm]; exact hchain _ _ h.symm hr
    · exact hbranch
    · rwa [T.intersection_symm]
  let B : Matrix (Fin 9) (Fin 9) ℚ := fun r s =>
    if r = s then -2 * (w : ℚ) else if E r s then w else 0
  have hle (r s : Fin 9) : B r s ≤ (T.intersection (v r) (v s) : ℚ) := by
    dsimp [B]
    split_ifs with hrs he
    · subst s
      rw [(hminus r).2, hweights r]
      push_cast
      exact le_refl _
    · have hnonneg := T.intersection_nonneg _ _ (hv.ne hrs)
      have heq := intersection_eq_max_weight_of_intersects T (by omega) _ _
        (hminus r) (hminus s) (lt_of_le_of_ne hnonneg (Ne.symm (hedge r s he)))
      rw [hweights r, hweights s, max_self] at heq
      rw [heq]
    · exact_mod_cast T.intersection_nonneg _ _ (hv.ne hrs)
  let c : Fin 9 → ℚ := ![1,2,3,4,5,6,4,2,3]
  have hc : c ≠ 0 := by intro h; have := congrFun h 0; norm_num [c] at this
  have hcpos : ∀ r, 0 ≤ c r := by intro r; fin_cases r <;> norm_num [c]
  have hneg := submatrix_quadratic_neg T v hv hn c hc
  have hsum : (∑ r, ∑ s, c r * B r s * c s) ≤
      ∑ r, ∑ s, c r * (T.intersection (v r) (v s) : ℚ) * c s :=
    Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hle r s) (hcpos r)) (hcpos s)
  have hz : (∑ r, ∑ s, c r * B r s * c s) = 0 := by
    simp [Fin.sum_univ_succ, c, B, E]
    ring
  linarith

private def segmentWithLeaf {t n : ℕ} (b : ℕ) (h : b + n ≤ t) :
    Fin (n + 1) ↪ Fin (t + 1) where
  toFun r := ⟨if r.val < n then b + r.val else t, by split_ifs <;> omega⟩
  inj' := by
    intro r s hrs
    apply Fin.ext
    have he := congrArg Fin.val hrs
    dsimp at he
    split_ifs at he <;> omega

private lemma segmentWithLeaf_val {t n : ℕ} (b : ℕ) (h : b + n ≤ t)
    (r : Fin (n + 1)) (hr : r.val < n) :
    (segmentWithLeaf b h r).val = b + r.val := by
  change (if r.val < n then b + r.val else t) = _
  rw [ite_eq_left hr]

private lemma segmentWithLeaf_last {t n : ℕ} (b : ℕ) (h : b + n ≤ t) :
    segmentWithLeaf b h (Fin.last n) = Fin.last t := by
  apply Fin.ext
  change (if (Fin.last n).val < n then b + (Fin.last n).val else t) = _
  simp

private lemma classify_oriented_chain_with_leaf {t : ℕ} (T : NumericalType)
    (ht : 5 ≤ t) (hn : t + 1 < T.componentCount)
    (v : Fin (t + 1) → Fin T.componentCount) (hv : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hchain : ∀ r s : Fin (t + 1), s.val = r.val + 1 → s.val < t →
      T.intersection (v r) (v s) ≠ 0)
    (k : Fin t) (hk : t - 1 - k.val ≤ k.val)
    (hbranch : T.intersection (v k.castSucc) (v (Fin.last t)) ≠ 0) :
    ∃ u : Fin (t + 1) → Fin T.componentCount,
      Function.Injective u ∧ Set.range u = Set.range v ∧
      ∃ d w, IsDynkinConfiguration T u d w := by
  classical
  by_cases hend : k.val = t - 1
  · apply dynkin_of_ordered_chain T (by omega) hn v hv hminus
    intro r s hrs
    by_cases hs : s.val < t
    · exact hchain r s hrs hs
    · have hs' : s = Fin.last t := Fin.ext (by simp; omega)
      have hr : r = k.castSucc := Fin.ext (by simp; omega)
      simpa [hr, hs'] using hbranch
  by_cases hfork : k.val = t - 2
  · refine ⟨v, hv, rfl, ?_⟩
    apply dynkin_of_fork T (by omega) hn v hv hminus hchain
    have heq : k.castSucc = (⟨t - 2, by omega⟩ : Fin (t + 1)) :=
      Fin.ext hfork
    have hlast : Fin.last t = (⟨t, by omega⟩ : Fin (t + 1)) := Fin.ext (by simp)
    simpa only [heq, hlast] using hbranch
  have segment (n p : ℕ) (hpn : p < n) (hp : p ≤ k.val) (hroom : k.val - p + n ≤ t) :
      ∃ u : Fin (n + 1) → Fin T.componentCount, Function.Injective u ∧
        (∀ r, IsMinusTwoIndex T (u r)) ∧
        (∀ r s : Fin (n + 1), s.val = r.val + 1 → s.val < n →
          T.intersection (u r) (u s) ≠ 0) ∧
        T.intersection (u ⟨p, by omega⟩) (u (Fin.last n)) ≠ 0 := by
    let f : Fin (n + 1) ↪ Fin (t + 1) := segmentWithLeaf (k.val - p) hroom
    have hfv (r : Fin (n + 1)) (hr : r.val < n) : (f r).val = k.val - p + r.val :=
      segmentWithLeaf_val _ _ r hr
    have hfl : f (Fin.last n) = Fin.last t := segmentWithLeaf_last _ _
    have hfp : f ⟨p, by omega⟩ = k.castSucc := Fin.ext (by rw [hfv _ hpn]; simp; omega)
    refine ⟨v ∘ f, hv.comp f.injective, fun r => hminus _, ?_, ?_⟩
    · intro r s hrs hs
      apply hchain
      · rw [hfv r (by omega), hfv s hs]; omega
      · rw [hfv s hs]; omega
    · simpa only [Function.comp_apply, hfp, hfl] using hbranch
  have hright : t - 1 - k.val = 2 := by
    by_contra hh
    obtain ⟨u, hu, hum, huc, hub⟩ := segment 7 3 (by omega) (by omega) (by omega)
    apply not_exists_branched_chain_of_eight_minus_two_indices T (by omega)
    exact ⟨u, hu, hum, huc _ _ rfl (by decide), huc _ _ rfl (by decide),
      huc _ _ rfl (by decide), huc _ _ rfl (by decide), huc _ _ rfl (by decide),
      huc _ _ rfl (by decide), by rwa [T.intersection_symm]⟩
  have hk4 : k.val ≤ 4 := by
    by_contra hh
    obtain ⟨u, hu, hum, huc, hub⟩ := segment 8 5 (by omega) (by omega) (by omega)
    exact no_affine_e8_ordering T (by omega) u hu hum (fun r s h hs => huc r s h hs) hub
  have hts : t = 5 ∨ t = 6 ∨ t = 7 := by omega
  refine ⟨v, hv, rfl, ?_⟩
  rcases hts with rfl | rfl | rfl
  · have heq : k.castSucc = (2 : Fin 6) := Fin.ext (by simp; omega)
    exact dynkin_of_e6_ordering T hn v hv hminus hchain (by simpa [heq] using hbranch)
  · have heq : k.castSucc = (3 : Fin 7) := Fin.ext (by simp; omega)
    exact dynkin_of_e7_ordering T hn v hv hminus hchain (by simpa [heq] using hbranch)
  · have heq : k.castSucc = (4 : Fin 8) := Fin.ext (by simp; omega)
    exact dynkin_of_e8_ordering T hn v hv hminus hchain (by simpa [heq] using hbranch)

private lemma classify_chain_with_leaf {t : ℕ} (T : NumericalType)
    (ht : 5 ≤ t) (hn : t + 1 < T.componentCount)
    (u : Fin t → Fin T.componentCount) (hu : Function.Injective u)
    (a : Fin T.componentCount) (ha : a ∉ Set.range u)
    (hminus : ∀ r, IsMinusTwoIndex T (u r)) (haMinus : IsMinusTwoIndex T a)
    (hchain : ∀ r s, s.val = r.val + 1 → T.intersection (u r) (u s) ≠ 0)
    (k : Fin t) (hbranch : T.intersection (u k) a ≠ 0) :
    ∃ v : Fin (t + 1) → Fin T.componentCount,
      Function.Injective v ∧ Set.range v = insert a (Set.range u) ∧
      ∃ d w, IsDynkinConfiguration T v d w := by
  classical
  have oriented (u : Fin t → Fin T.componentCount) (hu : Function.Injective u)
      (ha : a ∉ Set.range u) (hminus : ∀ r, IsMinusTwoIndex T (u r))
      (hchain : ∀ r s, s.val = r.val + 1 → T.intersection (u r) (u s) ≠ 0)
      (k : Fin t) (hk : t - 1 - k.val ≤ k.val)
      (hbranch : T.intersection (u k) a ≠ 0) :
      ∃ v : Fin (t + 1) → Fin T.componentCount,
        Function.Injective v ∧ Set.range v = insert a (Set.range u) ∧
        ∃ d w, IsDynkinConfiguration T v d w := by
    let v : Fin (t + 1) → Fin T.componentCount := Fin.lastCases a u
    have hvlast : v (Fin.last t) = a := by simp [v]
    have hvcast (r : Fin t) : v r.castSucc = u r := by simp [v]
    have hv : Function.Injective v := by
      intro r s h
      induction r using Fin.lastCases <;> induction s using Fin.lastCases
      · rfl
      · rename_i s
        exact (ha ⟨s, by simpa [v] using h.symm⟩).elim
      · rename_i r
        exact (ha ⟨r, by simpa [v] using h⟩).elim
      · rename_i r s
        exact congrArg Fin.castSucc (hu (by simpa [v] using h))
    have hrange : Set.range v = insert a (Set.range u) := by
      ext y
      constructor
      · rintro ⟨r, rfl⟩
        induction r using Fin.lastCases
        · simp [v]
        · rename_i r
          exact Or.inr ⟨r, (hvcast r).symm⟩
      · rintro (rfl | ⟨r,rfl⟩)
        · exact ⟨Fin.last t, hvlast⟩
        · exact ⟨r.castSucc, hvcast r⟩
    have hminusV : ∀ r, IsMinusTwoIndex T (v r) := by
      intro r
      induction r using Fin.lastCases
      · simpa [v] using haMinus
      · rename_i r
        simpa [v] using hminus r
    have hmain : ∀ r s : Fin (t + 1), s.val = r.val + 1 → s.val < t →
        T.intersection (v r) (v s) ≠ 0 := by
      intro r s hrs hs
      have hr : r.val < t := by omega
      have her : (⟨r.val, hr⟩ : Fin t).castSucc = r := rfl
      have hes : (⟨s.val, hs⟩ : Fin t).castSucc = s := rfl
      rw [← her, ← hes, hvcast, hvcast]
      exact hchain _ _ hrs
    obtain ⟨w, hw, hwrange, hcfg⟩ := classify_oriented_chain_with_leaf T ht hn v hv
      hminusV hmain k hk (by simpa [v] using hbranch)
    exact ⟨w, hw, hwrange.trans hrange, hcfg⟩
  by_cases hk : t - 1 - k.val ≤ k.val
  · exact oriented u hu ha hminus hchain k hk hbranch
  · let u' : Fin t → Fin T.componentCount := fun r => u r.rev
    have hu' : Function.Injective u' := hu.comp Fin.rev_injective
    have hrange : Set.range u' = Set.range u := by
      ext y
      constructor
      · rintro ⟨r,rfl⟩; exact ⟨r.rev,rfl⟩
      · rintro ⟨r,rfl⟩; exact ⟨r.rev, by simp [u']⟩
    have hchain' : ∀ r s : Fin t, s.val = r.val + 1 →
        T.intersection (u' r) (u' s) ≠ 0 := by
      intro r s hrs
      rw [T.intersection_symm]
      apply hchain
      simp only [Fin.val_rev]
      omega
    obtain ⟨v, hv, hvrange, hcfg⟩ := oriented u' hu' (hrange ▸ ha)
      (fun r => hminus _) hchain' k.rev (by simp only [Fin.val_rev]; omega)
      (by simpa [u'] using hbranch)
    exact ⟨v, hv, hvrange.trans (by rw [hrange]), hcfg⟩

private lemma degree_ge_three_of_neighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj x a) (hb : G.Adj x b) (hc : G.Adj x c) :
    3 ≤ G.degree x := by
  classical
  let f : Fin 3 → G.neighborSet x := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have he := congrArg Subtype.val hij
    clear hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, G.card_neighborSet_eq_degree] using h

/-- Deleting a leaf from a connected set of components leaves it connected. -/
public lemma connected_erase_leaf (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (a x : Fin T.componentCount)
    (ha : a ∈ I) (_hx : x ∈ I) (hax : a ≠ x)
    (hleaf : ∀ y ∈ I, y ≠ a → T.intersection a y ≠ 0 → y = x)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0)) :
    ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I.erase a ∧
        (∀ i ∈ J, ∀ j ∈ I.erase a, j ∉ J → T.intersection i j = 0) := by
  classical
  rintro ⟨J, hJ, hsub, hz⟩
  have hJI : J ⊆ I := hsub.subset.trans (Finset.erase_subset _ _)
  have haJ : a ∉ J := fun h => (Finset.mem_erase.mp (hsub.subset h)).1 rfl
  by_cases hxJ : x ∈ J
  · apply hconnected
    refine ⟨insert a J, hJ.mono (Finset.subset_insert _ _), ?_, ?_⟩
    · refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.insert_subset ha hJI, ?_⟩
      intro heq
      apply hsub.ne
      apply Finset.Subset.antisymm hsub.subset
      intro y hy
      have := heq.symm ▸ (Finset.mem_of_mem_erase hy)
      rcases Finset.mem_insert.mp this with h | h
      · exact ((Finset.mem_erase.mp hy).1 h).elim
      · exact h
    · intro i hi j hj hjnot
      have hja : j ≠ a := fun h => hjnot (by simp [h])
      have hjJ : j ∉ J := fun h => hjnot (Finset.mem_insert_of_mem h)
      rcases Finset.mem_insert.mp hi with rfl | hi
      · by_contra h
        exact hjJ (hleaf j hj hja h ▸ hxJ)
      · exact hz i hi j (Finset.mem_erase.mpr ⟨hja, hj⟩) hjJ
  · apply hconnected
    refine ⟨J, hJ, Finset.ssubset_iff_subset_ne.mpr ⟨hJI, ?_⟩, ?_⟩
    · intro heq
      exact haJ (heq.symm ▸ ha)
    · intro i hi j hj hjnot
      by_cases hja : j = a
      · subst j
        by_contra h
        have hia : i ≠ a := fun h => haJ (h ▸ hi)
        have hai : T.intersection a i ≠ 0 := by rwa [T.intersection_symm]
        exact hxJ (hleaf i (hJI hi) hia hai ▸ hi)
      · exact hz i hi j (Finset.mem_erase.mpr ⟨hja, hj⟩) hjnot

private lemma exists_chain_after_erasing_leaf (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hcard : 6 ≤ I.card)
    (hproper : I.card < T.componentCount)
    (hminus : ∀ i ∈ I, IsMinusTwoIndex T i)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0))
    (x a b c : {i // i ∈ I})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxa : (minusTwoGraph T I).Adj x a)
    (hxb : (minusTwoGraph T I).Adj x b)
    (hxc : (minusTwoGraph T I).Adj x c)
    [Fintype ((minusTwoGraph T I).neighborSet a)]
    (hleaf : (minusTwoGraph T I).degree a = 1) :
    ∃ (t : ℕ) (u : Fin t → Fin T.componentCount) (k : Fin t),
      t + 1 = I.card ∧ Function.Injective u ∧
      Set.range u = (I.erase a.val : Set (Fin T.componentCount)) ∧
      (∀ r s, s.val = r.val + 1 → T.intersection (u r) (u s) ≠ 0) ∧
      T.intersection (u k) a.val ≠ 0 := by
  classical
  let G := minusTwoGraph T I
  let J := I.erase a.val
  have hJcard : J.card + 1 = I.card := Finset.card_erase_add_one a.property
  have hJproper : J.card < T.componentCount := by omega
  have hJminus : ∀ i ∈ J, IsMinusTwoIndex T i :=
    fun i hi => hminus i (Finset.mem_of_mem_erase hi)
  have hTree := minusTwoGraph_isTree T I (by omega) hproper hminus hconnected
  have hxdeg : G.degree x = 3 := le_antisymm
    (minusTwoGraph_degree_le_three T I hproper hminus x)
    (degree_ge_three_of_neighbors G x a b c hab hac hbc hxa hxb hxc)
  have hleaf' : ∀ y ∈ I, y ≠ a.val → T.intersection a.val y ≠ 0 → y = x.val := by
    have hleaf' : G.degree a = 1 := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] using hleaf
    obtain ⟨z, hz, huniq⟩ := G.degree_eq_one_iff_existsUnique_adj.mp hleaf'
    intro y hy hya hay
    have h1 := huniq ⟨y, hy⟩ ⟨hya.symm, hay⟩
    have h2 := huniq x hxa.symm
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hconnJ := connected_erase_leaf T I a.val x.val a.property x.property
    hxa.1.symm hleaf' hconnected
  have hdegJ : ∀ y : {i // i ∈ J}, ((minusTwoGraph T J).neighborSet y).ncard ≤ 2 := by
    by_contra h
    obtain ⟨y, p, q, r, hpq, hpr, hqr, hyp, hyq, hyr⟩ :=
      exists_trivalent_vertex_of_not_degree_le_two T J hJproper hJminus h
    let f : {i // i ∈ J} → {i // i ∈ I} :=
      fun z => ⟨z.val, Finset.mem_of_mem_erase z.property⟩
    have hf : Function.Injective f := by
      intro z w h
      exact Subtype.ext (congrArg (fun z : {i // i ∈ I} => z.val) h)
    have hydeg : G.degree (f y) = 3 := le_antisymm
      (minusTwoGraph_degree_le_three T I hproper hminus (f y))
      (degree_ge_three_of_neighbors G (f y) (f p) (f q) (f r)
        (hf.ne hpq) (hf.ne hpr) (hf.ne hqr) hyp hyq hyr)
    have hyx : f y = x := by
      by_contra hne
      exact no_two_trivalent_vertices T I hproper hminus (f y) x hne
        hydeg hxdeg hTree
    have hfa (z : {i // i ∈ J}) : f z ≠ a := fun h =>
      (Finset.mem_erase.mp z.property).1 (congrArg Subtype.val h)
    have hya : G.Adj (f y) a := hyx.symm ▸ hxa
    exact no_four_neighbors_of_degree_le_three G
      (fun z => minusTwoGraph_degree_le_three T I hproper hminus z)
      (f y) (f p) (f q) (f r) a (hf.ne hpq) (hf.ne hpr) (hfa p)
      (hf.ne hqr) (hfa q) (hfa r) hyp hyq hyr hya
  obtain ⟨u, hu, hrange, hadj⟩ := exists_spanning_chain_of_degree_le_two
    T J (by omega) hconnJ hdegJ
  have hxJ : x.val ∈ J := Finset.mem_erase.mpr ⟨hxa.1, x.property⟩
  have hxrange : x.val ∈ Set.range u := by rw [hrange]; exact hxJ
  obtain ⟨k, hk⟩ := hxrange
  exact ⟨J.card, u, k, hJcard, hu, hrange, hadj, hk.symm ▸ hxa.2⟩

/-- A connected proper subset of minus-two indices has, up to reordering, one
of the listed A, B, C, D, E, F, or G configurations. -/
@[stacks 0C8Q]
public theorem classify_connected_proper_minusTwo_subgraph (T : NumericalType)
    (I : Finset (Fin T.componentCount))
    (hcard : 2 ≤ I.card) (hproper : I.card < T.componentCount)
    (hminus : ∀ i ∈ I, IsMinusTwoIndex T i)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0)) :
    ∃ v : Fin I.card → Fin T.componentCount,
      Function.Injective v ∧ Set.range v = (I : Set (Fin T.componentCount)) ∧
        ∃ (d : DynkinShape) (w : ℤ), IsDynkinConfiguration T v d w := by
  classical
  by_cases htwo : I.card = 2
  · rw [htwo]
    exact classify_two_vertex_subset T I hproper hminus hconnected htwo
  · by_cases hthree : I.card = 3
    · rw [hthree]
      exact classify_three_vertex_subset T I hproper hminus hconnected hthree
    · have hlarge : 4 ≤ I.card := by omega
      by_cases hdegree : ∀ x : {i // i ∈ I},
          ((minusTwoGraph T I).neighborSet x).ncard ≤ 2
      · obtain ⟨v, hv, hvrange, hadj⟩ :=
          exists_spanning_chain_of_degree_le_two T I hcard hconnected hdegree
        have hminusV : ∀ r, IsMinusTwoIndex T (v r) := by
          intro r
          apply hminus
          have hmem : v r ∈ (I : Set (Fin T.componentCount)) := by
            rw [← hvrange]
            exact ⟨r, rfl⟩
          simpa using hmem
        obtain ⟨u, hu, hurange, d, w, hcfg⟩ :=
          dynkin_of_ordered_chain T (by omega) hproper v hv hminusV hadj
        exact ⟨u, hu, hurange.trans hvrange, d, w, hcfg⟩
      · obtain ⟨x, a, b, c, hab, hac, hbc, hxa, hxb, hxc⟩ :=
          exists_trivalent_vertex_of_not_degree_le_two T I hproper hminus hdegree
        by_cases hfour : I.card = 4
        · rw [hfour]
          obtain ⟨hv, hvrange, hminusV⟩ := subtype_family_facts T I hminus hfour
            ![a, x, b, c] (by intro r s hrs; fin_cases r <;> fin_cases s <;> simp_all [hxa.ne,
              hxb.ne, hxc.ne, hxa.ne.symm, hxb.ne.symm, hxc.ne.symm])
          obtain ⟨d, w, hcfg⟩ := dynkin_of_d4_ordering T (by omega) _ hv hminusV
            hxa.2 hxb.2 hxc.2
          exact ⟨_, hv, hvrange, d, w, hcfg⟩
        · by_cases hfive : I.card = 5
          · rw [hfive]
            let G := minusTwoGraph T I
            let S : Finset {i // i ∈ I} := {x, a, b, c}
            have hScard : S.card = 4 := by
              simp [S, hxa.ne, hxb.ne, hxc.ne, hab, hac, hbc]
            have hSproper : S ≠ Finset.univ := by
              intro he
              have hc := congrArg Finset.card he
              rw [hScard, Finset.card_univ, Fintype.card_coe, hfive] at hc
              omega
            obtain ⟨s, hsS, z, hzS, hsz⟩ := exists_adj_across_of_connected G
              (minusTwoGraph_connected T I (by omega) hconnected) S ⟨x, by simp [S]⟩ hSproper
            simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hsS hzS
            obtain ⟨hzsx, hzsa, hzsb, hzsc⟩ := hzS
            rcases hsS with hsx | hsa | hsb | hsc
            · subst s
              exact (no_four_neighbors_of_degree_le_three G
                (fun y => minusTwoGraph_degree_le_three T I hproper hminus y)
                x a b c z hab hac (Ne.symm hzsa) hbc (Ne.symm hzsb) (Ne.symm hzsc)
                hxa hxb hxc hsz).elim
            · subst s
              exact dynkin_of_d5_subtypes T I hfive hproper hminus z a x b c
                hzsx hzsb hzsc hab hac hbc hsz.symm hxa.symm hxb hxc
            · subst s
              exact dynkin_of_d5_subtypes T I hfive hproper hminus z b x a c
                hzsx hzsa hzsc hab.symm hbc hac hsz.symm hxb.symm hxa hxc
            · subst s
              exact dynkin_of_d5_subtypes T I hfive hproper hminus z c x a b
                hzsx hzsa hzsb hac.symm hbc.symm hab hsz.symm hxc.symm hxa hxb
          · have hlarge : 6 ≤ I.card := by omega
            have hTree := minusTwoGraph_isTree T I (by omega) hproper hminus hconnected
            have finish (a b c : {i // i ∈ I})
                (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
                (hxa : (minusTwoGraph T I).Adj x a)
                (hxb : (minusTwoGraph T I).Adj x b)
                (hxc : (minusTwoGraph T I).Adj x c)
                (hleaf : (minusTwoGraph T I).degree a = 1) :
                ∃ v : Fin I.card → Fin T.componentCount,
                  Function.Injective v ∧ Set.range v = (I : Set (Fin T.componentCount)) ∧
                  ∃ d w, IsDynkinConfiguration T v d w := by
              obtain ⟨t, u, k, hsize, hu, hurange, hchain, hbranch⟩ :=
                exists_chain_after_erasing_leaf T I hlarge hproper hminus hconnected
                  x a b c hab hac hbc hxa hxb hxc hleaf
              have ha : a.val ∉ Set.range u := by rw [hurange]; simp
              have huMinus : ∀ r, IsMinusTwoIndex T (u r) := by
                intro r
                have hm : u r ∈ (I.erase a.val : Set (Fin T.componentCount)) := by
                  rw [← hurange]; exact ⟨r, rfl⟩
                exact hminus _ (Finset.mem_of_mem_erase hm)
              obtain ⟨v, hv, hvrange, hcfg⟩ := classify_chain_with_leaf T (by omega)
                (by omega) u hu a.val ha huMinus (hminus _ a.property) hchain k hbranch
              have hrange : Set.range v = (I : Set (Fin T.componentCount)) := by
                rw [hvrange, hurange, ← Finset.coe_insert, Finset.insert_erase a.property]
              rw [← hsize]
              exact ⟨v, hv, hrange, hcfg⟩
            rcases one_of_three_neighbors_is_leaf T I hproper hminus x a b c
                hab hac hbc hxa hxb hxc hTree with ha | hb | hc
            · exact finish a b c hab hac hbc hxa hxb hxc ha
            · exact finish b a c hab.symm hbc hac hxb hxa hxc hb
            · exact finish c a b hac.symm hbc.symm hab hxc hxa hxb hc

end AlgebraicGeometry.NumericalType
