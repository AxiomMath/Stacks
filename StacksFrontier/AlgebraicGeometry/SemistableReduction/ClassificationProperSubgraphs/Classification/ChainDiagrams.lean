module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.IncidenceGraph
import all StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.IncidenceGraph
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Dynkin
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.D5
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FiveChain
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FourVertices
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.LongChain
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.ThreeVertices
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.TwoVertices

/-!
# Dynkin types of chains of minus-two indices

An ordered chain of minus-two indices is matched against the diagram families,
one case per vertex count, using the two-, three- and four-vertex
classifications: the result is a configuration of type `A`, `B`, `C`, `F₄` or
`G₂`. The orderings of type `D₄` and `D₅` are recognised with the four-vertex
and the `D₅` classifications.

## Main results

* `AlgebraicGeometry.NumericalType.dynkin_of_ordered_chain`: an ordered chain of at least four
  minus-two indices can be reordered into a Dynkin configuration.
* `AlgebraicGeometry.NumericalType.classify_two_vertex_subset`,
  `AlgebraicGeometry.NumericalType.classify_three_vertex_subset`: the classification for two and
  three vertices.
* `AlgebraicGeometry.NumericalType.dynkin_of_d4_ordering`,
  `AlgebraicGeometry.NumericalType.dynkin_of_d5_ordering`: the orderings of
  type `D₄` and `D₅`.

## Implementation notes

An ordering of the subset is an injective map from `Fin I.card` with range
exactly `I`.

## References

* [Stacks Project, Tag 0C8Q](https://stacks.math.columbia.edu/tag/0C8Q)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

open Matrix

private lemma dynkin_of_two_vertex_configuration (T : NumericalType)
    (i j : Fin T.componentCount) (h : IsTwoVertexConfiguration T i j) :
    ∃ d w, IsDynkinConfiguration T ![i, j] d w := by
  rcases h with ⟨w, hiw, hjw, hii, hij, hji, hjj, hmi, hmj⟩ |
      ⟨w, hiw, hjw, hii, hij, hji, hjj, hmi, hmj⟩ |
      ⟨w, hiw, hjw, hii, hij, hji, hjj, hmi, hmj⟩ <;>
    [refine ⟨.A, w, ?_⟩; refine ⟨.C, w, ?_⟩; refine ⟨.G2, w, ?_⟩]
  all_goals
    have hw : 0 < w := by rw [← hiw]; exact T.weight_pos i
    dsimp [IsDynkinConfiguration]
    refine ⟨by simp [DynkinShape.Allows], hw, ?_, ?_, ?_⟩
    · intro r
      fin_cases r <;> simp [DynkinShape.weightFactor, hiw, hjw]
    · intro r s
      fin_cases r <;> fin_cases s <;>
        simp [DynkinShape.Edge, DynkinShape.weightFactor, hii, hij, hji, hjj]
    · intro r
      fin_cases r <;>
        simp [DynkinShape.Edge, DynkinShape.weightFactor] <;>
        omega

private lemma exists_dynkin_ordering_of_two_vertex_configuration
    (T : NumericalType) (i j : Fin T.componentCount) (hij : i ≠ j)
    (h : IsTwoVertexConfiguration T i j) :
    ∃ v : Fin 2 → Fin T.componentCount,
      Function.Injective v ∧ Set.range v = {i, j} ∧
        ∃ d w, IsDynkinConfiguration T v d w := by
  have hinj : Function.Injective (![i, j] : Fin 2 → Fin T.componentCount) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hrange : Set.range (![i, j] : Fin 2 → Fin T.componentCount) = {i, j} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨r, hr⟩
      fin_cases r <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  obtain ⟨d, w, hcfg⟩ := dynkin_of_two_vertex_configuration T i j h
  exact ⟨![i, j], hinj, hrange, d, w, hcfg⟩

private lemma selected_intersections_le_diagonal (T : NumericalType)
    (i : Fin T.componentCount) (S : Finset (Fin T.componentCount))
    (hnot : i ∉ S) (hdiag : T.intersection i i = -2 * T.weight i) :
    (∑ j ∈ S, T.intersection i j * T.multiplicity j) ≤
      2 * T.weight i * T.multiplicity i := by
  classical
  let f : Fin T.componentCount → ℤ :=
    fun j => T.intersection i j * T.multiplicity j
  have hsubset : S ⊆ Finset.univ.erase i := by
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ]
    exact ⟨fun heq => hnot (heq ▸ hj), trivial⟩
  have hnonneg : ∀ j ∈ Finset.univ.erase i, j ∉ S → 0 ≤ f j := by
    intro j hj _
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    dsimp [f]
    exact mul_nonneg (T.intersection_nonneg i j hji.symm)
      (le_of_lt (T.multiplicity_pos j))
  have hsumle : (∑ j ∈ S, f j) ≤ ∑ j ∈ Finset.univ.erase i, f j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hbalance : (∑ j, f j) = 0 := by
    simpa [f] using T.intersection_mul_multiplicity i
  rw [← Finset.add_sum_erase (s := Finset.univ) (f := f) (a := i)
    (Finset.mem_univ i)] at hbalance
  let c : ℤ := 2 * T.weight i * T.multiplicity i
  have hbalance' : -c + (∑ j ∈ Finset.univ.erase i, f j) = 0 := by
    simpa [f, hdiag, c, mul_assoc] using hbalance
  have hsumErase' : (∑ j ∈ Finset.univ.erase i, f j) = c := by
    omega
  have hsumErase : (∑ j ∈ Finset.univ.erase i, f j) =
      2 * T.weight i * T.multiplicity i := by
    simpa [c] using hsumErase'
  simpa [f] using hsumle.trans_eq hsumErase

private lemma multiplicity_row_bound_of_weighted_edges (T : NumericalType)
    (i : Fin T.componentCount) (S : Finset (Fin T.componentCount))
    (w cᵢ : ℤ) (c : Fin T.componentCount → ℤ)
    (hw : 0 < w) (hnot : i ∉ S)
    (hweight : T.weight i = cᵢ * w)
    (hdiag : T.intersection i i = -2 * cᵢ * w)
    (hedge : ∀ j ∈ S, T.intersection i j = c j * w) :
    (∑ j ∈ S, c j * T.multiplicity j) ≤ 2 * cᵢ * T.multiplicity i := by
  have hraw := selected_intersections_le_diagonal T i S hnot (by
    rw [hdiag, hweight]
    ring)
  have hleft : (∑ j ∈ S, T.intersection i j * T.multiplicity j) =
      w * (∑ j ∈ S, c j * T.multiplicity j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hedge j hj]
    ring
  have hright : 2 * T.weight i * T.multiplicity i =
      w * (2 * cᵢ * T.multiplicity i) := by
    rw [hweight]
    ring
  rw [hleft, hright] at hraw
  exact le_of_mul_le_mul_left hraw hw

private lemma multiplicity_row_bound_of_matrix {t : ℕ} (T : NumericalType)
    (v : Fin t → Fin T.componentCount) (hinj : Function.Injective v)
    (d : DynkinShape) (w : ℤ) (hw : 0 < w)
    (hallowed : d.Allows t)
    [DecidableRel (fun r s : Fin t => d.Edge r s)]
    (hweight : ∀ r, T.weight (v r) = d.weightFactor r * w)
    (hentry : ∀ r s, T.intersection (v r) (v s) =
      if r = s then -2 * d.weightFactor r * w
      else if d.Edge r s then max (d.weightFactor r) (d.weightFactor s) * w else 0) :
    ∀ r, (∑ s : Fin t, if d.Edge r s then
      max (d.weightFactor r) (d.weightFactor s) * T.multiplicity (v s) else 0) ≤
        2 * d.weightFactor r * T.multiplicity (v r) := by
  classical
  have hnoLoop : ∀ r : Fin t, ¬ d.Edge r r := by
    intro r
    cases d <;> simp [DynkinShape.Edge, DynkinShape.Allows] at hallowed ⊢ <;> omega
  intro r
  let N : Finset (Fin t) := Finset.univ.filter fun s => d.Edge r s
  let S : Finset (Fin T.componentCount) := N.image v
  let q : {j // j ∈ S} → Fin t := fun j =>
    Classical.choose (Finset.mem_image.mp j.property)
  have hq (j : {j // j ∈ S}) : q j ∈ N ∧ v (q j) = j.val :=
    Classical.choose_spec (Finset.mem_image.mp j.property)
  let c : Fin T.componentCount → ℤ := fun j =>
    if hj : j ∈ S then max (d.weightFactor r) (d.weightFactor (q ⟨j, hj⟩)) else 0
  have hnot : v r ∉ S := by
    intro hr
    rcases Finset.mem_image.mp hr with ⟨s, hs, hvs⟩
    have hEdge : d.Edge r s := (Finset.mem_filter.mp hs).2
    have hrs : s = r := hinj (by simpa using hvs)
    subst s
    exact hnoLoop r hEdge
  have hedge : ∀ j ∈ S, T.intersection (v r) j = c j * w := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨s, hs, hvs⟩
    have hEdge : d.Edge r s := (Finset.mem_filter.mp hs).2
    have hrs : s ≠ r := by
      intro h
      subst s
      exact hnoLoop r hEdge
    have hsS : v s ∈ S := Finset.mem_image.mpr ⟨s, hs, rfl⟩
    have hqeq : q ⟨v s, hsS⟩ = s := hinj (hq ⟨v s, hsS⟩).2
    have hc : c (v s) = max (d.weightFactor r) (d.weightFactor s) := by
      simp [c, hsS, hqeq]
    rw [← hvs, hentry r s]
    simp [Ne.symm hrs, hEdge, hc]
  have hdiag : T.intersection (v r) (v r) = -2 * T.weight (v r) := by
    rw [hentry r r, ite_eq_left rfl, hweight r]
    ring
  have hdiag' : T.intersection (v r) (v r) = -2 * d.weightFactor r * w := by
    rw [hdiag, hweight r]
    ring
  have hbound := multiplicity_row_bound_of_weighted_edges T (v r) S w
    (d.weightFactor r) c hw hnot (hweight r) hdiag' hedge
  have hsum : (∑ j ∈ S, c j * T.multiplicity j) =
      ∑ s : Fin t, if d.Edge r s then
        max (d.weightFactor r) (d.weightFactor s) * T.multiplicity (v s) else 0 := by
    calc
      (∑ j ∈ S, c j * T.multiplicity j) =
          ∑ s ∈ N, c (v s) * T.multiplicity (v s) :=
        Finset.sum_image (s := N) (g := v)
          (f := fun j => c j * T.multiplicity j) (by
            intro a ha b hb hab
            exact hinj hab)
      _ = ∑ s : Fin t, if d.Edge r s then
          max (d.weightFactor r) (d.weightFactor s) * T.multiplicity (v s) else 0 := by
        simp only [N, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hEdge : d.Edge r s
        · have hsN : s ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEdge⟩
          have hsS : v s ∈ S := Finset.mem_image.mpr ⟨s, hsN, rfl⟩
          have hqeq : q ⟨v s, hsS⟩ = s := hinj (hq ⟨v s, hsS⟩).2
          simp [hEdge, c, hsS, hqeq]
        · simp [hEdge]
  rw [← hsum]
  exact hbound

/-- The Dynkin configuration conditions follow from the weights and the matrix entries. -/
private theorem isDynkinConfiguration_of_entries {t : ℕ} (T : NumericalType)
    (v : Fin t → Fin T.componentCount) (hinj : Function.Injective v)
    (d : DynkinShape) (w : ℤ) (hw : 0 < w) (hallows : d.Allows t)
    [DecidableRel (fun r s : Fin t => d.Edge r s)]
    (hweight : ∀ r, T.weight (v r) = d.weightFactor r * w)
    (hentry : ∀ r s, T.intersection (v r) (v s) =
      if r = s then -2 * d.weightFactor r * w
      else if d.Edge r s then max (d.weightFactor r) (d.weightFactor s) * w else 0) :
    IsDynkinConfiguration T v d w := by
  classical
  refine ⟨hallows, hw, hweight, ?_, ?_⟩
  · convert hentry
  · convert multiplicity_row_bound_of_matrix T v hinj d w hw hallows hweight hentry

/-- A Dynkin configuration of type `A`, `B` or `C` along a path of minus-two indices. -/
private lemma dynkin_of_path_data {t : ℕ} (T : NumericalType)
    (v : Fin t → Fin T.componentCount) (hinj : Function.Injective v)
    (d : DynkinShape) (w : ℤ) (hw : 0 < w) (hd : d = .A ∨ d = .B ∨ d = .C) (ht : 2 ≤ t)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hweight : ∀ r, T.weight (v r) = d.weightFactor r * w)
    (hforward : ∀ (r s : Fin t), s.val = r.val + 1 →
      T.intersection (v r) (v s) = max (d.weightFactor r) (d.weightFactor s) * w)
    (hzero : ∀ (r s : Fin t), r.val + 1 < s.val → T.intersection (v r) (v s) = 0) :
    IsDynkinConfiguration T v d w := by
  classical
  have hedgeShape : ∀ (r s : Fin t), d.Edge r s ↔
      (r.val + 1 = s.val ∨ s.val + 1 = r.val) := by
    rcases hd with rfl | rfl | rfl <;> intro r s <;> simp [DynkinShape.Edge]
  have hallows : d.Allows t := by
    rcases hd with rfl | rfl | rfl <;> simpa [DynkinShape.Allows]
  refine isDynkinConfiguration_of_entries T v hinj d w hw hallows hweight ?_
  intro r s
  by_cases hrs : r = s
  · subst s
    rw [ite_eq_left rfl, (hminus r).2, hweight r]
    ring
  · rw [ite_eq_right hrs]
    by_cases he : d.Edge r s
    · rw [ite_eq_left he]
      rcases (hedgeShape r s).mp he with hforward' | hbackward
      · exact hforward r s (by omega)
      · rw [T.intersection_symm]
        simpa [max_comm] using hforward s r (by omega)
    · rw [ite_eq_right he]
      by_cases hlt : r.val < s.val
      · have hgap : r.val + 1 < s.val := by
          have hne : r.val + 1 ≠ s.val := by
            intro heq
            exact he ((hedgeShape r s).mpr (Or.inl heq))
          omega
        exact hzero r s hgap
      · have hslt : s.val < r.val := by omega
        have hgap : s.val + 1 < r.val := by
          have hne : s.val + 1 ≠ r.val := by
            intro heq
            exact he ((hedgeShape r s).mpr (Or.inr heq))
          omega
        rw [T.intersection_symm]
        exact hzero s r hgap

private lemma dynkin_of_long_chain {t : ℕ} (T : NumericalType)
    (v : Fin t → Fin T.componentCount) (hinj : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r)) (ht : 5 < t)
    (hcfg : IsLongChainConfiguration T v) :
    ∃ d w, IsDynkinConfiguration T v d w := by
  rcases hcfg with ⟨w, hweights, hadj, hzero⟩ |
      ⟨w, hweights, hlast, hadj, hdouble, hzero⟩ |
      ⟨w, hweights, hlast, hadj, hzero⟩
  · have hw : 0 < w := by
      rw [← hweights ⟨0, by omega⟩]
      exact T.weight_pos _
    refine ⟨.A, w, dynkin_of_path_data T v hinj .A w hw (by simp) (by omega) hminus
      (fun r => ?_) (fun r s hrs => ?_) hzero⟩
    · simpa [DynkinShape.weightFactor] using hweights r
    · rw [hadj r s hrs]
      simp [DynkinShape.weightFactor]
  · have hw : 0 < w := by
      let r0 : Fin t := ⟨0, by omega⟩
      have hr0 : r0.val + 1 < t := by simp [r0]; omega
      rw [← hweights r0 hr0]
      exact T.weight_pos (v r0)
    refine ⟨.C, w, dynkin_of_path_data T v hinj .C w hw (by simp) (by omega) hminus
      (fun r => ?_) (fun r s hrs => ?_) hzero⟩
    · by_cases hlast' : r.val + 1 = t
      · rw [hlast r hlast']
        simp [DynkinShape.weightFactor, hlast']
      · have hbefore : r.val + 1 < t := by omega
        rw [hweights r hbefore]
        simp [DynkinShape.weightFactor, hlast']
    · have hend : s.val + 1 = t ∨ s.val + 1 < t := by omega
      have hrnot : r.val + 1 ≠ t := by omega
      rcases hend with hend | hend
      · rw [hdouble r s hrs hend]
        simp [DynkinShape.weightFactor, hrnot, hend]
      · rw [hadj r s hrs hend]
        have hsnot : s.val + 1 ≠ t := by omega
        simp [DynkinShape.weightFactor, hrnot, hsnot]
  · have hw : 0 < w := by
      let r0 : Fin t := ⟨0, by omega⟩
      have hr0 : r0.val + 1 < t := by simp [r0]; omega
      have hp : 0 < T.weight (v r0) := T.weight_pos (v r0)
      rw [hweights r0 hr0] at hp
      omega
    refine ⟨.B, w, dynkin_of_path_data T v hinj .B w hw (by simp) (by omega) hminus
      (fun r => ?_) (fun r s hrs => ?_) hzero⟩
    · by_cases hlast' : r.val + 1 = t
      · rw [hlast r hlast']
        simp [DynkinShape.weightFactor, hlast']
      · have hbefore : r.val + 1 < t := by omega
        rw [hweights r hbefore]
        simp [DynkinShape.weightFactor, hlast']
    · rw [hadj r s hrs]
      have hrnot : r.val + 1 ≠ t := by omega
      by_cases hsLast : s.val + 1 = t <;>
        simp [DynkinShape.weightFactor, hrnot, hsLast]

private lemma dynkin_of_four_chain (T : NumericalType)
    (hcount : 4 < T.componentCount) (v : Fin 4 → Fin T.componentCount)
    (hinj : Function.Injective v) (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hadj : ∀ r s, s.val = r.val + 1 → T.intersection (v r) (v s) ≠ 0) :
    ∃ u : Fin 4 → Fin T.componentCount, Function.Injective u ∧
      Set.range u = Set.range v ∧ ∃ d w, IsDynkinConfiguration T u d w := by
  classical
  let a : Fin 4 → Fin T.componentCount := ![v 0, v 1, v 2, v 3]
  have ha : a = v := by
    funext r
    fin_cases r <;> rfl
  have hinjA : Function.Injective a := by simpa [ha] using hinj
  obtain ⟨σ, w, hdata⟩ := four_minus_two_indices T hcount
    (v 0) (v 1) (v 2) (v 3) hinjA (hminus 0) (hminus 1) (hminus 2) (hminus 3)
    (by simpa using hadj 0 1 (by decide))
    (by simpa using hadj 1 2 (by decide))
    (by simpa using hadj 2 3 (by decide))
  let u : Fin 4 → Fin T.componentCount := a ∘ σ
  have huinj : Function.Injective u := hinjA.comp σ.injective
  have hurange : Set.range u = Set.range v := ha ▸ EquivLike.range_comp a σ
  refine ⟨u, huinj, hurange, ?_⟩
  rcases hdata with
      ⟨hweights, hmatrix, -, -, -, -⟩
    | ⟨hweights, hmatrix, -, -, -, -⟩
    | ⟨hweights, hmatrix, -, -, -, -⟩
    | ⟨hweights, hmatrix, -, -, -, -⟩ <;>
    [refine ⟨.A, w, ?_⟩; refine ⟨.C, w, ?_⟩; refine ⟨.B, w, ?_⟩; refine ⟨.F4, w, ?_⟩]
  all_goals
    have hw0 : T.weight (u 0) = _ := congrFun hweights 0
    have hw3 : T.weight (u 3) = _ := congrFun hweights 3
    have p0 := T.weight_pos (u 0)
    have p3 := T.weight_pos (u 3)
    simp at hw0 hw3
    refine isDynkinConfiguration_of_entries T u huinj _ w (by omega)
      (by simp [DynkinShape.Allows]) (fun r => ?_) (fun r s => ?_)
    · have h := congrFun hweights r
      fin_cases r <;> simpa [DynkinShape.weightFactor, u] using h
    · have h := congrFun (congrFun hmatrix r) s
      fin_cases r <;> fin_cases s <;>
        simpa [DynkinShape.Edge, DynkinShape.weightFactor, u] using h

private lemma dynkin_of_five_chain (T : NumericalType)
    (hcount : 5 < T.componentCount) (v : Fin 5 → Fin T.componentCount)
    (hinj : Function.Injective v) (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hadj : ∀ r s, s.val = r.val + 1 → T.intersection (v r) (v s) ≠ 0) :
    ∃ u : Fin 5 → Fin T.componentCount, Function.Injective u ∧
      Set.range u = Set.range v ∧ ∃ d w, IsDynkinConfiguration T u d w := by
  classical
  obtain ⟨σ, w, hw, hdata⟩ := five_chain_is_A5_or_C5_or_B5 T hcount
    v hinj hminus (by
      intro r
      exact hadj r.castSucc r.succ (by simp))
  let u : Fin 5 → Fin T.componentCount := v ∘ σ
  have huinj : Function.Injective u := hinj.comp σ.injective
  refine ⟨u, huinj, EquivLike.range_comp v σ, ?_⟩
  rcases hdata with ⟨hweights, hmatrix, -, -, -, -, -⟩ | ⟨hweights, hmatrix, -, -, -, -, -⟩ |
      ⟨hweights, hmatrix, -, -, -, -, -⟩ <;>
    [refine ⟨.A, w, ?_⟩; refine ⟨.C, w, ?_⟩; refine ⟨.B, w, ?_⟩]
  all_goals
    refine isDynkinConfiguration_of_entries T u huinj _ w hw
      (by simp [DynkinShape.Allows]) (fun r => ?_) (fun r s => ?_)
    · have h := congrFun hweights r
      fin_cases r <;> simpa [u, DynkinShape.weightFactor] using h
    · have h := congrFun (congrFun hmatrix r) s
      fin_cases r <;> fin_cases s <;>
        simpa [u, DynkinShape.Edge, DynkinShape.weightFactor] using h

private lemma dynkin_of_ordered_chain {t : ℕ} (T : NumericalType)
    (ht : 4 ≤ t) (hproper : t < T.componentCount)
    (v : Fin t → Fin T.componentCount) (hinj : Function.Injective v)
    (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (hadj : ∀ r s, s.val = r.val + 1 → T.intersection (v r) (v s) ≠ 0) :
    ∃ u : Fin t → Fin T.componentCount, Function.Injective u ∧
      Set.range u = Set.range v ∧ ∃ d w, IsDynkinConfiguration T u d w := by
  classical
  by_cases ht4 : t = 4
  · subst t
    exact dynkin_of_four_chain T (by omega) v hinj hminus hadj
  · by_cases ht5 : t = 5
    · subst t
      exact dynkin_of_five_chain T (by omega) v hinj hminus hadj
    · have htlarge : 5 < t := by omega
      rcases classify_long_chain_of_minus_two_indices
          T v htlarge hproper hinj hminus hadj with hcfg | hcfg
      · obtain ⟨d, w, hdynkin⟩ := dynkin_of_long_chain T v hinj hminus htlarge hcfg
        exact ⟨v, hinj, rfl, d, w, hdynkin⟩
      · let u : Fin t → Fin T.componentCount := v ∘ Fin.revPerm
        have huinj : Function.Injective u := hinj.comp Fin.rev_injective
        have hminusu : ∀ r, IsMinusTwoIndex T (u r) := fun r => hminus (Fin.rev r)
        obtain ⟨d, w, hdynkin⟩ := dynkin_of_long_chain T u huinj hminusu htlarge hcfg
        exact ⟨u, huinj, EquivLike.range_comp v Fin.revPerm, d, w, hdynkin⟩

private lemma classify_two_vertex_subset (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hproper : I.card < T.componentCount)
    (hminus : ∀ i ∈ I, IsMinusTwoIndex T i)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0))
    (htwo : I.card = 2) :
    ∃ v : Fin 2 → Fin T.componentCount,
      Function.Injective v ∧ Set.range v = (I : Set (Fin T.componentCount)) ∧
        ∃ d w, IsDynkinConfiguration T v d w := by
  classical
  obtain ⟨i, j, hij, hI⟩ := (Finset.card_eq_two).mp htwo
  have hi : i ∈ I := by simp [hI]
  have hj : j ∈ I := by simp [hI]
  have hint : T.intersection i j ≠ 0 := by
    obtain ⟨x, hx, y, hy, hxy, hval⟩ :=
      exists_distinct_intersecting_pair T I (by omega) hconnected
    have hx' : x = i ∨ x = j := by simpa [hI] using hx
    have hy' : y = i ∨ y = j := by simpa [hI] using hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact (hxy rfl).elim
    · exact hval
    · rwa [T.intersection_symm]
    · exact (hxy rfl).elim
  have hpos : 0 < T.intersection i j := by
    have hnonneg := T.intersection_nonneg i j hij
    omega
  have hclass := isTwoVertexConfiguration_or_swap T (by omega)
    i j (hminus i hi) (hminus j hj) hpos
  rcases hclass with hclass | hclass
  · obtain ⟨v, hv, hrange, d, w, hcfg⟩ :=
      exists_dynkin_ordering_of_two_vertex_configuration T i j hij hclass
    exact ⟨v, hv, by simpa [hI] using hrange, d, w, hcfg⟩
  · obtain ⟨v, hv, hrange, d, w, hcfg⟩ :=
      exists_dynkin_ordering_of_two_vertex_configuration T j i hij.symm hclass
    exact ⟨v, hv, by simpa [Set.pair_comm, hI] using hrange, d, w, hcfg⟩

private lemma dynkin_of_three_vertex_path (T : NumericalType)
    (hn : 3 < T.componentCount) (i j k : Fin T.componentCount)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hk : IsMinusTwoIndex T k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hedges : (T.intersection i j ≠ 0 ∧ T.intersection i k ≠ 0) ∨
      (T.intersection i j ≠ 0 ∧ T.intersection j k ≠ 0) ∨
      (T.intersection i k ≠ 0 ∧ T.intersection j k ≠ 0)) :
    ∃ v : Fin 3 → Fin T.componentCount,
      Function.Injective v ∧ Set.range v = {i, j, k} ∧
        ∃ d w, IsDynkinConfiguration T v d w := by
  obtain ⟨v, hv, hvrange, hdata⟩ :=
    exists_ordering_of_three_minus_two_indices
      T hn i j k hi hj hk hij hik hjk hedges
  refine ⟨v, hv, hvrange, ?_⟩
  rcases hdata with
    ⟨w, hw0, hw1, hw2, hd0, he01, he02, he10, hd1, he12, he20, he21, hd2,
      hm0, hm1, hm2⟩
    | ⟨w, hw0, hw1, hw2, hd0, he01, he02, he10, hd1, he12, he20, he21, hd2,
      hm0, hm1, hm2⟩
    | ⟨w, hw0, hw1, hw2, hd0, he01, he02, he10, hd1, he12, he20, he21, hd2,
      hm0, hm1, hm2⟩ <;>
    [refine ⟨.A, w, ?_⟩; refine ⟨.C, w, ?_⟩; refine ⟨.B, w, ?_⟩]
  all_goals
    have hpos : 0 < w := by
      have := T.weight_pos (v 0)
      have := T.weight_pos (v 2)
      omega
    dsimp [IsDynkinConfiguration]
    refine ⟨by simp [DynkinShape.Allows], hpos, ?_, ?_, ?_⟩
    · intro r
      fin_cases r <;> simp [DynkinShape.weightFactor, hw0, hw1, hw2]
    · intro r s
      fin_cases r <;> fin_cases s <;>
        simp [DynkinShape.Edge, DynkinShape.weightFactor, hd0, hd1, hd2,
          he01, he02, he10, he12, he20, he21]
    · intro r
      fin_cases r <;>
        simp [DynkinShape.Edge, DynkinShape.weightFactor, Fin.sum_univ_three] <;> omega

private lemma classify_three_vertex_subset (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hproper : I.card < T.componentCount)
    (hminus : ∀ i ∈ I, IsMinusTwoIndex T i)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0))
    (hthree : I.card = 3) :
    ∃ v : Fin 3 → Fin T.componentCount,
      Function.Injective v ∧ Set.range v = (I : Set (Fin T.componentCount)) ∧
        ∃ d w, IsDynkinConfiguration T v d w := by
  classical
  obtain ⟨i, j, k, hij, hik, hjk, hI⟩ := (Finset.card_eq_three.mp hthree)
  have hi : i ∈ I := by simp [hI]
  have hj : j ∈ I := by simp [hI]
  have hk : k ∈ I := by simp [hI]
  have hcut : ∀ a ∈ I, ∃ b ∈ I, b ≠ a ∧ T.intersection a b ≠ 0 := by
    intro a ha
    by_contra hzero
    push Not at hzero
    apply hconnected
    have hsub : ({a} : Finset (Fin T.componentCount)) ⊂ I := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr ha, ?_⟩
      intro heq
      have hc := congrArg Finset.card heq
      simp at hc
      omega
    refine ⟨{a}, Finset.singleton_nonempty a, hsub, ?_⟩
    intro x hx y hy hyNot
    obtain rfl := Finset.mem_singleton.mp hx
    exact hzero y hy (by rintro rfl; exact hyNot (Finset.mem_singleton_self _))
  have hcut_i : T.intersection i j ≠ 0 ∨ T.intersection i k ≠ 0 := by
    obtain ⟨b, hb, hbi, hne⟩ := hcut i hi
    simp only [hI, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    exacts [(hbi rfl).elim, Or.inl hne, Or.inr hne]
  have hcut_j : T.intersection j i ≠ 0 ∨ T.intersection j k ≠ 0 := by
    obtain ⟨b, hb, hbj, hne⟩ := hcut j hj
    simp only [hI, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    exacts [Or.inl hne, (hbj rfl).elim, Or.inr hne]
  have hcut_k : T.intersection k i ≠ 0 ∨ T.intersection k j ≠ 0 := by
    obtain ⟨b, hb, hbk, hne⟩ := hcut k hk
    simp only [hI, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    exacts [Or.inl hne, Or.inr hne, (hbk rfl).elim]
  have hedges :
      (T.intersection i j ≠ 0 ∧ T.intersection i k ≠ 0) ∨
        (T.intersection i j ≠ 0 ∧ T.intersection j k ≠ 0) ∨
        (T.intersection i k ≠ 0 ∧ T.intersection j k ≠ 0) := by
    rcases hcut_k with hki | hkj
    · rcases hcut_j with hji | hjk'
      · exact Or.inl ⟨by rwa [T.intersection_symm], by rwa [T.intersection_symm]⟩
      · exact Or.inr (Or.inr ⟨by rwa [T.intersection_symm], hjk'⟩)
    · rcases hcut_i with hij' | hik'
      · exact Or.inr (Or.inl ⟨hij', by rwa [T.intersection_symm]⟩)
      · exact Or.inr (Or.inr ⟨hik', by rwa [T.intersection_symm]⟩)
  obtain ⟨v, hv, hvrange, d, w, hcfg⟩ :=
    dynkin_of_three_vertex_path T (by omega) i j k
      (hminus i hi) (hminus j hj) (hminus k hk) hij hik hjk hedges
  exact ⟨v, hv, by simpa [hI] using hvrange, d, w, hcfg⟩

private lemma dynkin_of_d4_ordering (T : NumericalType)
    (hcount : 4 < T.componentCount) (v : Fin 4 → Fin T.componentCount)
    (hinj : Function.Injective v) (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h₀₁ : T.intersection (v 1) (v 0) ≠ 0)
    (h₁₂ : T.intersection (v 1) (v 2) ≠ 0)
    (h₁₃ : T.intersection (v 1) (v 3) ≠ 0) :
    ∃ d w, IsDynkinConfiguration T v d w := by
  classical
  obtain ⟨w, hw, hweight0, hweight1, hweight2, hweight3,
      _, _, _, _, h10, h01, h12, h21, h13, h31,
      h02, h20, h03, h30, h23, h32, _⟩ :=
    exists_d4_configuration_of_four_isMinusTwoIndex T hcount
      (v 1) (v 0) (v 2) (v 3)
      (by intro h; exact (by decide : (1 : Fin 4) ≠ 0) (hinj h))
      (by intro h; exact (by decide : (1 : Fin 4) ≠ 2) (hinj h))
      (by intro h; exact (by decide : (1 : Fin 4) ≠ 3) (hinj h))
      (by intro h; exact (by decide : (0 : Fin 4) ≠ 2) (hinj h))
      (by intro h; exact (by decide : (0 : Fin 4) ≠ 3) (hinj h))
      (by intro h; exact (by decide : (2 : Fin 4) ≠ 3) (hinj h))
      (hminus 1) (hminus 0) (hminus 2) (hminus 3) h₀₁ h₁₂ h₁₃
  let d : DynkinShape := .D
  have hallows : d.Allows 4 := by simp [d, DynkinShape.Allows]
  have hweight : ∀ r, T.weight (v r) = d.weightFactor r * w := by
    intro r
    fin_cases r <;> simp [d, DynkinShape.weightFactor, hweight0, hweight1,
      hweight2, hweight3]
  have hentry : ∀ r s, T.intersection (v r) (v s) =
      if r = s then -2 * d.weightFactor r * w
      else if d.Edge r s then max (d.weightFactor r) (d.weightFactor s) * w else 0 := by
    intro r s
    fin_cases r <;> fin_cases s <;>
      simp [d, DynkinShape.Edge, DynkinShape.weightFactor, hweight0, hweight1,
        hweight2, hweight3, h10, h01, h12, h21, h13, h31,
        h02, h20, h03, h30, h23, h32, (hminus 0).2, (hminus 1).2,
        (hminus 2).2, (hminus 3).2]
  exact ⟨d, w, isDynkinConfiguration_of_entries T v hinj d w hw hallows hweight hentry⟩

private lemma dynkin_of_d5_ordering (T : NumericalType)
    (hcount : 5 < T.componentCount) (v : Fin 5 → Fin T.componentCount)
    (hinj : Function.Injective v) (hminus : ∀ r, IsMinusTwoIndex T (v r))
    (h₀₁ : T.intersection (v 0) (v 1) ≠ 0)
    (h₁₂ : T.intersection (v 1) (v 2) ≠ 0)
    (h₂₃ : T.intersection (v 2) (v 3) ≠ 0)
    (h₂₄ : T.intersection (v 2) (v 4) ≠ 0) :
    ∃ d w, IsDynkinConfiguration T v d w := by
  classical
  let e : Fin 5 ↪ Fin T.componentCount := ⟨v, hinj⟩
  obtain ⟨w, hweights, hmatrix⟩ :=
    exists_weight_eq_d5_of_isMinusTwoIndex T hcount e hminus
      h₀₁ h₁₂ h₂₃ h₂₄
  let d : DynkinShape := .D
  have hallows : d.Allows 5 := by simp [d, DynkinShape.Allows]
  have hw : 0 < w := by
    have hp := T.weight_pos (v 0)
    rw [show T.weight (v 0) = w by simpa [e] using congrFun hweights 0] at hp
    exact hp
  have hweight : ∀ r, T.weight (v r) = d.weightFactor r * w := by
    intro r
    have h := congrFun hweights r
    fin_cases r <;> simpa [e, d, DynkinShape.weightFactor] using h
  have hentry : ∀ r s, T.intersection (v r) (v s) =
      if r = s then -2 * d.weightFactor r * w
      else if d.Edge r s then max (d.weightFactor r) (d.weightFactor s) * w else 0 := by
    intro r s
    have h := congrFun (congrFun hmatrix r) s
    fin_cases r <;> fin_cases s <;>
      simpa [e, d, DynkinShape.Edge, DynkinShape.weightFactor] using h
  exact ⟨d, w, isDynkinConfiguration_of_entries T v hinj d w hw hallows hweight hentry⟩

end AlgebraicGeometry.NumericalType
