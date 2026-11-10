module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.IntervalCases
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FiveChain
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FiveVertices
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FourVertices
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.LongChain
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.ThreeVertices
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.TwoVertices

/-!
# The incidence graph of a set of minus-two indices

The incidence graph of a set of components of a numerical type joins two
distinct components when they meet. For a connected proper set of minus-two
indices it is connected and acyclic: cycles of every length are excluded by
exhibiting a positive vector supported on the cycle in the zero locus of the
intersection form. A fourth neighbour is excluded by the four-vertex
classification, so every vertex has degree at most three.

This is the first step of the classification of connected proper subgraphs of
minus-two indices, see
`StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification`.

## Main results

* `AlgebraicGeometry.NumericalType.minusTwoGraph`: the incidence graph.
* `AlgebraicGeometry.NumericalType.minusTwoGraph_isAcyclic`: the incidence graph has no cycles.
* `AlgebraicGeometry.NumericalType.intersection_eq_max_weight_of_intersects`: two meeting minus-two
  indices have intersection number the larger of their two weights.
* `AlgebraicGeometry.NumericalType.minusTwoGraph_degree_le_three`: every vertex
  has degree at most three.

## References

* [Stacks Project, Tag 0C8Q](https://stacks.math.columbia.edu/tag/0C8Q)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

open Matrix

/-- The incidence graph of a set of components of a numerical type: two
components are joined when they are distinct and meet. -/
public def minusTwoGraph (T : NumericalType)
    (I : Finset (Fin T.componentCount)) : SimpleGraph {i // i ∈ I} where
  Adj x y := x.val ≠ y.val ∧ T.intersection x.val y.val ≠ 0
  symm := ⟨fun {x y} h =>
    ⟨h.1.symm, by rw [T.intersection_symm]; exact h.2⟩⟩
  loopless := ⟨fun {x} h => h.1 rfl⟩

private lemma minusTwoGraph_connected (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hcard : 1 ≤ I.card)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0)) :
    (minusTwoGraph T I).Connected := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
  let x : {i // i ∈ I} := ⟨i, hi⟩
  have hxreach : ∀ y : {i // i ∈ I}, (minusTwoGraph T I).Reachable x y := by
    intro y
    by_contra hxy
    let J : Finset (Fin T.componentCount) := I.filter fun j =>
      ∃ hj : j ∈ I, (minusTwoGraph T I).Reachable x ⟨j, hj⟩
    have hxi : i ∈ J := by
      apply Finset.mem_filter.mpr
      refine ⟨hi, ?_⟩
      exact ⟨hi, SimpleGraph.Reachable.rfl⟩
    have hsub : J ⊆ I := Finset.filter_subset _ _
    have hyJ : y.val ∉ J := by
      intro hyJ
      rcases Finset.mem_filter.mp hyJ with ⟨_, ⟨_, hreach⟩⟩
      exact hxy hreach
    have hJne : J.Nonempty := ⟨i, hxi⟩
    have hJneq : J ≠ I := by
      intro heq
      exact hyJ (by simp [heq])
    have hJproper : J ⊂ I := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hJneq⟩
    apply hconnected
    refine ⟨J, hJne, hJproper, ?_⟩
    intro a ha b hb hbnot
    by_contra hab
    have hne : a ≠ b := by
      intro heq
      subst b
      exact hbnot ha
    have hreach : (minusTwoGraph T I).Reachable x ⟨a, hsub ha⟩ := by
      rcases Finset.mem_filter.mp ha with ⟨_, ⟨haI, hreach⟩⟩
      exact hreach
    have hadj : (minusTwoGraph T I).Adj ⟨a, hsub ha⟩ ⟨b, hb⟩ := by
      change a ≠ b ∧ T.intersection a b ≠ 0
      exact ⟨hne, hab⟩
    have hreachb := hreach.trans hadj.reachable
    have hbJ : b ∈ J := Finset.mem_filter.mpr ⟨hb, ⟨hb, hreachb⟩⟩
    exact hbnot hbJ
  let : Nonempty {i // i ∈ I} := ⟨x⟩
  exact ⟨fun y z => (hxreach y).symm.trans (hxreach z)⟩

private lemma long_chain_endpoints_disjoint {t : ℕ} (T : NumericalType)
    (ht : 5 < t) (v : Fin t → Fin T.componentCount)
    (hcfg : IsLongChainConfiguration T v) :
    T.intersection (v ⟨0, by omega⟩) (v ⟨t - 1, by omega⟩) = 0 := by
  rcases hcfg with ⟨w, _, _, hzero⟩ | ⟨w, _, _, _, _, hzero⟩ |
      ⟨w, _, _, _, hzero⟩
  all_goals exact hzero ⟨0, by omega⟩ ⟨t - 1, by omega⟩ (by simp; omega)

private lemma no_long_cycle_path (T : NumericalType) {t : ℕ}
    (ht : 5 < t) (hproper : t < T.componentCount)
    (v : Fin t → Fin T.componentCount) (hinj : Function.Injective v)
    (hminus : ∀ j, IsMinusTwoIndex T (v j))
    (hadj : ∀ j k, k.val = j.val + 1 → T.intersection (v j) (v k) ≠ 0)
    (hclose : T.intersection (v ⟨t - 1, by omega⟩) (v ⟨0, by omega⟩) ≠ 0) : False := by
  rcases classify_long_chain_of_minus_two_indices
      T v ht hproper hinj hminus hadj with hcfg | hcfg
  · have hz := long_chain_endpoints_disjoint T ht v hcfg
    apply hclose
    rw [T.intersection_symm]
    exact hz
  · have hz := long_chain_endpoints_disjoint T ht (fun j => v (Fin.rev j)) hcfg
    let j₀ : Fin t := ⟨0, by omega⟩
    let jₗ : Fin t := ⟨t - 1, by omega⟩
    have hrev₀ : Fin.rev j₀ = jₗ := by
      apply Fin.ext
      simp [j₀, jₗ]
    have hrevₗ : Fin.rev jₗ = j₀ := by
      rw [← hrev₀, Fin.rev_rev]
    rw [hrev₀, hrevₗ] at hz
    exact hclose hz

private lemma no_intersecting_triangle (T : NumericalType)
    (hn : 3 < T.componentCount) (i j k : Fin T.componentCount)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hk : IsMinusTwoIndex T k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (eij : T.intersection i j ≠ 0) (eik : T.intersection i k ≠ 0)
    (ejk : T.intersection j k ≠ 0) : False := by
  obtain ⟨v, hv, hvrange, hdata⟩ :=
    exists_ordering_of_three_minus_two_indices T hn i j k hi hj hk
      hij hik hjk (Or.inl ⟨eij, eik⟩)
  have hv0 : v 0 = i ∨ v 0 = j ∨ v 0 = k := by
    have hm : v 0 ∈ Set.range v := ⟨0, rfl⟩
    rw [hvrange] at hm
    simpa using hm
  have hv2 : v 2 = i ∨ v 2 = j ∨ v 2 = k := by
    have hm : v 2 ∈ Set.range v := ⟨2, rfl⟩
    rw [hvrange] at hm
    simpa using hm
  have hv02 : v 0 ≠ v 2 := by
    intro heq
    have hfin : (0 : Fin 3) = 2 := hv heq
    exact (by decide : (0 : Fin 3) ≠ 2) hfin
  have h02 : T.intersection (v 0) (v 2) ≠ 0 := by
    rcases hv0 with h0 | h0 | h0 <;> rcases hv2 with h2 | h2 | h2 <;>
      simp_all [T.intersection_symm]
  rcases hdata with
    ⟨w, _, _, _, _, _, hzero, _, _, _, _, _, _, _, _⟩
    | ⟨w, _, _, _, _, _, hzero, _, _, _, _, _, _, _, _⟩
    | ⟨w, _, _, _, _, _, hzero, _, _, _, _, _, _, _, _⟩
  · exact h02 hzero
  · exact h02 hzero
  · exact h02 hzero

/-- In a cycle of minus-two indices, the row of `σ 0` cannot vanish outside `σ 1`: the vertex
`σ 0` has two distinct neighbours on the cycle. -/
private lemma no_cycle_row_zero (T : NumericalType) {n : ℕ} (v : Fin (n + 3) → Fin T.componentCount)
    (hcyc : ∀ k, T.intersection (v k) (v (k + 1)) ≠ 0) (σ : Equiv.Perm (Fin (n + 3)))
    (hzero : ∀ q, q ≠ 0 → q ≠ 1 → T.intersection (v (σ 0)) (v (σ q)) = 0) : False := by
  have key : ∀ i, i ≠ σ 0 → T.intersection (v (σ 0)) (v i) ≠ 0 → σ.symm i ≠ 1 → False :=
    fun i hi he h1 => he (by
      simpa using hzero (σ.symm i) (fun h => hi (by simpa using congrArg σ h)) h1)
  by_cases h : σ.symm (σ 0 + 1) = 1
  · refine key (σ 0 - 1) (by simp) ?_ fun h' => ?_
    · rw [T.intersection_symm]
      simpa using hcyc (σ 0 - 1)
    · have e := σ.symm.injective (h.trans h'.symm)
      have e2 : σ 0 + (1 + 1) = σ 0 + 0 := by rw [← add_assoc, e, sub_add_cancel, add_zero]
      have := congrArg Fin.val (add_left_cancel e2)
      rw [Fin.val_add, Fin.val_zero] at this
      simp [Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at this
  · exact key (σ 0 + 1) (by simp) (hcyc _) h

private lemma no_four_cycle (T : NumericalType) (hcount : 4 < T.componentCount)
    (a b c d : Fin T.componentCount)
    (hinj : Function.Injective ![a, b, c, d])
    (ha : IsMinusTwoIndex T a) (hb : IsMinusTwoIndex T b)
    (hc : IsMinusTwoIndex T c) (hd : IsMinusTwoIndex T d)
    (hab : T.intersection a b ≠ 0) (hbc : T.intersection b c ≠ 0)
    (hcd : T.intersection c d ≠ 0) (hda : T.intersection d a ≠ 0) : False := by
  obtain ⟨σ, w, hdata⟩ := four_minus_two_indices T hcount
    a b c d hinj ha hb hc hd hab hbc hcd
  let r : Fin 4 → Fin T.componentCount := ![a, b, c, d] ∘ σ
  rcases hdata with ⟨_, hmat, _, _, _, _⟩ | ⟨_, hmat, _, _, _, _⟩ |
      ⟨_, hmat, _, _, _, _⟩ | ⟨_, hmat, _, _, _, _⟩
  all_goals
    have hzero : ∀ q : Fin 4, q ≠ 0 → q ≠ 1 → T.intersection (r 0) (r q) = 0 := by
      intro q hq0 hq1
      fin_cases q
      · exact (hq0 rfl).elim
      · exact (hq1 rfl).elim
      · have h := congrFun (congrFun hmat 0) 2
        simpa [r] using h
      · have h := congrFun (congrFun hmat 0) 3
        simpa [r] using h
    refine no_cycle_row_zero T ![a, b, c, d] (fun k => ?_) σ hzero
    fin_cases k
    exacts [hab, hbc, hcd, hda]

private lemma no_five_cycle (T : NumericalType) (hcount : 5 < T.componentCount)
    (a b c d e : Fin T.componentCount)
    (hinj : Function.Injective ![a, b, c, d, e])
    (ha : IsMinusTwoIndex T a) (hb : IsMinusTwoIndex T b)
    (hc : IsMinusTwoIndex T c) (hd : IsMinusTwoIndex T d)
    (he : IsMinusTwoIndex T e)
    (hab : T.intersection a b ≠ 0) (hbc : T.intersection b c ≠ 0)
    (hcd : T.intersection c d ≠ 0) (hde : T.intersection d e ≠ 0)
    (hea : T.intersection e a ≠ 0) : False := by
  obtain ⟨σ, w, hw, hdata⟩ := five_chain_is_A5_or_C5_or_B5 T hcount
    (![a, b, c, d, e] : Fin 5 → Fin T.componentCount) hinj (by
      intro r
      fin_cases r <;> assumption) (by
      intro r
      fin_cases r
      · exact hab
      · exact hbc
      · exact hcd
      · exact hde)
  let r : Fin 5 → Fin T.componentCount := ![a, b, c, d, e] ∘ σ
  rcases hdata with hdata | hdata | hdata
  all_goals
    rcases hdata with ⟨_, hmat, _, _, _, _, _⟩
    have hzero : ∀ q : Fin 5, q ≠ 0 → q ≠ 1 →
        T.intersection (r 0) (r q) = 0 := by
      intro q hq0 hq1
      fin_cases q
      · exact (hq0 rfl).elim
      · exact (hq1 rfl).elim
      · have h := congrFun (congrFun hmat 0) 2
        simpa [r] using h
      · have h := congrFun (congrFun hmat 0) 3
        simpa [r] using h
      · have h := congrFun (congrFun hmat 0) 4
        simpa [r] using h
    refine no_cycle_row_zero T ![a, b, c, d, e] (fun k => ?_) σ hzero
    fin_cases k
    exacts [hab, hbc, hcd, hde, hea]

/-- Two distinct positions `1 ≤ i < j ≤ length` of a cycle carry distinct vertices. -/
private lemma getVert_ne_of_isCycle {V : Type*} {G : SimpleGraph V} {x : V} {p : G.Walk x x}
    (hp : p.IsCycle) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ p.length) :
    p.getVert i ≠ p.getVert j := fun h => by
  have := hp.getVert_injOn (by simp; omega) (by simp; omega) h
  omega

/-- Consecutive vertices of a walk in the incidence graph have nonzero intersection number. -/
private lemma intersection_getVert_succ_ne_zero (T : NumericalType)
    (I : Finset (Fin T.componentCount)) {x y : {i // i ∈ I}} (p : (minusTwoGraph T I).Walk x y)
    {i : ℕ} (hi : i < p.length) :
    T.intersection (p.getVert i).val (p.getVert (i + 1)).val ≠ 0 :=
  (p.adj_getVert_succ hi).2

/-- The last vertex of a nontrivial closed walk meets its first step. -/
private lemma intersection_getVert_length_ne_zero (T : NumericalType)
    (I : Finset (Fin T.componentCount)) {x : {i // i ∈ I}} (p : (minusTwoGraph T I).Walk x x)
    (hp : 0 < p.length) :
    T.intersection (p.getVert p.length).val (p.getVert 1).val ≠ 0 := by
  simpa using intersection_getVert_succ_ne_zero T I p hp

private lemma minusTwoGraph_no_cycle_length_gt_five (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hproper : I.card < T.componentCount)
    (hminus : ∀ j ∈ I, IsMinusTwoIndex T j)
    {x : {i // i ∈ I}} (p : (minusTwoGraph T I).Walk x x)
    (hcycle : p.IsCycle) (hlength : 5 < p.length) : False := by
  classical
  let t := p.length
  let v : Fin t → Fin T.componentCount := fun r => (p.getVert (r.val + 1)).val
  let u : Fin t → {i // i ∈ I} := fun r => p.getVert (r.val + 1)
  have hu_inj : Function.Injective u := by
    intro a b hab
    apply Fin.ext
    have hab'' := hcycle.getVert_injOn (by simp; omega) (by simp; omega) hab
    omega
  have hv_inj : Function.Injective v := fun a b hab => hu_inj (Subtype.ext hab)
  have htproper : t < T.componentCount := by
    have hcard := Fintype.card_le_of_injective u hu_inj
    have hcard' : t ≤ I.card := by
      calc
        t = Fintype.card (Fin t) := (Fintype.card_fin t).symm
        _ ≤ Fintype.card {i // i ∈ I} := hcard
        _ = I.card := Fintype.card_coe I
    exact lt_of_le_of_lt hcard' hproper
  have hminus' : ∀ j, IsMinusTwoIndex T (v j) := by
    intro j
    exact hminus (v j) (u j).property
  have hadj : ∀ j k, k.val = j.val + 1 →
      T.intersection (v j) (v k) ≠ 0 := by
    intro j k hjk
    have h := intersection_getVert_succ_ne_zero T I p (i := j.val + 1) (by omega)
    rwa [show v k = (p.getVert (j.val + 1 + 1)).val by simp [v, hjk]]
  have hclose : T.intersection (v ⟨t - 1, by omega⟩) (v ⟨0, by omega⟩) ≠ 0 := by
    have h := intersection_getVert_length_ne_zero T I p (by omega)
    have hidx : (⟨t - 1, by omega⟩ : Fin t).val + 1 = t := by simp; omega
    simpa [v, t, hidx] using h
  exact no_long_cycle_path T hlength htproper v hv_inj hminus' hadj hclose

private lemma minusTwoGraph_isAcyclic (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hcard : 5 ≤ I.card)
    (hproper : I.card < T.componentCount)
    (hminus : ∀ j ∈ I, IsMinusTwoIndex T j) :
    (minusTwoGraph T I).IsAcyclic := by
  classical
  intro x p hp
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hne := fun i j => getVert_ne_of_isCycle hp (i := i) (j := j)
  have hedge := fun i hi => intersection_getVert_succ_ne_zero T I p (i := i) hi
  have hclose := intersection_getVert_length_ne_zero T I p (by omega)
  by_cases h3 : p.length = 3
  · let a := (p.getVert 1).val
    let b := (p.getVert 2).val
    let c := (p.getVert 3).val
    have hcount : 3 < T.componentCount := by omega
    have h12 := hne 1 2 (by omega) (by omega) (by omega)
    have h23 := hne 2 3 (by omega) (by omega) (by omega)
    have h13 := hne 1 3 (by omega) (by omega) (by omega)
    have eca : T.intersection c a ≠ 0 := by simpa [h3] using hclose
    exact no_intersecting_triangle T hcount a b c (hminus a (p.getVert 1).property)
      (hminus b (p.getVert 2).property) (hminus c (p.getVert 3).property)
      (fun hh => h12 (Subtype.ext hh)) (fun hh => h13 (Subtype.ext hh))
      (fun hh => h23 (Subtype.ext hh)) (hedge 1 (by omega)) (by rwa [T.intersection_symm])
      (hedge 2 (by omega))
  · by_cases h4 : p.length = 4
    · let a := (p.getVert 1).val
      let b := (p.getVert 2).val
      let c := (p.getVert 3).val
      let d := (p.getVert 4).val
      have hcount : 4 < T.componentCount := by omega
      have h12 := hne 1 2 (by omega) (by omega) (by omega)
      have h13 := hne 1 3 (by omega) (by omega) (by omega)
      have h14 := hne 1 4 (by omega) (by omega) (by omega)
      have h23 := hne 2 3 (by omega) (by omega) (by omega)
      have h24 := hne 2 4 (by omega) (by omega) (by omega)
      have h34 := hne 3 4 (by omega) (by omega) (by omega)
      have hinj : Function.Injective (![a, b, c, d] : Fin 4 → Fin T.componentCount) := by
        clear hne hedge hclose
        intro r s hrs
        fin_cases r <;> fin_cases s <;> simp_all [a, b, c, d]
      have eda : T.intersection d a ≠ 0 := by simpa [h4] using hclose
      exact no_four_cycle T hcount a b c d hinj (hminus a (p.getVert 1).property)
        (hminus b (p.getVert 2).property) (hminus c (p.getVert 3).property)
        (hminus d (p.getVert 4).property) (hedge 1 (by omega)) (hedge 2 (by omega))
        (hedge 3 (by omega)) eda
    · by_cases h5 : p.length = 5
      · let a := (p.getVert 1).val
        let b := (p.getVert 2).val
        let c := (p.getVert 3).val
        let d := (p.getVert 4).val
        let e := (p.getVert 5).val
        have hcount : 5 < T.componentCount := by omega
        have h12 := hne 1 2 (by omega) (by omega) (by omega)
        have h13 := hne 1 3 (by omega) (by omega) (by omega)
        have h14 := hne 1 4 (by omega) (by omega) (by omega)
        have h15 := hne 1 5 (by omega) (by omega) (by omega)
        have h23 := hne 2 3 (by omega) (by omega) (by omega)
        have h24 := hne 2 4 (by omega) (by omega) (by omega)
        have h25 := hne 2 5 (by omega) (by omega) (by omega)
        have h34 := hne 3 4 (by omega) (by omega) (by omega)
        have h35 := hne 3 5 (by omega) (by omega) (by omega)
        have h45 := hne 4 5 (by omega) (by omega) (by omega)
        have hinj : Function.Injective (![a, b, c, d, e] : Fin 5 → Fin T.componentCount) := by
          clear hne hedge hclose
          intro r s hrs
          fin_cases r <;> fin_cases s <;> simp_all [a, b, c, d, e]
        have eea : T.intersection e a ≠ 0 := by simpa [h5] using hclose
        exact no_five_cycle T hcount a b c d e hinj (hminus a (p.getVert 1).property)
          (hminus b (p.getVert 2).property) (hminus c (p.getVert 3).property)
          (hminus d (p.getVert 4).property) (hminus e (p.getVert 5).property)
          (hedge 1 (by omega)) (hedge 2 (by omega)) (hedge 3 (by omega))
          (hedge 4 (by omega)) eea
      · exact minusTwoGraph_no_cycle_length_gt_five T I hproper hminus p hp (by omega)

private lemma quadraticForm_neg_of_supported_proper_finset
    (T : NumericalType) (I : Finset (Fin T.componentCount))
    (hproper : I.card < T.componentCount) (x : Fin T.componentCount → ℚ)
    (hsupport : ∀ i, i ∉ I → x i = 0) (hnonzero : x ≠ 0) :
    x ⬝ᵥ ((fun i j => (T.intersection i j : ℚ)) *ᵥ x) < 0 := by
  let A : Matrix (Fin T.componentCount) (Fin T.componentCount) ℚ :=
    fun i j => (T.intersection i j : ℚ)
  let m : Fin T.componentCount → ℚ := fun i => T.multiplicity i
  have hsymm : A.IsSymm := by
    apply Matrix.IsSymm.ext_iff.mpr
    intro i j
    change (T.intersection j i : ℚ) = (T.intersection i j : ℚ)
    exact_mod_cast T.intersection_symm j i
  have hoff : ∀ i j, i ≠ j → 0 ≤ A i j := by
    intro i j hij
    simp only [A]
    exact_mod_cast T.intersection_nonneg i j hij
  have hm : ∀ i, 0 < m i := by
    intro i
    simp only [m]
    exact_mod_cast T.multiplicity_pos i
  have hAm : A *ᵥ m = 0 := by
    ext i
    change (∑ j, (T.intersection i j : ℚ) * (T.multiplicity j : ℚ)) = 0
    exact_mod_cast T.intersection_mul_multiplicity i
  have hconn : ∀ J : Set (Fin T.componentCount), J.Nonempty → J ≠ Set.univ →
      ¬ ∀ i ∈ J, ∀ j ∉ J, A i j = 0 := by
    intro J hne hproperJ hzero
    apply T.connected
    refine ⟨J, hne, hproperJ, ?_⟩
    · intro i hi j hj
      have hz := hzero i hi j hj
      simp only [A] at hz
      exact_mod_cast hz
  have hzero : x ⬝ᵥ (A *ᵥ x) = 0 → ∃ q : ℚ, x = q • m :=
    (Matrix.dotProduct_mulVec_eq_zero_iff_of_positive_kernel
      hsymm hoff hm hAm hconn).mp
  have hq : x ⬝ᵥ (A *ᵥ x) ≤ 0 :=
    Matrix.dotProduct_mulVec_nonpos_of_positive_kernel hsymm hoff hm hAm x
  have hxnot : ¬ ∃ q : ℚ, x = q • m := by
    rintro ⟨q, hq⟩
    obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
      by_contra h
      push Not at h
      have : I = Finset.univ := Finset.eq_univ_iff_forall.mpr h
      have hc := congrArg Finset.card this
      simp only [Finset.card_univ, Fintype.card_fin] at hc
      omega
    have := congrFun hq j
    rw [hsupport j hj] at this
    simp only [Pi.smul_apply, smul_eq_mul, m] at this
    have hpos : (0 : ℚ) < T.multiplicity j := by exact_mod_cast T.multiplicity_pos j
    have : q = 0 := by nlinarith
    subst q
    apply hnonzero
    funext i
    have := congrFun hq i
    simp only [Pi.smul_apply, smul_eq_mul, m, zero_mul] at this
    exact this
  have hneq : x ⬝ᵥ (A *ᵥ x) ≠ 0 := by
    intro hz
    have hex : ∃ q : ℚ, x = q • m := hzero hz
    exact hxnot hex
  exact lt_of_le_of_ne hq hneq

private lemma exists_distinct_intersecting_pair
    (T : NumericalType) (I : Finset (Fin T.componentCount))
    (hcard : 2 ≤ I.card)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0)) :
    ∃ i ∈ I, ∃ j ∈ I, i ≠ j ∧ T.intersection i j ≠ 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := I.card_pos.mp (by omega)
  have hsub : ({i} : Finset (Fin T.componentCount)) ⊂ I := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      simpa [hx] using hi
    · intro heq
      have hc := congrArg Finset.card heq
      simp at hc
      omega
  apply hconnected
  refine ⟨{i}, Finset.singleton_nonempty i, hsub, ?_⟩
  intro x hx y hy hyNot
  have hxEq : x = i := by simpa using hx
  subst x
  have hyNe : y ≠ i := by simpa using hyNot
  have hpair : T.intersection i y = 0 := h i hi y hy (Ne.symm hyNe)
  exact hpair

/-- Two meeting minus-two indices of a numerical type with more than two
components have intersection number the larger of their two weights. -/
public lemma intersection_eq_max_weight_of_intersects (T : NumericalType)
    (hcount : 2 < T.componentCount) (i j : Fin T.componentCount)
    (hi : IsMinusTwoIndex T i) (hj : IsMinusTwoIndex T j)
    (hij : 0 < T.intersection i j) :
    T.intersection i j = max (T.weight i) (T.weight j) := by
  rcases isTwoVertexConfiguration_or_swap T hcount i j hi hj hij with h | h
  · rcases h with h | h | h
    · rcases h with ⟨w, hiw, hjw, _, hcross, _, _, _⟩
      rw [hiw, hjw, hcross]
      simp
    · rcases h with ⟨w, hiw, hjw, _, hcross, _, _, _⟩
      have hw : 0 < w := by rw [← hiw]; exact T.weight_pos i
      rw [hiw, hjw, hcross, max_eq_right]
      omega
    · rcases h with ⟨w, hiw, hjw, _, hcross, _, _, _⟩
      have hw : 0 < w := by rw [← hiw]; exact T.weight_pos i
      rw [hiw, hjw, hcross, max_eq_right]
      omega
  · rcases h with h | h | h
    · rcases h with ⟨w, hjw, hiw, _, hcross, _, _, _⟩
      rw [T.intersection_symm, hiw, hjw, hcross]
      simp
    · rcases h with ⟨w, hjw, hiw, _, hcross, _, _, _⟩
      have hw : 0 < w := by rw [← hjw]; exact T.weight_pos j
      rw [T.intersection_symm, hiw, hjw, hcross, max_eq_left]
      omega
    · rcases h with ⟨w, hjw, hiw, _, hcross, _, _, _⟩
      have hw : 0 < w := by rw [← hjw]; exact T.weight_pos j
      rw [T.intersection_symm, hiw, hjw, hcross, max_eq_left]
      omega

private lemma at_most_three_neighbors (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hproper : I.card < T.componentCount)
    (hminus : ∀ j ∈ I, IsMinusTwoIndex T j)
    (i : Fin T.componentCount) (hi : i ∈ I)
    (S : Finset (Fin T.componentCount)) (hS : S ⊆ I) (hnot : i ∉ S)
    (hedge : ∀ j ∈ S, T.intersection i j ≠ 0) : S.card ≤ 3 := by
  classical
  by_contra hlarge
  have hfour : 3 < S.card := by omega
  obtain ⟨j, k, l, m, hjS, hkS, hlS, hmS, hjk, hjl, hjm, hkl, hkm, hlm⟩ :=
    Finset.three_lt_card_iff.mp hfour
  have hji : j ≠ i := by intro h; subst j; exact hnot hjS
  have hki : k ≠ i := by intro h; subst k; exact hnot hkS
  have hli : l ≠ i := by intro h; subst l; exact hnot hlS
  have hmi : m ≠ i := by intro h; subst m; exact hnot hmS
  have hcount : 5 < T.componentCount := by
    have hcard : 5 ≤ I.card := by
      have hsub : insert i S ⊆ I := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · exact hS hx
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at hc
      omega
    omega
  apply (not_exists_fourfold_of_five_lt_componentCount T hcount)
  refine ⟨![i, j, k, l, m], ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro r
    fin_cases r
    · exact hminus i hi
    · exact hminus j (hS hjS)
    · exact hminus k (hS hkS)
    · exact hminus l (hS hlS)
    · exact hminus m (hS hmS)
  · intro r hr
    fin_cases r
    · contradiction
    · exact lt_of_le_of_ne (T.intersection_nonneg i j hji.symm)
        (Ne.symm (hedge j hjS))
    · exact lt_of_le_of_ne (T.intersection_nonneg i k hki.symm)
        (Ne.symm (hedge k hkS))
    · exact lt_of_le_of_ne (T.intersection_nonneg i l hli.symm)
        (Ne.symm (hedge l hlS))
    · exact lt_of_le_of_ne (T.intersection_nonneg i m hmi.symm)
        (Ne.symm (hedge m hmS))

private lemma minusTwoGraph_degree_le_three (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hproper : I.card < T.componentCount)
    (hminus : ∀ j ∈ I, IsMinusTwoIndex T j) (x : {i // i ∈ I})
    [Fintype ((minusTwoGraph T I).neighborSet x)] :
    (minusTwoGraph T I).degree x ≤ 3 := by
  classical
  let : Fintype {i // i ∈ I} := Fintype.ofFinite _
  let S : Finset (Fin T.componentCount) := I.filter fun j =>
    j ≠ x.val ∧ T.intersection x.val j ≠ 0
  have hSsub : S ⊆ I := Finset.filter_subset _ _
  have hxnot : x.val ∉ S := by simp [S]
  have hedge : ∀ j ∈ S, T.intersection x.val j ≠ 0 := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2.2
  have hScard := at_most_three_neighbors T I hproper hminus x.val x.property
    S hSsub hxnot hedge
  let f : ↥((minusTwoGraph T I).neighborSet x) → {j // j ∈ S} := fun y =>
    ⟨y.val.val, by
      apply Finset.mem_filter.mpr
      refine ⟨y.val.property, ?_⟩
      have hadj : (minusTwoGraph T I).Adj x y.val :=
        (minusTwoGraph T I).mem_neighborSet x y.val |>.mp y.property
      change x.val ≠ y.val.val ∧ T.intersection x.val y.val.val ≠ 0 at hadj
      exact ⟨hadj.1.symm, hadj.2⟩⟩
  have hf : Function.Injective f := by
    intro y z hyz
    exact Subtype.ext (Subtype.ext (congrArg (fun q : {j // j ∈ S} => q.val) hyz))
  have hdegree : (minusTwoGraph T I).degree x ≤ S.card := by
    rw [← (minusTwoGraph T I).card_neighborSet_eq_degree x]
    simpa using Fintype.card_le_of_injective f hf
  exact hdegree.trans hScard

end AlgebraicGeometry.NumericalType
