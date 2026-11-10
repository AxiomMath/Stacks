module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.IncidenceGraph
import all StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification.IncidenceGraph
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.DoubleTriple
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.AffineE6

/-!
# The incidence graph of a set of minus-two indices is a tree

The incidence graph of a connected proper set of minus-two indices is a tree of
maximum degree three with at most one trivalent vertex: two trivalent vertices
are excluded because they would produce the affine diagram `D̃`. When every
vertex has degree at most two, the set can be listed as a chain.

## Main results

* `AlgebraicGeometry.NumericalType.no_two_trivalent_vertices`: there is at most
  one trivalent vertex.
* `AlgebraicGeometry.NumericalType.exists_spanning_chain_of_degree_le_two`: a connected set of
  components each meeting at most two others can be listed as a chain.
* `AlgebraicGeometry.NumericalType.minusTwoGraph_isTree`: the incidence graph is a tree.

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

private lemma minusTwoGraph_neighbor_ncard_le_three (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hproper : I.card < T.componentCount)
    (hminus : ∀ j ∈ I, IsMinusTwoIndex T j) (x : {i // i ∈ I}) :
    ((minusTwoGraph T I).neighborSet x).ncard ≤ 3 := by
  classical
  let : Fintype {i // i ∈ I} := Fintype.ofFinite _
  let : Fintype ((minusTwoGraph T I).neighborSet x) := Fintype.ofFinite _
  have hdeg := minusTwoGraph_degree_le_three T I hproper hminus x
  rw [← SimpleGraph.card_neighborSet_eq_degree] at hdeg
  simpa only [Set.fintypeCard_eq_ncard] using hdeg

private lemma exists_trivalent_vertex_of_not_degree_le_two (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hproper : I.card < T.componentCount)
    (hminus : ∀ j ∈ I, IsMinusTwoIndex T j)
    (hnot : ¬ ∀ x : {i // i ∈ I},
      ((minusTwoGraph T I).neighborSet x).ncard ≤ 2) :
    ∃ x a b c : {i // i ∈ I}, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (minusTwoGraph T I).Adj x a ∧ (minusTwoGraph T I).Adj x b ∧
      (minusTwoGraph T I).Adj x c := by
  classical
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  have hle := minusTwoGraph_neighbor_ncard_le_three T I hproper hminus x
  have hcard : ((minusTwoGraph T I).neighborSet x).ncard = 3 := by omega
  have hfinite := Set.toFinite ((minusTwoGraph T I).neighborSet x)
  rw [Set.ncard_eq_toFinset_card _ hfinite] at hcard
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hcard
  have hadj (s) (hs : s ∈ ({a, b, c} : Finset {i // i ∈ I})) : (minusTwoGraph T I).Adj x s := by
    rw [← hset, hfinite.mem_toFinset] at hs
    exact hs
  exact ⟨x, a, b, c, hab, hac, hbc, hadj a (by simp), hadj b (by simp), hadj c (by simp)⟩

private lemma no_three_neighbors_of_degree_le_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x : V, G.degree x ≤ 2) :
    ∀ (x a b c : V), a ≠ b → a ≠ c → b ≠ c →
      G.Adj x a → G.Adj x b → G.Adj x c → False := by
  classical
  intro x a b c hab hac hbc hxa hxb hxc
  let : Fintype (G.neighborSet x) := Subtype.fintype _
  let f : Fin 3 → G.neighborSet x := ![
    ⟨a, (G.mem_neighborSet x a).mpr hxa⟩,
    ⟨b, (G.mem_neighborSet x b).mpr hxb⟩,
    ⟨c, (G.mem_neighborSet x c).mpr hxc⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hcard := Fintype.card_le_of_injective f hf
  rw [G.card_neighborSet_eq_degree] at hcard
  have hcard' : 3 ≤ G.degree x := by simpa using hcard
  have hlt : 3 ≤ 2 := hcard'.trans (hdeg x)
  omega

/-- Cutting a walk at a vertex other than its start leaves a walk of positive length. -/
private lemma one_le_length_takeUntil {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {x z w : V} (p : G.Walk x z) (hw : w ∈ p.support) (hwx : w ≠ x) :
    1 ≤ (p.takeUntil w hw).length :=
  Nat.pos_of_ne_zero fun h => hwx ((p.takeUntil w hw).eq_of_length_eq_zero h).symm

private lemma paths_from_distinct_neighbors_disjoint {V : Type*}
    (G : SimpleGraph V) (hacyclic : G.IsAcyclic)
    (x y z : V) (p : G.Walk x y) (q : G.Walk x z)
    (hp : p.IsPath) (hq : q.IsPath) (hsnd : p.snd ≠ q.snd) :
    ∀ w, w ∈ p.support → w ∈ q.support → w = x := by
  classical
  intro w hwp hwq
  by_contra hwx
  let pp := p.takeUntil w hwp
  let qq := q.takeUntil w hwq
  have hpp : pp.IsPath := hp.takeUntil hwp
  have hqq : qq.IsPath := hq.takeUntil hwq
  have hppos : 1 ≤ pp.length := one_le_length_takeUntil p hwp hwx
  have heq : pp = qq := by
    have hpath := (hacyclic.subsingleton_path x w).elim ⟨pp, hpp⟩ ⟨qq, hqq⟩
    exact congrArg Subtype.val hpath
  have hfirst := congrArg (fun r : G.Walk x w => r.getVert 1) heq
  have hpfirst : pp.getVert 1 = p.getVert 1 := by
    dsimp [pp]
    rw [SimpleGraph.Walk.getVert_takeUntil hwp hppos]
  have hqfirst : qq.getVert 1 = q.getVert 1 := by
    dsimp [qq]
    rw [SimpleGraph.Walk.getVert_takeUntil hwq (one_le_length_takeUntil q hwq hwx)]
  apply hsnd
  calc
    p.snd = p.getVert 1 := by simp
    _ = pp.getVert 1 := hpfirst.symm
    _ = qq.getVert 1 := hfirst
    _ = q.getVert 1 := hqfirst

private lemma neighbor_not_mem_path_support {V : Type*}
    (G : SimpleGraph V) (hacyclic : G.IsAcyclic)
    {x y z : V} (hxy : G.Adj x y) (p : G.Walk x z) (hp : p.IsPath)
    (hfirst : y ≠ p.snd) : y ∉ p.support := by
  classical
  intro hy
  let q := p.takeUntil y hy
  have hq : q.IsPath := hp.takeUntil hy
  have hpos : 1 ≤ q.length := one_le_length_takeUntil p hy hxy.ne.symm
  have heq : q = hxy.toWalk := by
    have hpath := (hacyclic.subsingleton_path x y).elim ⟨q, hq⟩
      ⟨hxy.toWalk, hxy.isPath_toWalk⟩
    exact congrArg Subtype.val hpath
  have hfirstEq : q.getVert 1 = p.getVert 1 := by
    dsimp [q]
    rw [SimpleGraph.Walk.getVert_takeUntil hy hpos]
  apply hfirst
  calc
    y = (hxy.toWalk).snd := by simp
    _ = q.getVert 1 := by simp [heq]
    _ = p.getVert 1 := hfirstEq
    _ = p.snd := by simp

private lemma exists_two_other_neighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x u : V}
    (hdeg : G.degree x = 3) (hxu : G.Adj x u) :
    ∃ a b, G.Adj x a ∧ G.Adj x b ∧ a ≠ u ∧ b ≠ u ∧ a ≠ b := by
  classical
  obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp
    (show ((G.neighborFinset x).erase u).card = 2 by
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset x u).mpr hxu),
        G.card_neighborFinset_eq_degree, hdeg])
  have ha : a ∈ (G.neighborFinset x).erase u := by simp [hset]
  have hb : b ∈ (G.neighborFinset x).erase u := by simp [hset]
  simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at ha hb
  exact ⟨a, b, ha.2, hb.2, ha.1, hb.1, hab⟩

private lemma no_common_off_path_neighbor {V : Type*}
    (G : SimpleGraph V) (hacyclic : G.IsAcyclic)
    {x y a : V} (hxy : x ≠ y) (p : G.Walk x y) (hp : p.IsPath)
    (hxa : G.Adj x a) (ha : a ≠ p.snd) (hya : G.Adj y a) : False := by
  have hap : a ∉ p.support := neighbor_not_mem_path_support G hacyclic hxa p hp ha
  have hpos : 0 < p.length := Nat.pos_of_ne_zero fun h => hxy (p.eq_of_length_eq_zero h)
  have hq : (p.concat hya).IsPath := hp.concat (by intro h; exact hap h) hya
  have heq : p.concat hya = hxa.toWalk := by
    have hpath := (hacyclic.subsingleton_path x a).elim
      ⟨p.concat hya, hq⟩ ⟨hxa.toWalk, hxa.isPath_toWalk⟩
    exact congrArg Subtype.val hpath
  have hfirst : (p.concat hya).getVert 1 = p.snd := by
    rw [SimpleGraph.Walk.concat_eq_append, SimpleGraph.Walk.getVert_append']
    rw [ite_eq_left (show 1 ≤ p.length by omega)]
  have hlast : hxa.toWalk.getVert 1 = a := by simp
  have hsnd := congrArg (fun r : G.Walk x a => r.getVert 1) heq
  exact ha (hfirst.symm.trans (hsnd.trans hlast)).symm

private lemma no_two_trivalent_vertices (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hproper : I.card < T.componentCount)
    (hminus : ∀ i ∈ I, IsMinusTwoIndex T i)
    (x y : {i // i ∈ I}) (hxy : x ≠ y)
    [Fintype ((minusTwoGraph T I).neighborSet x)]
    [Fintype ((minusTwoGraph T I).neighborSet y)]
    (hxdeg : (minusTwoGraph T I).degree x = 3)
    (hydeg : (minusTwoGraph T I).degree y = 3)
    (hTree : (minusTwoGraph T I).IsTree) : False := by
  classical
  let G := minusTwoGraph T I
  let : Fintype {i // i ∈ I} := Fintype.ofFinite _
  obtain ⟨p, hp, _⟩ := hTree.connected.exists_path_of_dist x y
  have hlen : 0 < p.length := Nat.pos_of_ne_zero fun h => hxy (p.eq_of_length_eq_zero h)
  have hpx : G.Adj x p.snd := by
    simpa using p.adj_getVert_succ (i := 0) hlen
  have hpy : G.Adj y p.reverse.snd := by
    simpa using p.reverse.adj_getVert_succ (i := 0) (by simpa using hlen)
  obtain ⟨a, c, hxa, hxc, haFirst, hcFirst, hac⟩ :=
    exists_two_other_neighbors G (x := x) (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        Fintype.card_eq_nat_card] using hxdeg) hpx
  obtain ⟨b, d, hyb, hyd, hbFirst, hdFirst, hbd⟩ :=
    exists_two_other_neighbors G (x := y) (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        Fintype.card_eq_nat_card] using hydeg) hpy
  have hrevPath : ∀ {s}, G.Adj y s → s ≠ p.reverse.snd → s ∉ p.support := fun hys hs => by
    simpa using neighbor_not_mem_path_support G hTree.isAcyclic hys p.reverse hp.reverse hs
  have haPath := neighbor_not_mem_path_support G hTree.isAcyclic hxa p hp haFirst
  have hcPath := neighbor_not_mem_path_support G hTree.isAcyclic hxc p hp hcFirst
  have hbPath := hrevPath hyb hbFirst
  have hdPath := hrevPath hyd hdFirst
  have hne : ∀ {s t}, G.Adj x s → s ≠ p.snd → G.Adj y t → s ≠ t := by
    rintro s t hxs hs hyt rfl
    exact no_common_off_path_neighbor G hTree.isAcyclic hxy p hp hxs hs hyt
  have hab := hne hxa haFirst hyb
  have had := hne hxa haFirst hyd
  have hcb := hne hxc hcFirst hyb
  have hcd := hne hxc hcFirst hyd
  let tail : G.Walk x b := p.concat hyb
  have htail : tail.IsPath := hp.concat hbPath hyb
  have haTail : a ∉ tail.support := by
    rw [SimpleGraph.Walk.support_concat]
    simp [haPath, hab]
  let q : G.Walk a b := SimpleGraph.Walk.cons hxa.symm tail
  have hq : q.IsPath := (SimpleGraph.Walk.cons_isPath_iff hxa.symm tail).mpr ⟨htail, haTail⟩
  have hqSupport : q.support = a :: (p.support ++ [b]) := by
    simp [q, tail, SimpleGraph.Walk.support_concat]
  have hcQ : c ∉ q.support := by
    rw [hqSupport]
    simp [hcPath, hac.symm, hcb]
  have hdQ : d ∉ q.support := by
    rw [hqSupport]
    simp [hdPath, had.symm, hbd.symm]
  have hqlen : q.length = p.length + 2 := by simp [q, tail]
  let t : ℕ := p.length + 3
  let g : ℕ → {i // i ∈ I} := fun n =>
    if n = 0 then c else if n = t + 1 then d else q.getVert (n - 1)
  let idx : ℕ → Fin T.componentCount := fun n => (g n).val
  have hidxI : ∀ n, idx n ∈ I := fun n => (g n).property
  have hinj : Set.InjOn idx (Set.Iio (t + 2)) := by
    intro m hm n hn hEq
    have hm' : m < t + 2 := hm
    have hn' : n < t + 2 := hn
    have hEq' : g m = g n := Subtype.ext hEq
    have tri (n : ℕ) : n = 0 ∨ n = t + 1 ∨ (n ≠ 0 ∧ n ≠ t + 1) := by omega
    have e0 : g 0 = c := by simp [g]
    have e1 : g (t + 1) = d := by simp [g]
    have hmid (n : ℕ) (h0 : n ≠ 0) (ht : n ≠ t + 1) : g n ≠ c ∧ g n ≠ d := by
      have hmem := q.getVert_mem_support (n - 1)
      rw [← show g n = q.getVert (n - 1) by simp [g, h0, ht]] at hmem
      exact ⟨fun h => hcQ (h ▸ hmem), fun h => hdQ (h ▸ hmem)⟩
    rcases tri m with rfl | rfl | ⟨hm0, hmt⟩ <;> rcases tri n with rfl | rfl | ⟨hn0, hnt⟩
    · rfl
    · exact (hcd (e0.symm.trans (hEq'.trans e1))).elim
    · exact ((hmid n hn0 hnt).1 (hEq'.symm.trans e0)).elim
    · exact (hcd (e0.symm.trans (hEq'.symm.trans e1))).elim
    · rfl
    · exact ((hmid n hn0 hnt).2 (hEq'.symm.trans e1)).elim
    · exact ((hmid m hm0 hmt).1 (hEq'.trans e0)).elim
    · exact ((hmid m hm0 hmt).2 (hEq'.trans e1)).elim
    · have hverts : q.getVert (m - 1) = q.getVert (n - 1) := by
        simpa [g, hm0, hmt, hn0, hnt] using hEq'
      have hmn := hq.getVert_injOn (by simp; dsimp [t] at *; omega)
        (by simp; dsimp [t] at *; omega) hverts
      omega
  have hcard : t + 2 ≤ I.card := by
    let f : Fin (t + 2) → {i // i ∈ I} := fun n => g n
    have hf : Function.Injective f := fun m n h =>
      Fin.ext (hinj (by simp) (by simp) (congrArg Subtype.val h))
    have hc := Fintype.card_le_of_injective f hf
    simpa [Fintype.card_coe] using hc
  have htproper : t + 2 < T.componentCount := hcard.trans_lt hproper
  have hminusIdx : ∀ n, n < t + 2 → IsMinusTwoIndex T (idx n) := by
    intro n hn
    exact hminus (idx n) (hidxI n)
  have hchain : ∀ j, 1 ≤ j → j ≤ t - 1 →
      T.intersection (idx j) (idx (j + 1)) ≠ 0 := by
    intro j hjlo hjhi
    have hjx : j ≠ 0 := by omega
    have hjend : j ≠ t + 1 := by omega
    have hnext0 : j + 1 ≠ 0 := by omega
    have hnextend : j + 1 ≠ t + 1 := by omega
    have hadj : G.Adj (q.getVert (j - 1)) (q.getVert j) := by
      have h := q.adj_getVert_succ (i := j - 1) (by dsimp [t] at *; omega)
      simpa [Nat.sub_add_cancel hjlo] using h
    have hjt : j ≠ t := by omega
    simpa [idx, g, hjx, hjend, hnext0, hnextend, hjt] using hadj.2
  have hedgeLeft : T.intersection (idx 0) (idx 2) ≠ 0 := by
    have hq1 : q.getVert 1 = x := by simp [q, tail]
    have h2 : idx 2 = x.val := by simp [idx, g, t, hq1]
    have h0 : idx 0 = c.val := by simp [idx, g]
    rw [h2, h0, T.intersection_symm]
    exact hxc.2
  have hyq : q.getVert (t - 2) = y := by
    have htval : t - 2 = p.length + 1 := by dsimp [t]; omega
    rw [htval]
    simp [q, tail, SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.concat_eq_append, SimpleGraph.Walk.getVert_append']
  have hedgeRight : T.intersection (idx (t - 1)) (idx (t + 1)) ≠ 0 := by
    have h1 : t - 1 ≠ 0 := by dsimp [t]; omega
    have h2 : t - 1 ≠ t + 1 := by omega
    have h3 : t - 1 - 1 = t - 2 := by omega
    simpa [idx, g, h1, h2, h3, hyq] using hyd.2
  apply not_exists_double_triple_subgraph T t (by dsimp [t]; omega) htproper
  have pos {m n : ℕ} (hm : m < t + 2) (hn : n < t + 2) (hmn : m ≠ n)
      (he : T.intersection (idx m) (idx n) ≠ 0) :
      0 < T.intersection (idx m) (idx n) :=
    lt_of_le_of_ne (T.intersection_nonneg _ _ (fun h => hmn (hinj hm hn h))) he.symm
  refine ⟨idx, hinj, hminusIdx, ?_, ?_, ?_⟩
  · intro j hjlo hjhi
    exact pos (by omega) (by omega) (by omega) (hchain j hjlo hjhi)
  · exact pos (by dsimp [t]; omega) (by dsimp [t]; omega) (by omega) hedgeLeft
  · exact pos (by omega) (by omega) (by omega) hedgeRight

private lemma one_of_three_neighbors_is_leaf (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hproper : I.card < T.componentCount)
    (hminus : ∀ j ∈ I, IsMinusTwoIndex T j)
    (x a b c : {i // i ∈ I})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxa : (minusTwoGraph T I).Adj x a)
    (hxb : (minusTwoGraph T I).Adj x b)
    (hxc : (minusTwoGraph T I).Adj x c)
    [Fintype ((minusTwoGraph T I).neighborSet a)]
    [Fintype ((minusTwoGraph T I).neighborSet b)]
    [Fintype ((minusTwoGraph T I).neighborSet c)]
    (hTree : (minusTwoGraph T I).IsTree) :
    (minusTwoGraph T I).degree a = 1 ∨
    (minusTwoGraph T I).degree b = 1 ∨
    (minusTwoGraph T I).degree c = 1 := by
  classical
  let G := minusTwoGraph T I
  have extra (u v : {i // i ∈ I}) [Fintype (G.neighborSet v)]
      (huv : G.Adj u v) (hv : G.degree v ≠ 1) :
      ∃ z, G.Adj v z ∧ z ≠ u := by
    have hcard : 2 ≤ Fintype.card (G.neighborSet v) := by
      rw [G.card_neighborSet_eq_degree]
      have : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩
      omega
    have hnot : ¬ ∀ z : G.neighborSet v, z.val = u := by
      intro hall
      have hle : Fintype.card (G.neighborSet v) ≤ 1 :=
        Fintype.card_le_one_iff.mpr fun z₁ z₂ => Subtype.ext ((hall z₁).trans (hall z₂).symm)
      omega
    obtain ⟨z, hz⟩ := Classical.not_forall.mp hnot
    exact ⟨z.val, z.property, hz⟩
  /- Two paths `x - s - d` and `x - s' - d'` through distinct neighbours `s ≠ s'` of `x`
  share no vertex other than `x`. -/
  have key (s d s' d' : {i // i ∈ I}) (hxs : G.Adj x s) (hsd : G.Adj s d) (hdx : d ≠ x)
      (hxs' : G.Adj x s') (hsd' : G.Adj s' d') (hdx' : d' ≠ x) (hss : s ≠ s') :
      d ≠ s' ∧ d ≠ d' ∧ s ≠ d' := by
    have hpath (s d : {i // i ∈ I}) (hxs : G.Adj x s) (hsd : G.Adj s d) (hdx : d ≠ x) :
        (SimpleGraph.Walk.cons hxs hsd.toWalk).IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false, not_or]
      exact ⟨hsd.isPath_toWalk, hxs.ne, hdx.symm⟩
    have hdis := paths_from_distinct_neighbors_disjoint G hTree.isAcyclic x d d'
      _ _ (hpath s d hxs hsd hdx) (hpath s' d' hxs' hsd' hdx') (by simpa using hss)
    refine ⟨fun h => hdx ?_, fun h => hdx ?_, fun h => hxs.ne.symm ?_⟩
    · exact hdis d (by simp) (by simp [h])
    · exact hdis d (by simp) (by simp [h])
    · exact hdis s (by simp) (by simp [h])
  by_contra hleaf
  push Not at hleaf
  obtain ⟨d, had, hdx⟩ := extra x a hxa hleaf.1
  obtain ⟨e, hbe, hey⟩ := extra x b hxb hleaf.2.1
  obtain ⟨f, hcf, hfz⟩ := extra x c hxc hleaf.2.2
  obtain ⟨hdb, hde, hae⟩ := key a d b e hxa had hdx hxb hbe hey hab
  obtain ⟨hdc, hdf, haf⟩ := key a d c f hxa had hdx hxc hcf hfz hac
  obtain ⟨hec, hef, hbf⟩ := key b e c f hxb hbe hey hxc hcf hfz hbc
  have hda : d ≠ a := had.ne.symm
  have heb : e ≠ b := hbe.ne.symm
  have hfc : f ≠ c := hcf.ne.symm
  have hax : a ≠ x := fun h => hxa.1 (congrArg Subtype.val h).symm
  have hxb' : x ≠ b := fun h => hxb.1 (congrArg Subtype.val h)
  have hxc' : x ≠ c := fun h => hxc.1 (congrArg Subtype.val h)
  have hxe : x ≠ e := hey.symm
  have hxf : x ≠ f := hfz.symm
  let sevenI : List {i // i ∈ I} := [d, a, x, e, b, f, c]
  have hnodupI : sevenI.Nodup := by
    simp_all [sevenI, List.nodup_cons, eq_comm]
  have hpair : List.Pairwise (· ≠ ·) (sevenI.map Subtype.val) :=
    List.nodup_iff_pairwise_ne.mp (hnodupI.map Subtype.val_injective)
  have hIcard : 7 ≤ I.card := by
    have hlen := List.Nodup.length_le_card hnodupI
    calc
      7 = sevenI.length := by simp [sevenI]
      _ ≤ Fintype.card {i // i ∈ I} := hlen
      _ = I.card := Fintype.card_coe I
  have hn : 7 < T.componentCount := by omega
  apply not_exists_seven_minusTwoIndices_with_affineE6_edges T hn
  exact ⟨d.val, a.val, x.val, e.val, b.val, f.val, c.val, hpair,
    hminus _ d.2, hminus _ a.2, hminus _ x.2, hminus _ e.2, hminus _ b.2, hminus _ f.2,
    hminus _ c.2, had.symm.2, hxa.symm.2, hbe.symm.2, hxb.symm.2, hcf.symm.2, hxc.symm.2⟩

private lemma exists_adj_across_of_connected {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected) (S : Finset V)
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  classical
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ : ∃ y, y ∉ S := by
    by_contra h
    push Not at h
    exact hproper (Finset.eq_univ_iff_forall.mpr h)
  have hr : G.Reachable x y := hconn x y
  rcases hr with ⟨p⟩
  induction p with
  | nil => exact (hy hx).elim
  | @cons a b c hab p ih =>
      by_cases hb : b ∈ S
      · exact ih hb hy
      · exact ⟨a, hx, b, hb, hab⟩

private lemma maximal_path_spans_of_degree_le_two {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (u v : V) (p : G.Walk u v) (hp : p.IsPath)
    (_hlen : 0 < p.length)
    (hmax : ∀ (u' v' : V) (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length)
    (hno3 : ∀ (x a b c : V), a ≠ b → a ≠ c → b ≠ c →
      G.Adj x a → G.Adj x b → G.Adj x c → False) :
    p.support.toFinset = Finset.univ := by
  classical
  by_contra hne
  have hnonempty : p.support.toFinset.Nonempty := by
    refine ⟨u, ?_⟩
    simp
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    exists_adj_across_of_connected G hconn p.support.toFinset hnonempty hne
  have hx' : x ∈ p.support := by simpa using hx
  obtain ⟨k, hkx, hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx'
  by_cases hk0 : k = 0
  · have hu : u = x := by simpa [hk0] using hkx
    have hyu : G.Adj y u := by simpa [hu] using hxy.symm
    have hwalk : (SimpleGraph.Walk.cons hyu p).IsPath :=
      (SimpleGraph.Walk.cons_isPath_iff hyu p).mpr ⟨hp, by
        intro hyu'
        apply hy
        simpa using hyu'⟩
    have hlen' : (SimpleGraph.Walk.cons hyu p).length = p.length + 1 := by simp
    have := hmax y v (SimpleGraph.Walk.cons hyu p) hwalk
    omega
  · by_cases hkend : k = p.length
    · have hvx : v = x := by simpa [hkend] using hkx
      have hxy' : G.Adj v y := by simpa [hvx] using hxy
      have hwalk : (p.concat hxy').IsPath :=
        hp.concat (by
          intro hyx
          apply hy
          simpa using hyx) hxy'
      have hlen' : (p.concat hxy').length = p.length + 1 :=
        SimpleGraph.Walk.length_concat p hxy'
      have := hmax u y (p.concat hxy') hwalk
      omega
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hklt : k < p.length := Nat.lt_of_le_of_ne hk hkend
      let a := p.getVert (k - 1)
      let b := p.getVert (k + 1)
      have haAdj : G.Adj x a := by
        have hh := p.adj_getVert_succ (i := k - 1) (by omega)
        have hidx : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
        rw [hidx, hkx] at hh
        exact hh.symm
      have hbAdj : G.Adj x b := by
        have hh := p.adj_getVert_succ (i := k) (by omega)
        rw [hkx] at hh
        exact hh
      have hab : a ≠ b := by
        intro hab
        have hindices := hp.getVert_injOn (by simp; omega) (by simp; omega) hab
        have hne : k - 1 ≠ k + 1 := by omega
        exact hne hindices
      have hay : a ≠ y := by
        intro h
        apply hy
        simpa [h, a] using p.getVert_mem_support (k - 1)
      have hby : b ≠ y := by
        intro h
        apply hy
        simpa [h, b] using p.getVert_mem_support (k + 1)
      exact hno3 x a b y hab hay hby haAdj hbAdj hxy

private lemma exists_neighbor_of_connected (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hcard : 2 ≤ I.card)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0))
    (i : Fin T.componentCount) (hi : i ∈ I) :
    ∃ j ∈ I, j ≠ i ∧ T.intersection i j ≠ 0 := by
  by_contra h
  push Not at h
  have hsub : ({i} : Finset (Fin T.componentCount)) ⊂ I := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · exact Finset.singleton_subset_iff.mpr hi
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
  exact h y hy hyNe

private lemma minusTwoGraph_spanning_path (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hcard : 2 ≤ I.card)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0))
    (hno3 : ∀ (x a b c : {i // i ∈ I}), a ≠ b → a ≠ c → b ≠ c →
      (minusTwoGraph T I).Adj x a → (minusTwoGraph T I).Adj x b →
      (minusTwoGraph T I).Adj x c → False) :
    ∃ (u v : {i // i ∈ I}) (p : (minusTwoGraph T I).Walk u v),
      p.IsPath ∧ p.length + 1 = I.card ∧ ∀ x, x ∈ p.support := by
  classical
  let : Fintype {i // i ∈ I} := Fintype.ofFinite _
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
  let x : {i // i ∈ I} := ⟨i, hi⟩
  let : Nonempty {i // i ∈ I} := ⟨x⟩
  let : Fintype (minusTwoGraph T I).edgeSet := Fintype.ofFinite _
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length (minusTwoGraph T I)
  obtain ⟨j, hj, hji, he⟩ :=
    exists_neighbor_of_connected T I hcard hconnected i hi
  let y : {i // i ∈ I} := ⟨j, hj⟩
  have hxy : (minusTwoGraph T I).Adj x y := by
    change i ≠ j ∧ T.intersection i j ≠ 0
    exact ⟨hji.symm, he⟩
  let q := hxy.toWalk
  have hq : q.IsPath := hxy.isPath_toWalk
  have hpos : 0 < p.length := by
    have hle := hmax x y q hq
    simp [q] at hle
    omega
  have hconn : (minusTwoGraph T I).Connected :=
    minusTwoGraph_connected T I (by omega) hconnected
  have hsupport := maximal_path_spans_of_degree_le_two
    (minusTwoGraph T I) hconn u v p hp hpos hmax hno3
  have hcardSupport : p.length + 1 = I.card := by
    have h := congrArg Finset.card hsupport
    have h' : p.support.toFinset.card = I.card := by
      simpa [Fintype.card_coe] using h
    rw [List.toFinset_card_of_nodup hp.support_nodup,
      SimpleGraph.Walk.length_support] at h'
    exact h'
  exact ⟨u, v, p, hp, hcardSupport, fun z => by
    have hz : z ∈ p.support.toFinset := by rw [hsupport]; simp
    simpa using hz⟩

private lemma fin_ordering_of_spanning_walk (T : NumericalType)
    (I : Finset (Fin T.componentCount))
    (u v : {i // i ∈ I}) (p : (minusTwoGraph T I).Walk u v)
    (hp : p.IsPath) (hlen : p.length + 1 = I.card)
    (hcover : ∀ x : {i // i ∈ I}, x ∈ p.support) :
    ∃ f : Fin I.card → {i // i ∈ I}, Function.Injective f ∧
      Set.range f = Set.univ ∧
      (∀ r s, s.val = r.val + 1 → (minusTwoGraph T I).Adj (f r) (f s)) := by
  classical
  let f : Fin I.card → {i // i ∈ I} := fun r => p.getVert r.val
  have hinj : Function.Injective f := by
    intro r s hrs
    apply Fin.ext
    exact hp.getVert_injOn (by simp; omega) (by simp; omega) hrs
  have hrange : Set.range f = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨n, ⟨hn, hnle⟩⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover x)
    refine ⟨⟨n, ?_⟩, ?_⟩
    · rw [← hlen]
      omega
    · simpa [f] using hn
  refine ⟨f, hinj, hrange, ?_⟩
  intro r s hrs
  change (minusTwoGraph T I).Adj (p.getVert r.val) (p.getVert s.val)
  rw [hrs]
  apply p.adj_getVert_succ
  have hslt : r.val + 1 < I.card := by rw [← hrs]; exact s.isLt
  omega

/-- A connected set of components each meeting at most two others can be listed
as a chain: an injective ordering of the set whose consecutive entries meet. -/
public lemma exists_spanning_chain_of_degree_le_two (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hcard : 2 ≤ I.card)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0))
    (hdegree : ∀ x : {i // i ∈ I},
      ((minusTwoGraph T I).neighborSet x).ncard ≤ 2) :
    ∃ v : Fin I.card → Fin T.componentCount,
      Function.Injective v ∧ Set.range v = (I : Set (Fin T.componentCount)) ∧
      (∀ r s, s.val = r.val + 1 → T.intersection (v r) (v s) ≠ 0) := by
  classical
  let : Fintype {i // i ∈ I} := Fintype.ofFinite _
  have hdeg : ∀ x : {i // i ∈ I}, (minusTwoGraph T I).degree x ≤ 2 := by
    intro x
    let : Fintype ((minusTwoGraph T I).neighborSet x) := Fintype.ofFinite _
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    simpa only [Set.fintypeCard_eq_ncard] using hdegree x
  have hno3 : ∀ (x a b c : {i // i ∈ I}), a ≠ b → a ≠ c → b ≠ c →
      (minusTwoGraph T I).Adj x a → (minusTwoGraph T I).Adj x b →
      (minusTwoGraph T I).Adj x c → False := by
    intro x a b c hab hac hbc hxa hxb hxc
    let : Fintype ((minusTwoGraph T I).neighborSet x) := Fintype.ofFinite _
    exact no_three_neighbors_of_degree_le_two (minusTwoGraph T I) hdeg
      x a b c hab hac hbc hxa hxb hxc
  obtain ⟨u, w, p, hp, hlen, hcover⟩ :=
    minusTwoGraph_spanning_path T I hcard hconnected hno3
  obtain ⟨f, hf, hfrange, hfadj⟩ :=
    fin_ordering_of_spanning_walk T I u w p hp hlen hcover
  let v : Fin I.card → Fin T.componentCount := fun r => (f r).val
  have hv : Function.Injective v := by
    intro r s hrs
    exact hf (Subtype.ext hrs)
  have hvrange : Set.range v = (I : Set (Fin T.componentCount)) := by
    ext i
    constructor
    · rintro ⟨r, rfl⟩
      exact (f r).property
    · intro hi
      have hx : (⟨i, hi⟩ : {i // i ∈ I}) ∈ Set.range f := by
        rw [hfrange]
        simp
      rcases hx with ⟨r, hr⟩
      exact ⟨r, congrArg Subtype.val hr⟩
  refine ⟨v, hv, hvrange, ?_⟩
  intro r s hrs
  have hadj := hfadj r s hrs
  change (f r).val ≠ (f s).val ∧ T.intersection (f r).val (f s).val ≠ 0 at hadj
  exact hadj.2

private lemma minusTwoGraph_isTree (T : NumericalType)
    (I : Finset (Fin T.componentCount)) (hcard : 5 ≤ I.card)
    (hproper : I.card < T.componentCount)
    (hminus : ∀ j ∈ I, IsMinusTwoIndex T j)
    (hconnected : ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ I ∧
        (∀ i ∈ J, ∀ j ∈ I, j ∉ J → T.intersection i j = 0)) :
    (minusTwoGraph T I).IsTree :=
  ⟨minusTwoGraph_connected T I (by omega) hconnected,
    minusTwoGraph_isAcyclic T I hcard hproper hminus⟩

end AlgebraicGeometry.NumericalType
