module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.BoundaryControl
import all StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.BoundaryControl
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.MinusTwoComponents
import all StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.UniformBound.MinusTwoComponents
public import StacksCore.Tactic.StacksAttribute

/-!
# Short boundary chains and the uniform bound

Distances inside a connected component of minus-two indices are taken along
paths in the induced `SimpleGraph`. A walk inside a component gives a boundary
chain no longer than the component, and the Dynkin diagram `E8` has diameter at
most seven, which bounds the length `k` of the boundary chains there.
Assembling the reductions gives the uniform bound.

## Main results

* `AlgebraicGeometry.NumericalType.multiplicity_mul_abs_intersection_le`: for a
  minimal numerical type of genus `g` at least two, every entry of the
  intersection matrix, multiplied by the multiplicity of its row, is bounded in
  absolute value by `768 * g`.

## References

* [Stacks Project, Tag 0C9W](https://stacks.math.columbia.edu/tag/0C9W)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

private def minusTwoComponentGraph (T : NumericalType) (i : Fin T.componentCount) :
    SimpleGraph (MinusTwoComponent T i) :=
  SimpleGraph.fromRel fun x y => MinusTwoEdge T (x : Fin T.componentCount)
    (y : Fin T.componentCount)

private theorem minusTwoEdge_of_componentAdj {T : NumericalType}
    {i : Fin T.componentCount} {x y : MinusTwoComponent T i}
    (h : (minusTwoComponentGraph T i).Adj x y) :
    MinusTwoEdge T (x : Fin T.componentCount) (y : Fin T.componentCount) := by
  rcases (SimpleGraph.fromRel_adj _ _ _).mp h with ⟨_, hedge | hedge⟩
  · exact hedge
  · exact minusTwoEdge_symm T hedge

private theorem componentAdj_of_minusTwoEdge {T : NumericalType}
    {i : Fin T.componentCount} {x y : MinusTwoComponent T i}
    (h : MinusTwoEdge T (x : Fin T.componentCount) (y : Fin T.componentCount)) :
    (minusTwoComponentGraph T i).Adj x y := by
  apply (SimpleGraph.fromRel_adj _ _ _).mpr
  refine ⟨?_, Or.inl h⟩
  intro heq
  have heqval : (x : Fin T.componentCount) = (y : Fin T.componentCount) :=
    congrArg Subtype.val heq
  rcases h.1 with ⟨_, hdiag⟩
  have hpos : 0 < T.intersection (x : Fin T.componentCount) (x : Fin T.componentCount) := by
    simpa [heqval] using h.2.2
  have hw := T.weight_pos (x : Fin T.componentCount)
  rw [hdiag] at hpos
  omega

private theorem minusTwoComponent_closed {T : NumericalType}
    {i x y : Fin T.componentCount} (hx : x ∈ MinusTwoComponent T i)
    (hedge : MinusTwoEdge T x y) : y ∈ MinusTwoComponent T i := by
  have hx' := (minusTwoComponent_mem_iff T i x).mp hx
  exact (minusTwoComponent_mem_iff T i y).mpr
    ⟨hedge.2.1, hx'.2.tail hedge⟩

private theorem minusTwoPath_mem {T : NumericalType}
    {i x y : Fin T.componentCount} (hx : x ∈ MinusTwoComponent T i)
    (h : Relation.ReflTransGen (MinusTwoEdge T) x y) :
    y ∈ MinusTwoComponent T i := by
  induction h with
  | refl => exact hx
  | @tail b c hpath hedge ih => exact minusTwoComponent_closed ih hedge

private theorem componentReachable_of_minusTwoPath {T : NumericalType}
    {i x y : Fin T.componentCount} (hx : x ∈ MinusTwoComponent T i)
    (hy : y ∈ MinusTwoComponent T i)
    (h : Relation.ReflTransGen (MinusTwoEdge T)
      x y) :
    (minusTwoComponentGraph T i).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  rw [(minusTwoComponentGraph T i).reachable_eq_reflTransGen]
  induction h generalizing hx with
  | refl => exact .refl
  | @tail b c hpath hedge ih =>
      exact (ih hx (minusTwoPath_mem hx hpath)).tail (componentAdj_of_minusTwoEdge hedge)

private theorem boundaryChain_of_walk_to_boundary {T : NumericalType}
    {i : Fin T.componentCount} {j : Fin T.componentCount}
    {b x : MinusTwoComponent T i} (hjb : 0 < T.intersection b j)
    (p : (minusTwoComponentGraph T i).Walk x b) :
    ∃ n, BoundaryChain T j (x : Fin T.componentCount) n ∧ n = p.length + 1 := by
  induction p with
  | nil =>
      rename_i u
      have hminus : IsMinusTwoIndex T (u : Fin T.componentCount) :=
        ((minusTwoComponent_mem_iff T i u).mp u.property).1
      exact ⟨1, BoundaryChain.start hminus (by rwa [T.intersection_symm]), by simp⟩
  | @cons u v w hadj p ih =>
      rcases ih hjb with ⟨n, hchain, hlen⟩
      have hedge := minusTwoEdge_symm T (minusTwoEdge_of_componentAdj hadj)
      refine ⟨n + 1, BoundaryChain.step hchain hedge.2.1 hedge.2.2, ?_⟩
      simp [hlen]

private theorem exists_short_boundary_chain {t : ℕ} (T : NumericalType)
    (i : Fin T.componentCount) (_hi : IsMinusTwoIndex T i)
    (v : Fin t → Fin T.componentCount) (hinj : Function.Injective v)
    (hrange : Set.range v = (MinusTwoComponent T i : Set _))
    (b : Fin T.componentCount) (hb : b ∈ MinusTwoComponent T i)
    (j : Fin T.componentCount) (hjb : 0 < T.intersection b j)
    (x : Fin T.componentCount) (hx : x ∈ MinusTwoComponent T i) :
    ∃ n, BoundaryChain T j x n ∧ n ≤ t := by
  classical
  let e : Fin t ≃ MinusTwoComponent T i := Equiv.ofBijective
    (fun a => ⟨v a, by
      have ha : v a ∈ Set.range v := ⟨a, rfl⟩
      rw [hrange] at ha
      exact ha⟩)
    ⟨fun a c hac => hinj (congrArg Subtype.val hac), fun y => by
      have hy : (y : Fin T.componentCount) ∈ Set.range v := by
        rw [hrange]
        exact y.property
      obtain ⟨a, ha⟩ := hy
      exact ⟨a, Subtype.ext ha⟩⟩
  have hcard : Fintype.card (MinusTwoComponent T i) = t := by
    simpa using (Fintype.card_congr e).symm
  obtain ⟨p, hp⟩ := (componentReachable_of_minusTwoPath hb hx
    ((reflTransGen_reverse_minusTwo T ((minusTwoComponent_mem_iff T i b).mp hb).2).trans
      ((minusTwoComponent_mem_iff T i x).mp hx).2)).exists_isPath
  have hlen : p.length < t := hcard ▸ hp.length_lt
  obtain ⟨n, hchain, hn⟩ := boundaryChain_of_walk_to_boundary hjb p.reverse
  exact ⟨n, hchain, by rw [hn, SimpleGraph.Walk.length_reverse]; omega⟩

private abbrev E8Graph : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel (DynkinShape.Edge .E8)

private theorem e8_forward_aux (n : ℕ) :
    ∀ a : Fin 8, a.val + n ≤ 6 →
      ∃ b : Fin 8, b.val = a.val + n ∧
        ∃ p : E8Graph.Walk a b, p.length = n := by
  induction n with
  | zero =>
      intro a ha
      exact ⟨a, by simp, SimpleGraph.Walk.nil, by simp⟩
  | succ n ih =>
      intro a ha
      obtain ⟨c, hc, p, hp⟩ := ih a (by omega)
      let b : Fin 8 := ⟨a.val + n + 1, by omega⟩
      have hcval : c.val = a.val + n := hc
      have hbval : b.val = a.val + n + 1 := rfl
      have hcb : E8Graph.Adj c b := by
        apply (SimpleGraph.fromRel_adj _ _ _).2
        refine ⟨?_, Or.inl ?_⟩
        · intro heq
          have hv := congrArg Fin.val heq
          rw [hcval, hbval] at hv
          omega
        · have hsucc : c.val + 1 = b.val := by rw [hcval, hbval]
          have hclt : c.val < 7 := by rw [hcval]; omega
          have hblt : b.val < 7 := by rw [hbval]; omega
          change ((c.val + 1 = b.val ∨ b.val + 1 = c.val) ∧
              c.val < 7 ∧ b.val < 7) ∨
            (c.val = 4 ∧ b.val = 7) ∨ (b.val = 4 ∧ c.val = 7)
          exact Or.inl ⟨Or.inl hsucc, hclt, hblt⟩
      exact ⟨b, hbval, p.concat hcb, by simp [SimpleGraph.Walk.length_concat, hp]⟩

private theorem e8_segment {a b : Fin 8}
    (hab : a.val ≤ b.val) (hb : b.val ≤ 6) :
    ∃ p : E8Graph.Walk a b, p.length = b.val - a.val := by
  let n := b.val - a.val
  obtain ⟨c, hc, p, hp⟩ := e8_forward_aux n a (by dsimp [n]; omega)
  have hcb : c = b := Fin.ext (by dsimp [n] at hc; omega)
  refine ⟨p.copy rfl hcb, ?_⟩
  simp [n, hp]

private theorem e8_edge_47 : E8Graph.Adj (4 : Fin 8) (7 : Fin 8) := by
  apply (SimpleGraph.fromRel_adj _ _ _).2
  refine ⟨by decide, Or.inl ?_⟩
  simp [DynkinShape.Edge]

private theorem e8_walk_to_center (a : Fin 8) :
    ∃ p : E8Graph.Walk a (4 : Fin 8), p.length ≤ 4 := by
  by_cases ha7 : a.val = 7
  · have hae : a = 7 := Fin.ext ha7
    subst a
    exact ⟨SimpleGraph.Walk.cons e8_edge_47.symm SimpleGraph.Walk.nil, by simp⟩
  · have ha6 : a.val ≤ 6 := by omega
    by_cases hle : a.val ≤ 4
    · obtain ⟨p, hp⟩ := e8_segment (a := a) (b := (4 : Fin 8)) hle (by norm_num)
      exact ⟨p, by omega⟩
    · have hge : 4 ≤ a.val := by omega
      obtain ⟨p, hp⟩ := e8_segment (a := (4 : Fin 8)) (b := a) hge ha6
      refine ⟨p.reverse, ?_⟩
      rw [SimpleGraph.Walk.length_reverse, hp]
      omega

private theorem e8_short_walk (a b : Fin 8) :
    ∃ p : E8Graph.Walk a b, p.length ≤ 6 := by
  by_cases ha7 : a.val = 7
  · by_cases hb7 : b.val = 7
    · have hae : a = 7 := Fin.ext ha7
      have hbe : b = 7 := Fin.ext hb7
      subst a
      subst b
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
    · have hbe6 : b.val ≤ 6 := by omega
      have hae : a = 7 := Fin.ext ha7
      subst a
      obtain ⟨p, hp⟩ := e8_walk_to_center b
      exact ⟨(SimpleGraph.Walk.cons e8_edge_47.symm .nil).append p.reverse, by simp; omega⟩
  · by_cases hb7 : b.val = 7
    · have hae6 : a.val ≤ 6 := by omega
      have hbe : b = 7 := Fin.ext hb7
      subst b
      obtain ⟨p, hp⟩ := e8_walk_to_center a
      exact ⟨p.append (SimpleGraph.Walk.cons e8_edge_47 .nil), by simp; omega⟩
    · have ha6 : a.val ≤ 6 := by omega
      have hb6 : b.val ≤ 6 := by omega
      by_cases hab : a.val ≤ b.val
      · obtain ⟨p, hp⟩ := e8_segment hab hb6
        exact ⟨p, by omega⟩
      · obtain ⟨p, hp⟩ := e8_segment (a := b) (b := a) (by omega) ha6
        refine ⟨p.reverse, ?_⟩
        rw [SimpleGraph.Walk.length_reverse, hp]
        omega

private def map_E8_walk {T : NumericalType} {i : Fin T.componentCount}
    (f : Fin 8 → MinusTwoComponent T i)
    (hmap : ∀ a b, E8Graph.Adj a b →
      (minusTwoComponentGraph T i).Adj (f a) (f b)) :
    E8Graph →g minusTwoComponentGraph T i :=
  ⟨f, by intro a b hab; exact hmap a b hab⟩

private theorem e8_boundary_chain {t : ℕ} {T : NumericalType}
    (i : Fin T.componentCount) (_hi : IsMinusTwoIndex T i)
    (ht : t = 8) (v : Fin t → Fin T.componentCount)
    (hinj : Function.Injective v)
    (hrange : Set.range v = (MinusTwoComponent T i : Set _))
    (w : ℤ) (hconfig : IsDynkinConfiguration T v .E8 w)
    (b x : Fin t) (j : Fin T.componentCount)
    (_hj : j ∉ MinusTwoComponent T i) (hjb : 0 < T.intersection (v b) j) :
    ∃ n, BoundaryChain T j (v x) n ∧ n ≤ 7 := by
  cases ht
  classical
  rcases hconfig with ⟨hd, hw, hweights, hinter, hineq⟩
  let f : Fin 8 → MinusTwoComponent T i := fun a => ⟨v a, by
    have ha : v a ∈ Set.range v := ⟨a, rfl⟩
    rw [hrange] at ha
    exact ha⟩
  have hedgemap (a c : Fin 8) (hac : E8Graph.Adj a c) :
      MinusTwoEdge T (v a) (v c) := by
    have hacne : a ≠ c := hac.1
    have hedge : DynkinShape.Edge .E8 a c := by
      rcases hac.2 with h | h
      · exact h
      · have hs : DynkinShape.Edge .E8 c a := h
        simp [DynkinShape.Edge] at hs ⊢
        omega
    have haI : v a ∈ MinusTwoComponent T i := (f a).property
    have hcI : v c ∈ MinusTwoComponent T i := (f c).property
    have haMinus := (minusTwoComponent_mem_iff T i (v a)).mp haI |>.1
    have hcMinus := (minusTwoComponent_mem_iff T i (v c)).mp hcI |>.1
    have hinter' : T.intersection (v a) (v c) = w := by
      simpa [hacne, hedge, DynkinShape.weightFactor] using hinter a c
    exact ⟨haMinus, hcMinus, by rwa [hinter']⟩
  have hgraphmap (a c : Fin 8) (hac : E8Graph.Adj a c) :
      (minusTwoComponentGraph T i).Adj (f a) (f c) :=
    componentAdj_of_minusTwoEdge (hedgemap a c hac)
  obtain ⟨p, hp⟩ := e8_short_walk b x
  let hom := map_E8_walk f hgraphmap
  let q := p.map hom
  have hjb' : 0 < T.intersection (hom b : Fin T.componentCount) j := by
    simpa [hom, map_E8_walk, f] using hjb
  obtain ⟨n, hchain, hlen⟩ := boundaryChain_of_walk_to_boundary hjb' q.reverse
  refine ⟨n, hchain, ?_⟩
  rw [hlen, SimpleGraph.Walk.length_reverse]
  have hmaplen : q.length = p.length := by simp [q, hom, map_E8_walk]
  omega

private lemma pair_bound_of_diagonal_bounds (T : NumericalType) (g : ℤ)
    (hg : 2 ≤ g)
    (hdiag : ∀ k : Fin T.componentCount,
      T.multiplicity k * |T.intersection k k| ≤ 768 * g)
    (i j : Fin T.componentCount) :
    T.multiplicity i * |T.intersection i j| ≤ 768 * g := by
  by_cases hij : i = j
  · subst j
    simpa using hdiag i
  · by_cases hpos : 0 < T.intersection i j
    · rw [abs_of_nonneg (T.intersection_nonneg i j hij)]
      exact (multiplicity_mul_intersection_le T i j hpos).trans (hdiag j)
    · have hzero : T.intersection i j = 0 := by
        have := T.intersection_nonneg i j hij
        omega
      rw [hzero, abs_zero, mul_zero]
      omega

/-- For a minimal numerical type of genus at least two, each multiplicity-weighted
absolute intersection is at most 768 times its genus. -/
@[stacks 0C9W]
public lemma multiplicity_mul_abs_intersection_le
    (T : NumericalType) (g : ℤ) (hg : 2 ≤ g) (hgenus : genus T = g)
    (hminimal : IsMinimal T) (i j : Fin T.componentCount) :
    T.multiplicity i * |T.intersection i j| ≤ 768 * g := by
  apply pair_bound_of_diagonal_bounds T g hg ?_ i j
  intro k
  by_cases hk : IsMinusTwoIndex T k
  · let I := MinusTwoComponent T k
    have hkI : k ∈ I := (minusTwoComponent_mem_iff T k k).mpr ⟨hk, .refl⟩
    obtain ⟨b, hbI, j, hj, hbj⟩ := minusTwoComponent_boundary_exists T g hg hgenus k hk
    have hjI : j ∉ I := fun hjmem => hj ((minusTwoComponent_mem_iff T k j).mp hjmem).1
    have hcountpos : 1 < T.componentCount := by
      have hne : j ≠ k := by
        rintro rfl
        exact hj hk
      have hvalse : j.val ≠ k.val := fun h => hne (Fin.ext h)
      omega
    by_cases hsingle : I.card = 1
    · have hbeq : b = k := (Finset.card_le_one.mp (show I.card ≤ 1 by omega) k hkI b hbI).symm
      subst b
      exact (minus_two_diagonal_bound_of_nonminus_neighbor T g hg hgenus hminimal
        hcountpos k j hk hj hbj).trans (by omega)
    · have hcard : 2 ≤ I.card := by
        have := Finset.card_pos.mpr ⟨k, hkI⟩
        omega
      have hstrict : I ⊂ Finset.univ := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
        intro heq
        exact hjI (by rw [heq]; simp)
      have hproper : I.card < T.componentCount := by
        simpa using Finset.card_lt_card hstrict
      obtain ⟨v, hinj, hrange, d, w, hconfig⟩ :=
        classify_minusTwoComponent T k hk hcard hproper
      obtain ⟨rk, hrk⟩ := (show k ∈ Set.range v by rw [hrange]; exact hkI)
      obtain ⟨rb, hrb⟩ := (show b ∈ Set.range v by rw [hrange]; exact hbI)
      have hboundary : BoundaryAt T I v rb := ⟨j, hjI, by simpa [hrb] using hbj⟩
      have hfacA : ∀ r : Fin I.card,
          1 ≤ DynkinShape.weightFactor .A r ∧
            DynkinShape.weightFactor .A r ≤ 2 := by
        intro r
        simp [DynkinShape.weightFactor]
      have hshort : I.card ≤ 7 → T.multiplicity k * |T.intersection k k| ≤ 768 * g := by
        intro h7
        obtain ⟨n, hpath, hn⟩ := exists_short_boundary_chain T k hk v hinj hrange
          b hbI j hbj k hkI
        exact diagonal_bound_of_short_boundary_chain T g hg hgenus hminimal
          hcountpos j k hj n ((by simpa using hn : n ≤ I.card).trans h7) hpath
      have hBC : ∀ d', (d' = .B ∨ d' = .C) → IsDynkinConfiguration T v d' w →
          T.multiplicity k * |T.intersection k k| ≤ 768 * g := by
        intro d' hd' hconfig'
        have h2 : 2 ≤ I.card := by rcases hd' with rfl | rfl <;> exact hconfig'.1
        by_cases hsmall : I.card = 2
        · exact hshort (by omega)
        · obtain ⟨r, hr, hmax⟩ := exists_BC_boundary_control T k hk v hinj hrange
            d' w hd' hconfig' (h2.lt_of_ne' hsmall)
          have hfac : ∀ s : Fin I.card,
              1 ≤ DynkinShape.weightFactor d' s ∧ DynkinShape.weightFactor d' s ≤ 2 := by
            intro s
            rcases hd' with rfl | rfl <;> simp [DynkinShape.weightFactor] <;> split_ifs <;> omega
          simpa [hrk] using (diagonal_bound_of_config_control T g hg hgenus hminimal hcountpos
            k hk v hinj hrange d' w hconfig' r hr hfac 2 (by norm_num) hmax rk)
      cases d with
      | A =>
          obtain ⟨r, hr, hmax⟩ := exists_A_boundary_max T k hk v hinj hrange w hconfig
          have hcontrol : ∀ s : Fin I.card,
              T.multiplicity (v s) ≤ 1 * T.multiplicity (v r) := by
            simpa using hmax
          simpa [hrk] using (diagonal_bound_of_config_control T g hg hgenus hminimal hcountpos
            k hk v hinj hrange .A w hconfig r hr hfacA 1 (by norm_num)
            hcontrol rk)
      | B => exact hBC .B (Or.inl rfl) hconfig
      | C => exact hBC .C (Or.inr rfl) hconfig
      | D =>
          obtain ⟨r, hr, hmax⟩ := exists_D_boundary_control T k hk v hinj hrange w hconfig
          have hfac : ∀ s : Fin I.card,
              1 ≤ DynkinShape.weightFactor .D s ∧
                DynkinShape.weightFactor .D s ≤ 2 := by
            intro s
            simp [DynkinShape.weightFactor]
          simpa [hrk] using (diagonal_bound_of_config_control T g hg hgenus hminimal hcountpos
            k hk v hinj hrange .D w hconfig r hr hfac 2 (by norm_num)
            hmax rk)
      | E6 | E7 | F4 | G2 =>
          exact hshort (by
            have := hconfig.1
            simp [DynkinShape.Allows] at this
            exact this.le.trans (by norm_num))
      | E8 =>
          have ht : I.card = 8 := by
            simpa [DynkinShape.Allows] using hconfig.1
          have hbj' : 0 < T.intersection (v rb) j := by simpa [hrb] using hbj
          obtain ⟨n, hpath, hn⟩ := e8_boundary_chain k hk ht v hinj hrange
            w hconfig rb rk j hjI hbj'
          have hpath' : BoundaryChain T j k n := by simpa [hrk] using hpath
          exact diagonal_bound_of_short_boundary_chain T g hg hgenus hminimal
            hcountpos j k hj n hn hpath'
  · by_cases hn : 1 < T.componentCount
    · exact (nonminus_diagonal_bound T g hg hgenus hminimal hn k hk).trans (by omega)
    · have hcount : T.componentCount = 1 := by
        have := T.componentCount_pos
        omega
      have hdiagzero : T.intersection k k = 0 := by
        have heq : ∀ j : Fin T.componentCount, j = k := fun j => Fin.ext (by omega)
        have hsum :
            (∑ j : Fin T.componentCount,
              T.intersection k j * T.multiplicity j) =
              T.intersection k k * T.multiplicity k :=
          Finset.sum_eq_single k (fun j _ hjk => (hjk (heq j)).elim)
            (fun hnot => (hnot (Finset.mem_univ k)).elim)
        have hs := T.intersection_mul_multiplicity k
        rw [hsum] at hs
        exact (mul_eq_zero.mp hs).resolve_right (T.multiplicity_pos k).ne'
      rw [hdiagzero, abs_zero, mul_zero]
      omega

end AlgebraicGeometry.NumericalType
