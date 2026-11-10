module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ClassificationProperSubgraphs.Classification
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Contribution
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.Irreducible
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.TwoVertices

/-!
# Genus-one configurations of numerical types: the four-component shapes

In the four-component case the shape of the incidence graph has to be settled first. No three
components form a triangle: a triangle of minus-two indices is a connected *proper* subgraph as soon
as there are more than three components, so Proposition 0C8Q applies to it, and every Dynkin diagram
on three vertices is a chain, whose two ends do not meet. A connected triangle-free graph on four
vertices is a chain, a star or a cycle, and the level identity of each of those three shapes pins it
down.

This file settles that shape; the level identity of each shape and the four-component classification
are in `StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneConfiguration/FourComponents.lean`.

## Main results

* `AlgebraicGeometry.NumericalType.four_vertex_shape_of_minusTwo` —
  the incidence graph of a four-component numerical type of minus-two indices is a chain, a
  star or a cycle.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

/-! ### The classification for four components -/

/-- Three minus-two indices of a numerical type with more than three components never pairwise
intersect: such a triangle is a connected proper subgraph, and every Dynkin diagram on three
vertices is a chain, whose two ends do not meet. -/
private lemma not_pairwise_intersecting_minusTwo_triple (T : NumericalType)
    (hn : 3 < T.componentCount) (x y z : Fin T.componentCount)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : IsMinusTwoIndex T x) (hy : IsMinusTwoIndex T y) (hz : IsMinusTwoIndex T z)
    (ha : T.intersection x y ≠ 0) (hb : T.intersection x z ≠ 0)
    (hc : T.intersection y z ≠ 0) : False := by
  classical
  have hcard : ({x, y, z} : Finset (Fin T.componentCount)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hpair : ∀ p ∈ ({x, y, z} : Finset (Fin T.componentCount)),
      ∀ q ∈ ({x, y, z} : Finset (Fin T.componentCount)), p ≠ q →
      T.intersection p q ≠ 0 := by
    intro p hp q hq hpq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    all_goals
      first
        | exact absurd rfl hpq
        | exact ha
        | exact hb
        | exact hc
        | (rw [T.intersection_symm]; first | exact ha | exact hb | exact hc)
  obtain ⟨v, hv, hrange, d, w, hcfg⟩ :=
    classify_connected_proper_minusTwo_subgraph T {x, y, z} (by omega) (by omega)
      (by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl <;> assumption)
      (by
        rintro ⟨J, ⟨p, hp⟩, hJ, hcut⟩
        obtain ⟨q, hqI, hqJ⟩ := Finset.exists_of_ssubset hJ
        exact hpair p (hJ.1 hp) q hqI (fun hpq => hqJ (hpq ▸ hp)) (hcut p hp q hqI hqJ))
  have hallow : d.Allows 3 := hcard ▸ hcfg.1
  have hd : d = .A ∨ d = .B ∨ d = .C := by
    cases d <;> simp_all [DynkinShape.Allows]
  have h0lt : 0 < ({x, y, z} : Finset (Fin T.componentCount)).card := by omega
  have h2lt : 2 < ({x, y, z} : Finset (Fin T.componentCount)).card := by omega
  set r : Fin ({x, y, z} : Finset (Fin T.componentCount)).card := ⟨0, h0lt⟩ with hrdef
  set s : Fin ({x, y, z} : Finset (Fin T.componentCount)).card := ⟨2, h2lt⟩ with hsdef
  have hrs : r ≠ s := by simp [hrdef, hsdef, Fin.ext_iff]
  have hnotedge : ¬ d.Edge r s := by
    rcases hd with rfl | rfl | rfl <;>
      simp only [DynkinShape.Edge, hrdef, hsdef] <;> omega
  have hzero : T.intersection (v r) (v s) = 0 := by
    rw [hcfg.2.2.2.1 r s, ite_eq_right hrs, ite_eq_right hnotedge]
  have hmem : ∀ t, v t ∈ ({x, y, z} : Finset (Fin T.componentCount)) := fun t => by
    have : v t ∈ Set.range v := ⟨t, rfl⟩
    rw [hrange] at this
    simpa using this
  exact hpair _ (hmem r) _ (hmem s) (fun hq => hrs (hv hq)) hzero

/-- A connected triangle-free graph on four vertices is a chain, a star or a cycle. The six
Booleans are the edges `01, 02, 03, 12, 13, 23`; the next seven say that no cut of the four
vertices is empty, and the last four that no triple of vertices is a triangle. The conclusion
lists the twelve chains, the four stars and the three cycles. -/
private lemma four_vertex_shape (e01 e02 e03 e12 e13 e23 : Bool)
    (c0 : e01 = true ∨ e02 = true ∨ e03 = true)
    (c1 : e01 = true ∨ e12 = true ∨ e13 = true)
    (c2 : e02 = true ∨ e12 = true ∨ e23 = true)
    (c3 : e03 = true ∨ e13 = true ∨ e23 = true)
    (c01 : e02 = true ∨ e03 = true ∨ e12 = true ∨ e13 = true)
    (c02 : e01 = true ∨ e03 = true ∨ e12 = true ∨ e23 = true)
    (c03 : e01 = true ∨ e02 = true ∨ e13 = true ∨ e23 = true)
    (t012 : ¬(e01 = true ∧ e02 = true ∧ e12 = true))
    (t013 : ¬(e01 = true ∧ e03 = true ∧ e13 = true))
    (t023 : ¬(e02 = true ∧ e03 = true ∧ e23 = true))
    (t123 : ¬(e12 = true ∧ e13 = true ∧ e23 = true)) :
    (e01 = true ∧ e02 = false ∧ e03 = false ∧ e12 = true ∧ e13 = false ∧ e23 = true) ∨
      (e01 = true ∧ e02 = false ∧ e03 = false ∧ e12 = false ∧ e13 = true ∧ e23 = true) ∨
      (e01 = false ∧ e02 = true ∧ e03 = false ∧ e12 = true ∧ e13 = true ∧ e23 = false) ∨
      (e01 = false ∧ e02 = true ∧ e03 = false ∧ e12 = false ∧ e13 = true ∧ e23 = true) ∨
      (e01 = false ∧ e02 = false ∧ e03 = true ∧ e12 = true ∧ e13 = true ∧ e23 = false) ∨
      (e01 = false ∧ e02 = false ∧ e03 = true ∧ e12 = true ∧ e13 = false ∧ e23 = true) ∨
      (e01 = true ∧ e02 = true ∧ e03 = false ∧ e12 = false ∧ e13 = false ∧ e23 = true) ∨
      (e01 = false ∧ e02 = true ∧ e03 = true ∧ e12 = true ∧ e13 = false ∧ e23 = false) ∨
      (e01 = true ∧ e02 = false ∧ e03 = true ∧ e12 = false ∧ e13 = false ∧ e23 = true) ∨
      (e01 = false ∧ e02 = true ∧ e03 = true ∧ e12 = false ∧ e13 = true ∧ e23 = false) ∨
      (e01 = true ∧ e02 = true ∧ e03 = false ∧ e12 = false ∧ e13 = true ∧ e23 = false) ∨
      (e01 = true ∧ e02 = false ∧ e03 = true ∧ e12 = true ∧ e13 = false ∧ e23 = false) ∨
      (e01 = true ∧ e02 = true ∧ e03 = true ∧ e12 = false ∧ e13 = false ∧ e23 = false) ∨
      (e01 = true ∧ e02 = false ∧ e03 = false ∧ e12 = true ∧ e13 = true ∧ e23 = false) ∨
      (e01 = false ∧ e02 = true ∧ e03 = false ∧ e12 = true ∧ e13 = false ∧ e23 = true) ∨
      (e01 = false ∧ e02 = false ∧ e03 = true ∧ e12 = false ∧ e13 = true ∧ e23 = true) ∨
      (e01 = false ∧ e02 = true ∧ e03 = true ∧ e12 = true ∧ e13 = true ∧ e23 = false) ∨
      (e01 = true ∧ e02 = false ∧ e03 = true ∧ e12 = true ∧ e13 = false ∧ e23 = true) ∨
      (e01 = true ∧ e02 = true ∧ e03 = false ∧ e12 = false ∧ e13 = true ∧ e23 = true) := by
  cases e01 <;> cases e02 <;> cases e03 <;> cases e12 <;> cases e13 <;> cases e23 <;>
    simp_all

/-- Connectedness, read off at an explicit set of components of a four-component numerical type:
a set of indices that contains one index and omits another has an index meeting its
complement. -/
private lemma four_vertex_cut (T : NumericalType) (e : Fin 4 ≃ Fin T.componentCount)
    (S : Fin 4 → Prop) (r₀ : Fin 4) (hr₀ : S r₀) (s₀ : Fin 4) (hs₀ : ¬ S s₀) :
    ∃ r s : Fin 4, S r ∧ ¬ S s ∧ T.intersection (e r) (e s) ≠ 0 := by
  by_contra hcon
  have hcon' : ∀ r s : Fin 4, S r → ¬ S s → T.intersection (e r) (e s) = 0 := by
    intro r s hr hs
    by_contra hrs
    exact hcon ⟨r, s, hr, hs, hrs⟩
  refine T.connected ⟨{u | S (e.symm u)}, ⟨e r₀, by simpa using hr₀⟩, ?_, ?_⟩
  · intro hS
    have hmem : e s₀ ∈ {u | S (e.symm u)} := hS ▸ Set.mem_univ _
    simp only [Set.mem_ofPred_eq, Equiv.symm_apply_apply] at hmem
    exact hs₀ hmem
  · intro i hi j hj
    simpa using hcon' (e.symm i) (e.symm j) hi hj

/-- The singleton cut at a component of a four-component numerical type: the component meets one
of the other three. -/
private lemma four_vertex_cut_one (T : NumericalType) (e : Fin 4 ≃ Fin T.componentCount)
    (a b c d : Fin 4) (hab : a ≠ b)
    (hcover : ∀ r : Fin 4, r = a ∨ r = b ∨ r = c ∨ r = d) :
    T.intersection (e a) (e b) ≠ 0 ∨ T.intersection (e a) (e c) ≠ 0 ∨
      T.intersection (e a) (e d) ≠ 0 := by
  obtain ⟨r, s, hr, hs, hrs⟩ :=
    four_vertex_cut T e (fun r => r = a) a rfl b (Ne.symm hab)
  subst hr
  rcases hcover s with rfl | rfl | rfl | rfl
  · exact absurd rfl hs
  · exact Or.inl hrs
  · exact Or.inr (Or.inl hrs)
  · exact Or.inr (Or.inr hrs)

/-- The two-element cut at a pair of components of a four-component numerical type: one of the
two meets one of the other two. -/
private lemma four_vertex_cut_two (T : NumericalType) (e : Fin 4 ≃ Fin T.componentCount)
    (a b c d : Fin 4) (hac : a ≠ c) (hbc : b ≠ c)
    (hcover : ∀ r : Fin 4, r = a ∨ r = b ∨ r = c ∨ r = d) :
    T.intersection (e a) (e c) ≠ 0 ∨ T.intersection (e a) (e d) ≠ 0 ∨
      T.intersection (e b) (e c) ≠ 0 ∨ T.intersection (e b) (e d) ≠ 0 := by
  obtain ⟨r, s, hr, hs, hrs⟩ :=
    four_vertex_cut T e (fun r => r = a ∨ r = b) a (Or.inl rfl) c
      (by rintro (hq | hq); exacts [hac hq.symm, hbc hq.symm])
  rcases hr with rfl | rfl <;> rcases hcover s with rfl | rfl | rfl | rfl
  · exact absurd (Or.inl rfl) hs
  · exact absurd (Or.inr rfl) hs
  · exact Or.inl hrs
  · exact Or.inr (Or.inl hrs)
  · exact absurd (Or.inl rfl) hs
  · exact absurd (Or.inr rfl) hs
  · exact Or.inr (Or.inr (Or.inl hrs))
  · exact Or.inr (Or.inr (Or.inr hrs))

/-- The incidence graph of a four-component numerical type all of whose indices are minus-two
indices is a chain, a star or a cycle. Connectedness rules out an empty cut, and no three
components form a triangle, because a triangle is a connected proper subgraph and no Dynkin
diagram on three vertices is one. -/
public lemma four_vertex_shape_of_minusTwo (T : NumericalType) (hn : T.componentCount = 4)
    (h : ∀ i, IsMinusTwoIndex T i) (e : Fin 4 ≃ Fin T.componentCount) :
    (0 < T.intersection (e 0) (e 1) ∧
        T.intersection (e 0) (e 2) = 0 ∧
        T.intersection (e 0) (e 3) = 0 ∧
        0 < T.intersection (e 1) (e 2) ∧
        T.intersection (e 1) (e 3) = 0 ∧
        0 < T.intersection (e 2) (e 3)) ∨
      (0 < T.intersection (e 0) (e 1) ∧
        T.intersection (e 0) (e 2) = 0 ∧
        T.intersection (e 0) (e 3) = 0 ∧
        T.intersection (e 1) (e 2) = 0 ∧
        0 < T.intersection (e 1) (e 3) ∧
        0 < T.intersection (e 2) (e 3)) ∨
      (T.intersection (e 0) (e 1) = 0 ∧
        0 < T.intersection (e 0) (e 2) ∧
        T.intersection (e 0) (e 3) = 0 ∧
        0 < T.intersection (e 1) (e 2) ∧
        0 < T.intersection (e 1) (e 3) ∧
        T.intersection (e 2) (e 3) = 0) ∨
      (T.intersection (e 0) (e 1) = 0 ∧
        0 < T.intersection (e 0) (e 2) ∧
        T.intersection (e 0) (e 3) = 0 ∧
        T.intersection (e 1) (e 2) = 0 ∧
        0 < T.intersection (e 1) (e 3) ∧
        0 < T.intersection (e 2) (e 3)) ∨
      (T.intersection (e 0) (e 1) = 0 ∧
        T.intersection (e 0) (e 2) = 0 ∧
        0 < T.intersection (e 0) (e 3) ∧
        0 < T.intersection (e 1) (e 2) ∧
        0 < T.intersection (e 1) (e 3) ∧
        T.intersection (e 2) (e 3) = 0) ∨
      (T.intersection (e 0) (e 1) = 0 ∧
        T.intersection (e 0) (e 2) = 0 ∧
        0 < T.intersection (e 0) (e 3) ∧
        0 < T.intersection (e 1) (e 2) ∧
        T.intersection (e 1) (e 3) = 0 ∧
        0 < T.intersection (e 2) (e 3)) ∨
      (0 < T.intersection (e 0) (e 1) ∧
        0 < T.intersection (e 0) (e 2) ∧
        T.intersection (e 0) (e 3) = 0 ∧
        T.intersection (e 1) (e 2) = 0 ∧
        T.intersection (e 1) (e 3) = 0 ∧
        0 < T.intersection (e 2) (e 3)) ∨
      (T.intersection (e 0) (e 1) = 0 ∧
        0 < T.intersection (e 0) (e 2) ∧
        0 < T.intersection (e 0) (e 3) ∧
        0 < T.intersection (e 1) (e 2) ∧
        T.intersection (e 1) (e 3) = 0 ∧
        T.intersection (e 2) (e 3) = 0) ∨
      (0 < T.intersection (e 0) (e 1) ∧
        T.intersection (e 0) (e 2) = 0 ∧
        0 < T.intersection (e 0) (e 3) ∧
        T.intersection (e 1) (e 2) = 0 ∧
        T.intersection (e 1) (e 3) = 0 ∧
        0 < T.intersection (e 2) (e 3)) ∨
      (T.intersection (e 0) (e 1) = 0 ∧
        0 < T.intersection (e 0) (e 2) ∧
        0 < T.intersection (e 0) (e 3) ∧
        T.intersection (e 1) (e 2) = 0 ∧
        0 < T.intersection (e 1) (e 3) ∧
        T.intersection (e 2) (e 3) = 0) ∨
      (0 < T.intersection (e 0) (e 1) ∧
        0 < T.intersection (e 0) (e 2) ∧
        T.intersection (e 0) (e 3) = 0 ∧
        T.intersection (e 1) (e 2) = 0 ∧
        0 < T.intersection (e 1) (e 3) ∧
        T.intersection (e 2) (e 3) = 0) ∨
      (0 < T.intersection (e 0) (e 1) ∧
        T.intersection (e 0) (e 2) = 0 ∧
        0 < T.intersection (e 0) (e 3) ∧
        0 < T.intersection (e 1) (e 2) ∧
        T.intersection (e 1) (e 3) = 0 ∧
        T.intersection (e 2) (e 3) = 0) ∨
      (0 < T.intersection (e 0) (e 1) ∧
        0 < T.intersection (e 0) (e 2) ∧
        0 < T.intersection (e 0) (e 3) ∧
        T.intersection (e 1) (e 2) = 0 ∧
        T.intersection (e 1) (e 3) = 0 ∧
        T.intersection (e 2) (e 3) = 0) ∨
      (0 < T.intersection (e 0) (e 1) ∧
        T.intersection (e 0) (e 2) = 0 ∧
        T.intersection (e 0) (e 3) = 0 ∧
        0 < T.intersection (e 1) (e 2) ∧
        0 < T.intersection (e 1) (e 3) ∧
        T.intersection (e 2) (e 3) = 0) ∨
      (T.intersection (e 0) (e 1) = 0 ∧
        0 < T.intersection (e 0) (e 2) ∧
        T.intersection (e 0) (e 3) = 0 ∧
        0 < T.intersection (e 1) (e 2) ∧
        T.intersection (e 1) (e 3) = 0 ∧
        0 < T.intersection (e 2) (e 3)) ∨
      (T.intersection (e 0) (e 1) = 0 ∧
        T.intersection (e 0) (e 2) = 0 ∧
        0 < T.intersection (e 0) (e 3) ∧
        T.intersection (e 1) (e 2) = 0 ∧
        0 < T.intersection (e 1) (e 3) ∧
        0 < T.intersection (e 2) (e 3)) ∨
      (T.intersection (e 0) (e 1) = 0 ∧
        0 < T.intersection (e 0) (e 2) ∧
        0 < T.intersection (e 0) (e 3) ∧
        0 < T.intersection (e 1) (e 2) ∧
        0 < T.intersection (e 1) (e 3) ∧
        T.intersection (e 2) (e 3) = 0) ∨
      (0 < T.intersection (e 0) (e 1) ∧
        T.intersection (e 0) (e 2) = 0 ∧
        0 < T.intersection (e 0) (e 3) ∧
        0 < T.intersection (e 1) (e 2) ∧
        T.intersection (e 1) (e 3) = 0 ∧
        0 < T.intersection (e 2) (e 3)) ∨
      (0 < T.intersection (e 0) (e 1) ∧
        0 < T.intersection (e 0) (e 2) ∧
        T.intersection (e 0) (e 3) = 0 ∧
        T.intersection (e 1) (e 2) = 0 ∧
        0 < T.intersection (e 1) (e 3) ∧
        0 < T.intersection (e 2) (e 3)) := by
  have hne : ∀ i j : Fin 4, i ≠ j → e i ≠ e j := fun i j hij hq => hij (e.injective hq)
  have hk : ∀ i j : Fin 4, i ≠ j → (0 < T.intersection (e i) (e j) ↔
      decide (T.intersection (e i) (e j) ≠ 0) = true) ∧ (T.intersection (e i) (e j) = 0 ↔
      decide (T.intersection (e i) (e j) ≠ 0) = false) := fun i j hij => by
    have := T.intersection_nonneg _ _ (hne i j hij)
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_not, ne_eq]
    exact ⟨⟨fun h => h.ne', fun h => lt_of_le_of_ne this (Ne.symm h)⟩, trivial⟩
  have hcover : ∀ r : Fin 4, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by decide
  have hc0 := four_vertex_cut_one T e 0 1 2 3 (by decide) hcover
  have hc1 := four_vertex_cut_one T e 1 0 2 3 (by decide) (by decide)
  have hc2 := four_vertex_cut_one T e 2 0 1 3 (by decide) (by decide)
  have hc3 := four_vertex_cut_one T e 3 0 1 2 (by decide) (by decide)
  have hc01 := four_vertex_cut_two T e 0 1 2 3 (by decide) (by decide) hcover
  have hc02 := four_vertex_cut_two T e 0 2 1 3 (by decide) (by decide) (by decide)
  have hc03 := four_vertex_cut_two T e 0 3 1 2 (by decide) (by decide) (by decide)
  simp only [T.intersection_symm (e 1) (e 0), T.intersection_symm (e 2) (e 0),
    T.intersection_symm (e 2) (e 1), T.intersection_symm (e 3) (e 0),
    T.intersection_symm (e 3) (e 1), T.intersection_symm (e 3) (e 2)] at hc1 hc2 hc3 hc02 hc03
  have htri : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      ¬(decide (T.intersection (e i) (e j) ≠ 0) = true ∧
        decide (T.intersection (e i) (e k) ≠ 0) = true ∧
        decide (T.intersection (e j) (e k) ≠ 0) = true) := by
    rintro i j k hij hik hjk ⟨h1, h2, h3⟩
    exact not_pairwise_intersecting_minusTwo_triple T (by omega) (e i) (e j) (e k)
      (hne i j hij) (hne i k hik) (hne j k hjk) (h _) (h _) (h _)
      (of_decide_eq_true h1) (of_decide_eq_true h2) (of_decide_eq_true h3)
  have hshape := four_vertex_shape
    (decide (T.intersection (e 0) (e 1) ≠ 0)) (decide (T.intersection (e 0) (e 2) ≠ 0))
    (decide (T.intersection (e 0) (e 3) ≠ 0)) (decide (T.intersection (e 1) (e 2) ≠ 0))
    (decide (T.intersection (e 1) (e 3) ≠ 0)) (decide (T.intersection (e 2) (e 3) ≠ 0))
    (by simpa using hc0) (by simpa using hc1) (by simpa using hc2) (by simpa using hc3)
    (by simpa using hc01) (by simpa using hc02) (by simpa using hc03)
    (htri 0 1 2 (by decide) (by decide) (by decide))
    (htri 0 1 3 (by decide) (by decide) (by decide))
    (htri 0 2 3 (by decide) (by decide) (by decide))
    (htri 1 2 3 (by decide) (by decide) (by decide))
  simp only [(hk 0 1 (by decide)).1, (hk 0 2 (by decide)).1, (hk 0 3 (by decide)).1,
    (hk 1 2 (by decide)).1, (hk 1 3 (by decide)).1, (hk 2 3 (by decide)).1,
    (hk 0 1 (by decide)).2, (hk 0 2 (by decide)).2, (hk 0 3 (by decide)).2,
    (hk 1 2 (by decide)).2, (hk 1 3 (by decide)).2, (hk 2 3 (by decide)).2]
  exact hshape

end AlgebraicGeometry.NumericalType
