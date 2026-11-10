module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneAffineExtension

/-!
# Reading off the affine extension system

`AlgebraicGeometry.NumericalType.affine_system_of_erase_leaf` presents the classification of
minimal numerical types of genus one with a component meeting exactly one other as a linear
system in the weighted Cartan matrix of a Dynkin shape. This file supplies the tools for
solving that system: the expansion of a row of the weighted Cartan matrix over the neighbours
of a vertex, the solution of the three-term recurrence that such a row becomes along a chain,
and the translation of a lower bound on the number of components a given component meets into
a lower bound on the number of neighbours of a vertex of the diagram.

## Main definitions

* `AlgebraicGeometry.shiftExtend` — a vector on `Fin t` read as a sequence on `ℕ`, shifted by
  one and extended by zero, so that the three-term recurrence `2 Mⱼ₊₁ = Mⱼ + Mⱼ₊₂` expresses
  the row of the weighted Cartan matrix at the `j`-th vertex of a chain uniformly, including at
  the two ends.

## Main results

* `AlgebraicGeometry.DynkinShape.sum_weightedCartan_eq` — a row of the weighted Cartan matrix,
  evaluated on a vector, is twice the weight factor at the vertex times the entry there minus
  the contributions of its neighbours.
* `AlgebraicGeometry.DynkinShape.row_one`, `row_two`, `row_three` — the same for a vertex with
  one, two or three neighbours, listed.
* `AlgebraicGeometry.recurrence_arith` — a sequence satisfying `2 Mⱼ₊₁ = Mⱼ + Mⱼ₊₂` on an
  interval is an arithmetic progression there.
* `AlgebraicGeometry.NumericalType.exists_two_edge_of_three_le_neighborCount` — a component
  meeting three or more others is a vertex of the diagram with at least two neighbours in it,
  and with three unless it is the attachment vertex.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry

/-! ### Entries of the weighted Cartan matrix -/

/-- No vertex of a Dynkin diagram on an allowed number of vertices is joined to itself. -/
public lemma DynkinShape.not_edge_self {t : ℕ} (d : DynkinShape) (ht : d.Allows t) (r : Fin t) :
    ¬ d.Edge r r := by
  have hr := r.isLt
  cases d <;> simp only [DynkinShape.Allows] at ht <;>
    simp only [DynkinShape.Edge] <;> omega

/-- The diagonal entry of the weighted Cartan matrix. -/
public lemma DynkinShape.weightedCartan_self {t : ℕ} (d : DynkinShape) (r : Fin t) :
    d.weightedCartan r r = 2 * d.weightFactor r := by
  unfold DynkinShape.weightedCartan
  simp

/-- The entry of the weighted Cartan matrix along an edge. -/
public lemma DynkinShape.weightedCartan_edge {t : ℕ} (d : DynkinShape) {r s : Fin t}
    (hne : r ≠ s) (h : d.Edge r s) :
    d.weightedCartan r s = -max (d.weightFactor r) (d.weightFactor s) := by
  unfold DynkinShape.weightedCartan
  simp [hne, h]

/-- The entry of the weighted Cartan matrix away from the diagonal and the edges. -/
public lemma DynkinShape.weightedCartan_of_not_edge {t : ℕ} (d : DynkinShape) {r s : Fin t}
    (hne : r ≠ s) (h : ¬ d.Edge r s) : d.weightedCartan r s = 0 := by
  unfold DynkinShape.weightedCartan
  simp [hne, h]

/-! ### Rows of the weighted Cartan matrix -/

/-- A row of the weighted Cartan matrix, evaluated on a vector: twice the weight factor at the
vertex times the entry there, minus the contributions of its neighbours. -/
public lemma DynkinShape.sum_weightedCartan_eq {t : ℕ} (d : DynkinShape) (m : Fin t → ℤ)
    (r : Fin t) (S : Finset (Fin t)) (hrS : r ∉ S) (hS : ∀ s, d.Edge r s ↔ s ∈ S) :
    ∑ s, d.weightedCartan r s * m s
      = 2 * d.weightFactor r * m r
        - ∑ s ∈ S, max (d.weightFactor r) (d.weightFactor s) * m s := by
  classical
  have hzero : ∀ s ∈ (Finset.univ : Finset (Fin t)), s ∉ insert r S →
      d.weightedCartan r s * m s = 0 := by
    intro s _ hs
    simp only [Finset.mem_insert, not_or] at hs
    have hne : r ≠ s := fun h => hs.1 h.symm
    rw [d.weightedCartan_of_not_edge hne (fun h => hs.2 ((hS s).mp h)), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (insert r S)) hzero,
    Finset.sum_insert hrS, d.weightedCartan_self r]
  have hedges : ∀ s ∈ S, d.weightedCartan r s * m s
      = -(max (d.weightFactor r) (d.weightFactor s) * m s) := by
    intro s hs
    have hne : r ≠ s := fun h => hrS (h ▸ hs)
    rw [d.weightedCartan_edge hne ((hS s).mpr hs)]
    ring
  rw [Finset.sum_congr rfl hedges, Finset.sum_neg_distrib]
  ring

/-- The two ends of an edge of a Dynkin diagram on an allowed number of vertices differ. -/
private lemma DynkinShape.ne_of_edge {t : ℕ} (d : DynkinShape) (ht : d.Allows t) {r a : Fin t}
    (h : d.Edge r a) : r ≠ a :=
  fun e => d.not_edge_self ht r (e ▸ h)

/-- A row of the weighted Cartan matrix at a vertex with exactly one neighbour. -/
public lemma DynkinShape.row_one {t : ℕ} (d : DynkinShape) (ht : d.Allows t) (m : Fin t → ℤ)
    (r a : Fin t) (ha : d.Edge r a) (hother : ∀ s, d.Edge r s → s = a) :
    ∑ s, d.weightedCartan r s * m s
      = 2 * d.weightFactor r * m r - max (d.weightFactor r) (d.weightFactor a) * m a := by
  classical
  have hra := d.ne_of_edge ht ha
  rw [d.sum_weightedCartan_eq m r {a} (by simp [hra]) (fun s => by
    simp only [Finset.mem_singleton]
    exact ⟨hother s, fun h => h ▸ ha⟩), Finset.sum_singleton]

/-- A row of the weighted Cartan matrix at a vertex with exactly two neighbours. -/
public lemma DynkinShape.row_two {t : ℕ} (d : DynkinShape) (ht : d.Allows t) (m : Fin t → ℤ)
    (r a b : Fin t) (hab : a ≠ b) (ha : d.Edge r a) (hb : d.Edge r b)
    (hother : ∀ s, d.Edge r s → s = a ∨ s = b) :
    ∑ s, d.weightedCartan r s * m s
      = 2 * d.weightFactor r * m r - max (d.weightFactor r) (d.weightFactor a) * m a
        - max (d.weightFactor r) (d.weightFactor b) * m b := by
  classical
  have hra := d.ne_of_edge ht ha
  have hrb := d.ne_of_edge ht hb
  rw [d.sum_weightedCartan_eq m r {a, b} (by simp [hra, hrb]) (fun s => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hother s, by rintro (rfl | rfl); exacts [ha, hb]⟩),
    Finset.sum_insert (by simp [hab]), Finset.sum_singleton]
  ring

/-- A row of the weighted Cartan matrix at a vertex with exactly three neighbours. -/
public lemma DynkinShape.row_three {t : ℕ} (d : DynkinShape) (ht : d.Allows t) (m : Fin t → ℤ)
    (r a b c : Fin t) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : d.Edge r a) (hb : d.Edge r b) (hc : d.Edge r c)
    (hother : ∀ s, d.Edge r s → s = a ∨ s = b ∨ s = c) :
    ∑ s, d.weightedCartan r s * m s
      = 2 * d.weightFactor r * m r - max (d.weightFactor r) (d.weightFactor a) * m a
        - max (d.weightFactor r) (d.weightFactor b) * m b
        - max (d.weightFactor r) (d.weightFactor c) * m c := by
  classical
  have hra := d.ne_of_edge ht ha
  have hrb := d.ne_of_edge ht hb
  have hrc := d.ne_of_edge ht hc
  rw [d.sum_weightedCartan_eq m r {a, b, c} (by simp [hra, hrb, hrc]) (fun s => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact ⟨hother s, by rintro (rfl | rfl | rfl); exacts [ha, hb, hc]⟩),
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton]
  ring

/-! ### The three-term recurrence -/

/-- A vector on `Fin t` read as a sequence on `ℕ`, shifted by one and extended by zero. The
entry at `j + 1` is the entry at the `j`-th vertex, the entry at `0` and the entries beyond `t`
are zero. -/
public noncomputable def shiftExtend {t : ℕ} (m : Fin t → ℤ) (j : ℕ) : ℤ := by
  classical
  exact if h : 0 < j ∧ j - 1 < t then m ⟨j - 1, h.2⟩ else 0

@[simp]
public lemma shiftExtend_zero {t : ℕ} (m : Fin t → ℤ) : shiftExtend m 0 = 0 := by
  simp [shiftExtend]

@[simp]
public lemma shiftExtend_succ {t : ℕ} (m : Fin t → ℤ) (r : Fin t) :
    shiftExtend m (r.val + 1) = m r := by
  have hr := r.isLt
  simp only [shiftExtend, Nat.add_sub_cancel]
  rw [dite_eq_left ⟨by omega, hr⟩]

public lemma shiftExtend_of_le {t : ℕ} (m : Fin t → ℤ) {j : ℕ} (hj : t + 1 ≤ j) :
    shiftExtend m j = 0 := by
  simp only [shiftExtend]
  rw [dite_eq_right (by omega)]

/-- A sequence satisfying the three-term recurrence `2 Mⱼ₊₁ = Mⱼ + Mⱼ₊₂` on `[a, b]` is an
arithmetic progression on `[a, b + 2]`; the paired form carrying two consecutive values, which
is what the induction needs. -/
public lemma recurrence_arith_pair (M : ℕ → ℤ) (a b : ℕ)
    (h : ∀ j, a ≤ j → j ≤ b → 2 * M (j + 1) = M j + M (j + 2)) (i : ℕ) (hi : a + i ≤ b + 1) :
    M (a + i) = M a + i * (M (a + 1) - M a) ∧
      M (a + i + 1) = M a + (i + 1) * (M (a + 1) - M a) := by
  induction i with
  | zero => exact ⟨by simp, by push_cast; ring⟩
  | succ p ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hrec := h (a + p) (by omega) (by omega)
      refine ⟨by rwa [show a + (p + 1) = a + p + 1 by ring], ?_⟩
      rw [show a + (p + 1) + 1 = a + p + 2 by ring]
      push_cast at h1 h2 ⊢
      linarith

/-- A sequence satisfying the three-term recurrence `2 Mⱼ₊₁ = Mⱼ + Mⱼ₊₂` on `[a, b]` is an
arithmetic progression on `[a, b + 2]`. -/
public lemma recurrence_arith (M : ℕ → ℤ) (a b : ℕ)
    (h : ∀ j, a ≤ j → j ≤ b → 2 * M (j + 1) = M j + M (j + 2)) (i : ℕ) (hi : a + i ≤ b + 2) :
    M (a + i) = M a + i * (M (a + 1) - M a) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by omega⟩
    rw [show a + (p + 1) = a + p + 1 by ring]
    exact (recurrence_arith_pair M a b h p (by omega)).2

namespace NumericalType

/-! ### Matching a coefficient table -/

/-- A numerical type matches a coefficient table as soon as some ordering of all of its
components realises the table entry by entry. -/
public lemma matchesCoefficients_of_ordering (T : NumericalType) {n : ℕ}
    (hcard : n = T.componentCount) (v : Fin n → Fin T.componentCount)
    (hvinj : Function.Injective v) (mc wc : Fin n → ℤ) (ac : Fin n → Fin n → ℤ)
    (gc : Fin n → ℤ) (m w : ℤ) (hm : 0 < m) (hw : 0 < w)
    (hmul : ∀ i, T.multiplicity (v i) = mc i * m)
    (hwt : ∀ i, T.weight (v i) = wc i * w)
    (hint : ∀ i j, T.intersection (v i) (v j) = ac i j * w)
    (hgen : ∀ i, T.componentGenus (v i) = gc i) :
    MatchesCoefficients T n mc wc ac gc :=
  ⟨Equiv.ofBijective v ((Fintype.bijective_iff_injective_and_card v).mpr
    ⟨hvinj, by rw [Fintype.card_fin, Fintype.card_fin, hcard]⟩),
    m, w, hm, hw, hmul, hwt, hint, hgen⟩

/-- The intersection numbers of a numerical type all of whose indices are minus-two indices,
read off an ordering of its components for which meeting is adjacency for a given relation: on
the diagonal minus twice the weight, along an adjacent pair the larger of the two weights, and
zero elsewhere. This is the shape-free form of the computation that matching a coefficient table
needs; the adjacency relation is a parameter, so a chain, a cycle and a fork are all instances
of it. -/
public lemma intersection_eq_of_adjacency (T : NumericalType) {n : ℕ}
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin n → Fin T.componentCount) (hvinj : Function.Injective v)
    (adj : Fin n → Fin n → Prop)
    (hchar : ∀ a b : Fin n, T.intersection (v a) (v b) ≠ 0 ↔ (adj a b ∨ a = b))
    (wc : Fin n → ℤ) (ac : Fin n → Fin n → ℤ) (w : ℤ) (hw : 0 < w)
    (hwt : ∀ a, T.weight (v a) = wc a * w)
    (hdiag : ∀ a, ac a a = -2 * wc a)
    (hedge : ∀ a b, a ≠ b → adj a b → ac a b = max (wc a) (wc b))
    (hzero : ∀ a b, a ≠ b → ¬ adj a b → ac a b = 0)
    (a b : Fin n) : T.intersection (v a) (v b) = ac a b * w := by
  classical
  by_cases hab : a = b
  · subst hab
    rw [(hminus (v a)).2, hwt a, hdiag a]
    ring
  · by_cases hadj : adj a b
    · have hne : v a ≠ v b := hvinj.ne hab
      have hnz : T.intersection (v a) (v b) ≠ 0 := (hchar a b).mpr (Or.inl hadj)
      have hpos : 0 < T.intersection (v a) (v b) :=
        lt_of_le_of_ne (T.intersection_nonneg _ _ hne) (Ne.symm hnz)
      rw [intersection_eq_max_weight_of_intersects T hn _ _ (hminus _) (hminus _) hpos,
        hwt a, hwt b, hedge a b hab hadj]
      exact (max_mul_of_nonneg (wc a) (wc b) hw.le).symm
    · have h0 : T.intersection (v a) (v b) = 0 := by
        by_contra hc
        exact ((hchar a b).mp hc).elim hadj hab
      rw [h0, hzero a b hab hadj]
      ring

/-- A numerical type all of whose indices are minus-two indices matches a finite coefficient
table as soon as some ordering of all of its components realises the adjacency of the table: the
list form of `AlgebraicGeometry.NumericalType.intersection_eq_of_adjacency` composed with
`AlgebraicGeometry.NumericalType.matchesCoefficients_of_ordering`. -/
public lemma matchesFinite_of_adjacency (T : NumericalType) {n : ℕ}
    (hn : 2 < T.componentCount) (hcard : n = T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (v : Fin n → Fin T.componentCount) (hvinj : Function.Injective v)
    (adj : Fin n → Fin n → Prop)
    (hchar : ∀ a b : Fin n, T.intersection (v a) (v b) ≠ 0 ↔ (adj a b ∨ a = b))
    (mc wc : List ℤ) (ac : List (List ℤ)) (hlen : mc.length = n) (m w : ℤ)
    (hm : 0 < m) (hw : 0 < w)
    (hmul : ∀ a : Fin n, T.multiplicity (v a) = mc.getD a.val 0 * m)
    (hwt : ∀ a : Fin n, T.weight (v a) = wc.getD a.val 0 * w)
    (hdiag : ∀ a : Fin n, (ac.getD a.val []).getD a.val 0 = -2 * wc.getD a.val 0)
    (hedge : ∀ a b : Fin n, a ≠ b → adj a b →
      (ac.getD a.val []).getD b.val 0 = max (wc.getD a.val 0) (wc.getD b.val 0))
    (hzero : ∀ a b : Fin n, a ≠ b → ¬ adj a b → (ac.getD a.val []).getD b.val 0 = 0) :
    MatchesFinite T mc wc ac := by
  obtain ⟨u, hu⟩ : ∃ u : Fin mc.length → Fin n, ∀ i, (u i).val = i.val :=
    ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩, fun i => rfl⟩
  have hueq : ∀ i j, u i = u j ↔ i = j :=
    fun i j => ⟨fun h => Fin.ext (by rw [← hu i, ← hu j, h]), congrArg u⟩
  have huinj : Function.Injective (fun i => v (u i)) := fun p q h => (hueq p q).mp (hvinj h)
  have hchar' : ∀ i j : Fin mc.length, T.intersection (v (u i)) (v (u j)) ≠ 0 ↔
      (adj (u i) (u j) ∨ i = j) :=
    fun i j => (hchar (u i) (u j)).trans (or_congr_right (hueq i j))
  have hwt' : ∀ i : Fin mc.length, T.weight (v (u i)) = wc.getD i.val 0 * w :=
    fun i => by simpa [hu] using hwt (u i)
  refine matchesCoefficients_of_ordering T (by omega) (fun i => v (u i)) huinj _ _ _ _ m w hm hw
    (fun i => by simpa [hu] using hmul (u i)) hwt' ?_ (fun i => (hminus _).1)
  intro p q
  refine intersection_eq_of_adjacency T hn hminus (fun i => v (u i)) huinj
    (fun i j => adj (u i) (u j)) hchar'
    (fun i => wc.getD i.val 0) (fun i j => (ac.getD i.val []).getD j.val 0) w hw
    hwt' (fun i => by simpa [hu] using hdiag (u i)) ?_ ?_ p q
  · intro i j hij hadj
    simpa [hu] using hedge (u i) (u j) (mt (hueq i j).mp hij) hadj
  · intro i j hij hadj
    simpa [hu] using hzero (u i) (u j) (mt (hueq i j).mp hij) hadj

/-! ### The meeting pattern of a configuration with one component attached -/

/-- The pattern of meetings in a numerical type which is a Dynkin configuration together with
one further component `l` attached at a single vertex: two vertices of the configuration meet
exactly when they are joined in the diagram, the attached component meets the configuration only
at the attachment vertex, and every component meets itself. -/
public lemma intersection_ne_zero_iff_of_erase_leaf {t : ℕ} (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (d : DynkinShape) (w : ℤ) (hcfg : IsDynkinConfiguration T v d w)
    (r₀ : Fin t) (hr₀ : v r₀ = x) :
    (∀ r s, T.intersection (v r) (v s) ≠ 0 ↔ (d.Edge r s ∨ r = s)) ∧
      (∀ r, T.intersection l (v r) ≠ 0 ↔ r = r₀) ∧ T.intersection l l ≠ 0 := by
  classical
  have hwpos : 0 < w := hcfg.2.1
  have hwfpos : ∀ r : Fin t, 0 < d.weightFactor r := by
    intro r
    have h := T.weight_pos (v r)
    rw [hcfg.2.2.1 r] at h
    by_contra hc
    push Not at hc
    nlinarith
  have hself : ∀ i, T.intersection i i ≠ 0 := fun i => by
    rw [(hminus i).2]
    have := T.weight_pos i
    omega
  refine ⟨fun r s => ?_, fun r => ?_, hself l⟩
  · by_cases hrs : r = s
    · subst hrs
      exact ⟨fun _ => Or.inr rfl, fun _ => hself _⟩
    · rw [hcfg.2.2.2.1 r s, ite_eq_right hrs]
      by_cases hE : d.Edge r s
      · rw [ite_eq_left hE]
        exact ⟨fun _ => Or.inl hE, fun _ => (mul_pos (lt_max_of_lt_left (hwfpos r)) hwpos).ne'⟩
      · rw [ite_eq_right hE]
        exact ⟨fun h => absurd rfl h, fun h => h.elim (absurd · hE) (absurd · hrs)⟩
  · refine ⟨fun h => hvinj ((hleaf (v r) (hvl r) h).trans hr₀.symm), fun h => ?_⟩
    subst h
    rw [hr₀]
    rcases lt_or_eq_of_le (T.intersection_nonneg l x hlx) with hp | hp
    · omega
    · exfalso
      have h1 : 1 ≤ (neighbors T l).card := one_le_neighborCount T (by omega) l
      obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (neighbors T l).card by omega)
      rw [mem_neighbors_iff] at hy
      have hyx := hleaf y (Ne.symm hy.1) hy.2
      rw [hyx] at hy
      exact hy.2 hp.symm

/-! ### Components meeting three or more others -/

/-- In a numerical type obtained from a Dynkin configuration by attaching one further component
`l` at a single vertex, a component meeting three or more others is a vertex of the diagram with
at least two neighbours there; it has three unless it is the attachment vertex. -/
public lemma exists_two_edge_of_three_le_neighborCount {t : ℕ} (T : NumericalType)
    (l x : Fin T.componentCount) (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (d : DynkinShape) (w : ℤ) (hcfg : IsDynkinConfiguration T v d w)
    (r₀ : Fin t) (hr₀ : v r₀ = x)
    (i : Fin T.componentCount) (hdeg : 3 ≤ neighborCount T i) :
    ∃ r : Fin t, v r = i ∧ ∃ a b : Fin t, a ≠ b ∧ d.Edge r a ∧ d.Edge r b ∧
      (r = r₀ ∨ ∃ c : Fin t, c ≠ a ∧ c ≠ b ∧ d.Edge r c) := by
  classical
  -- the attached component meets only `x`
  have hsub : neighbors T l ⊆ {x} := by
    intro y hy
    obtain ⟨hne, hint⟩ := (mem_neighbors_iff T l y).mp hy
    exact Finset.mem_singleton.mpr (hleaf y (Ne.symm hne) hint)
  have hlcard : (neighbors T l).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have hdegc : 3 ≤ (neighbors T i).card := hdeg
  have hil : i ≠ l := by
    intro h
    rw [h] at hdegc
    omega
  obtain ⟨r, hr⟩ := hvsurj i hil
  -- every neighbour of `i` other than `l` is a neighbour of `r` in the diagram
  have hnb : ∀ y ∈ neighbors T i, y ≠ l → ∃ s : Fin t, v s = y ∧ d.Edge r s := by
    intro y hy hyl
    obtain ⟨hne, hint⟩ := (mem_neighbors_iff T i y).mp hy
    obtain ⟨s, hs⟩ := hvsurj y hyl
    refine ⟨s, hs, ?_⟩
    by_contra hedge
    have hrs : r ≠ s := fun h => hne (by rw [← hr, ← hs, h])
    have h0 : T.intersection (v r) (v s) = 0 := by
      simp [hcfg.2.2.2.1 r s, hrs, hedge]
    rw [hr, hs] at h0
    exact hint h0
  have hdist : ∀ {a b : Fin t} {y z : Fin T.componentCount}, v a = y → v b = z → y ≠ z → a ≠ b :=
    fun h1 h2 hyz h => hyz (by rw [← h1, ← h2, h])
  -- if `l` is a neighbour of `i` then `i` is the attachment vertex
  have hlmem : l ∈ neighbors T i → r = r₀ := by
    intro hl
    obtain ⟨hne, hint⟩ := (mem_neighbors_iff T i l).mp hl
    have hint' : T.intersection l i ≠ 0 := by
      rw [T.intersection_symm]
      omega
    have := hleaf i hil hint'
    exact hvinj (by rw [hr, this, hr₀])
  refine ⟨r, hr, ?_⟩
  by_cases hl : l ∈ neighbors T i
  · -- two neighbours remain after discarding `l`
    have hcard : 1 < ((neighbors T i).erase l).card := by
      have := Finset.card_erase_of_mem hl
      omega
    obtain ⟨y, z, hy, hz, hyz⟩ := Finset.one_lt_card_iff.mp hcard
    obtain ⟨a, hay, ha⟩ := hnb y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
    obtain ⟨b, hbz, hb⟩ := hnb z (Finset.mem_of_mem_erase hz) (Finset.ne_of_mem_erase hz)
    exact ⟨a, b, hdist hay hbz hyz, ha, hb, Or.inl (hlmem hl)⟩
  · -- three neighbours, none of them `l`
    have hcard : 2 < (neighbors T i).card := by omega
    obtain ⟨y, z, u, hy, hz, hu, hyz, hyu, hzu⟩ := Finset.two_lt_card_iff.mp hcard
    obtain ⟨a, hay, ha⟩ := hnb y hy (fun h => hl (h ▸ hy))
    obtain ⟨b, hbz, hb⟩ := hnb z hz (fun h => hl (h ▸ hz))
    obtain ⟨c, hcu, hc⟩ := hnb u hu (fun h => hl (h ▸ hu))
    exact ⟨a, b, hdist hay hbz hyz, ha, hb,
      Or.inr ⟨c, hdist hcu hay hyu.symm, hdist hcu hbz hzu.symm, hc⟩⟩

end NumericalType

end AlgebraicGeometry
