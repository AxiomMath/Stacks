module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneConfiguration
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.GenusBound
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.ProperSubgraph.FiveChain

/-!
# Minimal numerical types of genus one whose components all meet two others

A minimal numerical type of genus one has topological genus at most one, so it has at most as
many edges as components. If in addition every component meets at least two others, the degree
sum forces every component to meet exactly two others, and the type is a cycle.

This file carries out that reduction and then identifies the cycle: for five or more components
the weights along the cycle are all equal, the intersection numbers along the cycle are all
equal to that common weight, and the multiplicities are all equal. That is case (16) of the
source's list for five components and the `n`-cycle family, case (25), for six or more — and
unlike the component-by-component classification of the preceding file, it holds for every
number of components at once.

The reduction to a cycle is a count. The topological genus `1 - n + e` of a minimal numerical
type is at most its genus, so a minimal type of genus one has `e ≤ n`; the degrees sum to `2e`,
so if every degree is at least two then every degree is exactly two. A connected graph all of
whose degrees are two is a cycle, and the spanning chain produced by the classification of
subgraphs, together with the degree count, exhibits the cyclic order.

The weights are pinned down by looking at five consecutive components. They are a *proper*
chain, so the classification of proper chains of five minus-two indices applies to them: up to
reordering they are of type `A₅`, `C₅` or `B₅`. In the last two cases exactly one of the five
weights differs from the other four, and the component carrying it meets only one other
component of the chain, so it sits at an end of the chain. Hence the three interior weights of
any five consecutive components agree, and since every pair of adjacent components lies in the
interior of such a window, all the weights agree. With five components exactly there is no room
for a five-window; four consecutive components are used instead, their classification is of
type `A₄`, `C₄`, `B₄` or `F₄`, the reordering is the identity or the reversal because the four
lie on a chain, and each of the seven resulting weight patterns changes weight across at most
one of the three adjacent pairs — which around a cycle of length five forces no change at all.

With the weights constant, each intersection number along the cycle is the larger of its two
endpoint weights, hence the common weight; the balance relation then reads
`2mᵢ = mᵢ₋₁ + mᵢ₊₁`, so the multiplicities form an arithmetic progression, and a progression
that closes up around the cycle is constant.

## Main results

* `AlgebraicGeometry.NumericalType.edgeCount_le_componentCount_of_isMinimal_of_genus_eq_one` —
  a minimal numerical type of genus one has at most as many edges as components.
* `AlgebraicGeometry.NumericalType.exists_cyclic_ordering` — a numerical type each of whose
  components meets exactly two others is a cycle.
* `AlgebraicGeometry.NumericalType.isGenusOneConfiguration_of_two_le_neighborCount` — a minimal
  numerical type of genus one with at least five components, each meeting at least two others,
  is the cycle configuration.
* `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_two_le_neighborCount` —
  the resulting two-sided statement.
* `AlgebraicGeometry.NumericalType.exists_dynkinConfiguration_of_erase_leaf` — the reduction
  for the complementary case: deleting a component that meets exactly one other leaves a
  connected proper set of minus-two indices, hence a Dynkin configuration on one fewer
  component.
* `AlgebraicGeometry.NumericalType.isGenusOneConfiguration_or_exists_dynkin_erase_leaf` — the
  resulting dichotomy for five or more components.
* `AlgebraicGeometry.NumericalType.weight_interior_eq_of_five_window` and
  `AlgebraicGeometry.NumericalType.weight_pattern_of_four_window` — the two window lemmas
  bounding the weights of five, resp. four, consecutive minus-two indices. Neither is specific
  to a cycle: both apply to any window of consecutive components of a configuration in which
  consecutive components meet and non-consecutive ones do not.

## Implementation notes

The hypothesis of `isGenusOneConfiguration_of_two_le_neighborCount` is the only one left to
remove. Its complement is the case in which some component meets exactly one other; there
`exists_dynkinConfiguration_of_erase_leaf` reduces to a Dynkin configuration on one fewer
component, and the enumeration of the ways the deleted component can be attached to each Dynkin
diagram — the affine extensions, cases (17)-(24) and (26)-(34) of the source's list — is carried
out in `StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneChain.lean` and in
`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneForkClassification.lean`. That reduction does
*not*
need the strict properness hypothesis `k < T.componentCount` of
`AlgebraicGeometry.NumericalType.no_positive_supported_kernel`, which indeed fails for the full
index set: deleting a component leaves `T.componentCount - 1` of them, which is proper.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

/-! ### The edge bound -/

/-- A minimal numerical type of genus one with more than one component has at most as many
edges as it has components: its topological genus is at most its genus. -/
public lemma edgeCount_le_componentCount_of_isMinimal_of_genus_eq_one (T : NumericalType)
    (hmin : IsMinimal T) (hgenus : genus T = 1) (hn : 1 < T.componentCount) :
    edgeCount T ≤ T.componentCount := by
  have h := one_sub_componentCount_add_edgeCount_le_genus_of_isMinimal T hmin hn
  rw [hgenus] at h
  omega

/-- In a minimal numerical type of genus one each of whose components meets at least two
others, every component meets exactly two others. -/
public lemma neighborCount_eq_two_of_two_le_neighborCount (T : NumericalType)
    (hmin : IsMinimal T) (hgenus : genus T = 1) (hn : 1 < T.componentCount)
    (hdeg : ∀ i, 2 ≤ neighborCount T i) (i : Fin T.componentCount) :
    neighborCount T i = 2 := by
  have hsum := sum_neighborCount_eq_two_edgeCount T
  have hle := edgeCount_le_componentCount_of_isMinimal_of_genus_eq_one T hmin hgenus hn
  by_contra hne
  have hi := hdeg i
  have hi' : 2 < neighborCount T i := by omega
  have hlt : ∑ _j : Fin T.componentCount, 2 < ∑ j, neighborCount T j :=
    Finset.sum_lt_sum (fun j _ => hdeg j) ⟨i, Finset.mem_univ i, hi'⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
  omega

/-! ### Membership in the neighbour set -/

/-- A component lies in the neighbour set of another exactly when the two are distinct and
meet. -/
public lemma mem_neighbors_iff (T : NumericalType) (i j : Fin T.componentCount) :
    j ∈ neighbors T i ↔ i ≠ j ∧ T.intersection i j ≠ 0 := by
  classical
  simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun h => ⟨h.1, by omega⟩, fun h => ⟨h.1, ?_⟩⟩
  exact lt_of_le_of_ne (T.intersection_nonneg i j h.1) (Ne.symm h.2)

/-! ### Connectedness of the whole component set -/

/-- The full set of components of a numerical type is connected in the sense used by the
classification of subgraphs. -/
public lemma univ_connected (T : NumericalType) :
    ¬ ∃ J : Finset (Fin T.componentCount),
      J.Nonempty ∧ J ⊂ Finset.univ ∧
        (∀ i ∈ J, ∀ j ∈ (Finset.univ : Finset (Fin T.componentCount)), j ∉ J →
          T.intersection i j = 0) := by
  rintro ⟨J, hne, hproper, hcut⟩
  obtain ⟨y, -, hyJ⟩ := Finset.exists_of_ssubset hproper
  refine T.connected ⟨(J : Set (Fin T.componentCount)), Finset.coe_nonempty.mpr hne, ?_, ?_⟩
  · intro h
    exact hyJ (by simpa using (h ▸ Set.mem_univ y : y ∈ (J : Set (Fin T.componentCount))))
  · intro i hi j hj
    exact hcut i (by simpa using hi) j (Finset.mem_univ j) (by simpa using hj)

/-! ### The cyclic ordering -/

/-- A chain through all the components: if every component meets at most two others, the
components can be listed injectively so that consecutive entries meet. -/
private lemma exists_spanning_chain_univ (T : NumericalType) (hn : 2 ≤ T.componentCount)
    (hdeg : ∀ i, (neighbors T i).card ≤ 2) :
    ∃ v : Fin T.componentCount → Fin T.componentCount, Function.Injective v ∧
      ∀ a b : Fin T.componentCount, b.val = a.val + 1 →
        T.intersection (v a) (v b) ≠ 0 := by
  classical
  have hdeg2 : ∀ x : {i // i ∈ (Finset.univ : Finset (Fin T.componentCount))},
      ((minusTwoGraph T Finset.univ).neighborSet x).ncard ≤ 2 := by
    intro x
    have hsub : (Subtype.val '' ((minusTwoGraph T Finset.univ).neighborSet x))
        ⊆ (neighbors T x.val : Set (Fin T.componentCount)) := by
      rintro y ⟨z, hz, rfl⟩
      simpa using (mem_neighbors_iff T x.val z.val).mpr hz
    calc ((minusTwoGraph T Finset.univ).neighborSet x).ncard
        = (Subtype.val '' ((minusTwoGraph T Finset.univ).neighborSet x)).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ ((neighbors T x.val : Finset (Fin T.componentCount)) :
            Set (Fin T.componentCount)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = (neighbors T x.val).card := Set.ncard_coe_finset _
      _ ≤ 2 := hdeg x.val
  obtain ⟨u, huinj, -, huadj⟩ :=
    exists_spanning_chain_of_degree_le_two T Finset.univ
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega) (univ_connected T) hdeg2
  have hlt : ∀ a : Fin T.componentCount,
      a.val < (Finset.univ : Finset (Fin T.componentCount)).card := fun a => by simp
  refine ⟨fun a => u ⟨a.val, hlt a⟩, ?_, ?_⟩
  · exact fun a b h => Fin.ext (Fin.mk_eq_mk.mp (huinj h))
  · exact fun a b hab => huadj _ _ hab

/-- Reading the successor of a residue modulo the number of components. -/
private lemma mod_succ_eq_iff (T : NumericalType) (x y : ℕ)
    (hx : x < T.componentCount) (hy : y < T.componentCount) :
    (x + 1) % T.componentCount = y ↔
      (x + 1 = y ∨ (x + 1 = T.componentCount ∧ y = 0)) := by
  by_cases h : x + 1 < T.componentCount
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [show x + 1 = T.componentCount by omega, Nat.mod_self]
    omega

/-- Two known neighbours exhaust the neighbours of a component that meets at most two others. -/
private lemma neighbours_exhausted (T : NumericalType)
    (hdeg : ∀ i, (neighbors T i).card ≤ 2)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (a x y z : Fin T.componentCount) (hxa : x ≠ a) (hya : y ≠ a) (hxy : x ≠ y)
    (hx : T.intersection (v a) (v x) ≠ 0) (hy : T.intersection (v a) (v y) ≠ 0)
    (hza : z ≠ a) (hz : T.intersection (v a) (v z) ≠ 0) : z = x ∨ z = y := by
  classical
  have hmem : ∀ p q : Fin T.componentCount, p ≠ q →
      (T.intersection (v p) (v q) ≠ 0 ↔ v q ∈ neighbors T (v p)) := by
    intro p q hpq
    rw [mem_neighbors_iff]
    exact ⟨fun h => ⟨hvinj.ne hpq, h⟩, fun h => h.2⟩
  have hsub : ({v x, v y} : Finset (Fin T.componentCount)) ⊆ neighbors T (v a) := by
    intro ww hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact (hmem a x (Ne.symm hxa)).mp hx
    · rw [Finset.mem_singleton] at hw
      subst hw
      exact (hmem a y (Ne.symm hya)).mp hy
  have hcard : (neighbors T (v a)).card ≤
      ({v x, v y} : Finset (Fin T.componentCount)).card := by
    rw [Finset.card_pair (hvinj.ne hxy)]
    exact hdeg (v a)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hzmem : v z ∈ ({v x, v y} : Finset (Fin T.componentCount)) :=
    heq ▸ (hmem a z (Ne.symm hza)).mp hz
  rcases Finset.mem_insert.mp hzmem with h | h
  · exact Or.inl (hvinj h)
  · exact Or.inr (hvinj (Finset.mem_singleton.mp h))

/-- An interior position of a chain through all the components, in a numerical type each of
whose components meets at most two others, has exactly its two chain neighbours. -/
private lemma chain_interior_neighbours (T : NumericalType)
    (hdeg : ∀ i, (neighbors T i).card ≤ 2)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hvadj : ∀ a b : Fin T.componentCount, b.val = a.val + 1 →
      T.intersection (v a) (v b) ≠ 0)
    (a b : Fin T.componentCount) (ha0 : 0 < a.val)
    (ha1 : a.val + 1 < T.componentCount) (hba : b ≠ a)
    (hb : T.intersection (v a) (v b) ≠ 0) :
    b.val + 1 = a.val ∨ a.val + 1 = b.val := by
  obtain ⟨am, hamv⟩ : ∃ am : Fin T.componentCount, am.val = a.val - 1 :=
    ⟨⟨a.val - 1, by omega⟩, rfl⟩
  obtain ⟨ap, hapv⟩ : ∃ ap : Fin T.componentCount, ap.val = a.val + 1 :=
    ⟨⟨a.val + 1, ha1⟩, rfl⟩
  have hama : am ≠ a := Fin.ne_of_val_ne (by omega)
  have hapa : ap ≠ a := Fin.ne_of_val_ne (by omega)
  have hamap : am ≠ ap := Fin.ne_of_val_ne (by omega)
  have hx : T.intersection (v a) (v am) ≠ 0 := by
    rw [T.intersection_symm]
    exact hvadj am a (by omega)
  have hy : T.intersection (v a) (v ap) ≠ 0 := hvadj a ap (by omega)
  rcases neighbours_exhausted T hdeg v hvinj a am ap b hama hapa hamap hx hy hba hb with h | h
  · exact Or.inl (by rw [h, hamv]; omega)
  · exact Or.inr (by rw [h, hapv])

/-- In a chain through all the components of a numerical type each of whose components meets
exactly two others, the two ends of the chain meet. -/
private lemma chain_ends_meet_of_neighborCount_eq_two (T : NumericalType)
    (hn : 3 ≤ T.componentCount) (hdeg : ∀ i, (neighbors T i).card = 2)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hvadj : ∀ a b : Fin T.componentCount, b.val = a.val + 1 →
      T.intersection (v a) (v b) ≠ 0)
    (i0 iL : Fin T.componentCount) (hi0 : i0.val = 0) (hiL : iL.val = T.componentCount - 1) :
    T.intersection (v i0) (v iL) ≠ 0 := by
  classical
  have hvsurj : Function.Surjective v := Finite.injective_iff_surjective.mp hvinj
  have hinterior := chain_interior_neighbours T (fun i => (hdeg i).le) v hvinj hvadj
  obtain ⟨i1, hi1⟩ : ∃ i1 : Fin T.componentCount, i1.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hsub : ({v i1} : Finset (Fin T.componentCount)) ⊆ neighbors T (v i0) := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact (mem_neighbors_iff T _ _).mpr
      ⟨hvinj.ne (Fin.ne_of_val_ne (by omega)), hvadj i0 i1 (by omega)⟩
  have hne : ({v i1} : Finset (Fin T.componentCount)) ≠ neighbors T (v i0) := by
    intro h
    have hc := congrArg Finset.card h
    rw [Finset.card_singleton, hdeg] at hc
    omega
  obtain ⟨x, hxmem, hxnot⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  obtain ⟨cz, rfl⟩ := hvsurj x
  rw [mem_neighbors_iff] at hxmem
  have hcz1 : cz ≠ i1 := by
    intro h
    exact hxnot (by rw [h]; exact Finset.mem_singleton_self _)
  have hcz0 : cz ≠ i0 := fun h => hxmem.1 (by rw [h])
  have hczlast : cz.val = T.componentCount - 1 := by
    by_contra hne'
    have hb0 : 0 < cz.val := Nat.pos_of_ne_zero fun h => hcz0 (Fin.ext (h.trans hi0.symm))
    have hsym : T.intersection (v cz) (v i0) ≠ 0 := by
      rw [T.intersection_symm]
      exact hxmem.2
    rcases hinterior cz i0 hb0 (by have := cz.isLt; omega) (fun h => hcz0 h.symm) hsym with
      h | h
    · omega
    · exact hcz1 (Fin.ext (by omega))
  rw [← (Fin.ext (by omega) : cz = iL)]
  exact hxmem.2

/-- In a chain through all the components of a numerical type, each of whose components meets
at most two others and whose two ends meet, two positions meet exactly when they agree or are
cyclically adjacent. -/
private lemma chain_intersection_ne_zero_iff_of_ends_meet (T : NumericalType)
    (hn : 3 ≤ T.componentCount) (hdeg : ∀ i, (neighbors T i).card ≤ 2)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hvadj : ∀ a b : Fin T.componentCount, b.val = a.val + 1 →
      T.intersection (v a) (v b) ≠ 0)
    (i0 iL : Fin T.componentCount) (hi0 : i0.val = 0) (hiL : iL.val = T.componentCount - 1)
    (hclose : T.intersection (v i0) (v iL) ≠ 0) (a b : Fin T.componentCount) :
    T.intersection (v a) (v b) ≠ 0 ↔
      (b.val + 1 = a.val ∨ a.val + 1 = b.val ∨
        (a.val = 0 ∧ b.val + 1 = T.componentCount) ∨
        (b.val = 0 ∧ a.val + 1 = T.componentCount) ∨ a.val = b.val) := by
  have hdiag : ∀ i, T.intersection i i ≠ 0 := fun i =>
    ne_of_lt (intersection_self_neg_of_one_lt_componentCount T (by omega) i)
  have hclosed := neighbours_exhausted T hdeg v hvinj
  obtain ⟨i1, hi1⟩ : ∃ i1 : Fin T.componentCount, i1.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨iM, hiM⟩ : ∃ iM : Fin T.componentCount, iM.val = T.componentCount - 2 :=
    ⟨⟨T.componentCount - 2, by omega⟩, rfl⟩
  by_cases hab : a.val = b.val
  · rw [Fin.ext hab]
    exact iff_of_true (hdiag (v b)) (by omega)
  have habne : a ≠ b := fun h => hab (congrArg Fin.val h)
  have hbLt := b.isLt
  have haLt := a.isLt
  constructor
  · intro hint
    rcases Nat.eq_zero_or_pos a.val with ha0 | ha0
    · have hae : a = i0 := Fin.ext (by omega)
      subst hae
      rcases hclosed a i1 iL b (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) (hvadj a i1 (by omega)) hclose (Ne.symm habne) hint with
        rfl | rfl <;> omega
    · by_cases ha1 : a.val + 1 < T.componentCount
      · rcases chain_interior_neighbours T hdeg v hvinj hvadj a b ha0 ha1 (Ne.symm habne)
          hint with h | h <;> omega
      · have hae : a = iL := Fin.ext (by omega)
        subst hae
        have hx : T.intersection (v a) (v iM) ≠ 0 := by
          rw [T.intersection_symm]
          exact hvadj iM a (by omega)
        have hy : T.intersection (v a) (v i0) ≠ 0 := by
          rw [T.intersection_symm]
          exact hclose
        rcases hclosed a iM i0 b (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega)) hx hy (Ne.symm habne) hint with rfl | rfl <;> omega
  · rintro (h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h)
    · rw [T.intersection_symm]
      exact hvadj b a h.symm
    · exact hvadj a b h.symm
    · rw [(Fin.ext (by omega) : a = i0), (Fin.ext (by omega) : b = iL)]
      exact hclose
    · rw [(Fin.ext (by omega) : a = iL), (Fin.ext (by omega) : b = i0), T.intersection_symm]
      exact hclose
    · exact absurd h hab

/-- The components of a numerical type with at least three components, each meeting exactly
two others, can be listed cyclically: there is a periodic enumeration of all the components in
which two of them meet exactly when their positions agree or are cyclically adjacent. -/
public lemma exists_cyclic_ordering (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hdeg : ∀ i, neighborCount T i = 2) :
    ∃ c : ℕ → Fin T.componentCount,
      (∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount]) ∧
      (∀ i, ∃ k, c k = i) ∧
      (∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
        (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
          k ≡ l [MOD T.componentCount])) := by
  classical
  have hpos : 0 < T.componentCount := by omega
  have hdegc : ∀ i, (neighbors T i).card = 2 := fun i => hdeg i
  obtain ⟨v, hvinj, hvadj⟩ :=
    exists_spanning_chain_univ T (by omega) (fun i => (hdegc i).le)
  have hvsurj : Function.Surjective v := Finite.injective_iff_surjective.mp hvinj
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin T.componentCount, i0.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨iL, hiL⟩ : ∃ iL : Fin T.componentCount, iL.val = T.componentCount - 1 :=
    ⟨⟨T.componentCount - 1, by omega⟩, rfl⟩
  have hclose :=
    chain_ends_meet_of_neighborCount_eq_two T hn hdegc v hvinj hvadj i0 iL hi0 hiL
  have hchar : ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
      ((a.val + 1) % T.componentCount = b.val ∨
        (b.val + 1) % T.componentCount = a.val ∨ a.val = b.val) := by
    intro a b
    rw [chain_intersection_ne_zero_iff_of_ends_meet T hn (fun i => (hdegc i).le) v hvinj hvadj
        i0 iL hi0 hiL hclose a b,
      mod_succ_eq_iff T a.val b.val a.isLt b.isLt,
      mod_succ_eq_iff T b.val a.val b.isLt a.isLt]
    have haLt := a.isLt
    have hbLt := b.isLt
    omega
  refine ⟨fun k => v ⟨k % T.componentCount, Nat.mod_lt _ hpos⟩,
    fun k l => ⟨fun h => congrArg Fin.val (hvinj h), fun h => congrArg v (Fin.ext h)⟩, ?_, ?_⟩
  · intro i
    obtain ⟨a, rfl⟩ := hvsurj i
    exact ⟨a.val, congrArg v (Fin.ext (by simp [Nat.mod_eq_of_lt a.isLt]))⟩
  · intro k l
    rw [hchar]
    change _ ↔ ((k + 1) % T.componentCount = l % T.componentCount ∨
      (l + 1) % T.componentCount = k % T.componentCount ∨
      k % T.componentCount = l % T.componentCount)
    simp only [Nat.mod_add_mod]

/-! ### The path ordering -/

/-- In a chain through all the components of a numerical type, each of whose components meets
at most two others and one of which meets fewer, the two ends of the chain do not meet. -/
private lemma chain_ends_not_meet_of_exists_neighborCount_lt_two (T : NumericalType)
    (hn : 3 ≤ T.componentCount) (hsmall : ∃ i, neighborCount T i < 2)
    (v : Fin T.componentCount → Fin T.componentCount) (hvinj : Function.Injective v)
    (hvadj : ∀ a b : Fin T.componentCount, b.val = a.val + 1 →
      T.intersection (v a) (v b) ≠ 0)
    (i0 iL : Fin T.componentCount) (hi0 : i0.val = 0) (hiL : iL.val = T.componentCount - 1) :
    T.intersection (v i0) (v iL) = 0 := by
  classical
  -- two distinct neighbours of a component force its degree to be two
  have hpair : ∀ a p q : Fin T.componentCount, p ≠ a → q ≠ a → p ≠ q →
      T.intersection (v a) (v p) ≠ 0 → T.intersection (v a) (v q) ≠ 0 →
      2 ≤ neighborCount T (v a) := by
    intro a p q hpa hqa hpq hp hq
    have hmp : v p ∈ neighbors T (v a) :=
      (mem_neighbors_iff T (v a) (v p)).mpr ⟨hvinj.ne (Ne.symm hpa), hp⟩
    have hmq : v q ∈ neighbors T (v a) :=
      (mem_neighbors_iff T (v a) (v q)).mpr ⟨hvinj.ne (Ne.symm hqa), hq⟩
    exact Finset.one_lt_card.mpr ⟨v p, hmp, v q, hmq, hvinj.ne hpq⟩
  -- the two ends of the chain are not joined
  by_contra hcon
  obtain ⟨i, hi⟩ := hsmall
  obtain ⟨a, rfl⟩ := (Finite.injective_iff_surjective.mp hvinj : Function.Surjective v) i
  have haLt := a.isLt
  have htwo : 2 ≤ neighborCount T (v a) := by
    by_cases ha0 : a.val = 0
    · obtain ⟨i1, hi1⟩ : ∃ i1 : Fin T.componentCount, i1.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
      rw [(Fin.ext (by omega) : a = i0)]
      exact hpair i0 i1 iL (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) (hvadj i0 i1 (by omega)) hcon
    · by_cases ha1 : a.val + 1 < T.componentCount
      · obtain ⟨am, hamv⟩ : ∃ am : Fin T.componentCount, am.val = a.val - 1 :=
          ⟨⟨a.val - 1, by omega⟩, rfl⟩
        obtain ⟨ap, hapv⟩ : ∃ ap : Fin T.componentCount, ap.val = a.val + 1 :=
          ⟨⟨a.val + 1, ha1⟩, rfl⟩
        refine hpair a am ap (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega)) ?_ (hvadj a ap (by omega))
        rw [T.intersection_symm]
        exact hvadj am a (by omega)
      · obtain ⟨iM, hiM⟩ : ∃ iM : Fin T.componentCount, iM.val = T.componentCount - 2 :=
          ⟨⟨T.componentCount - 2, by omega⟩, rfl⟩
        rw [(Fin.ext (by omega) : a = iL)]
        refine hpair iL iM i0 (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega)) ?_ ?_
        · rw [T.intersection_symm]
          exact hvadj iM iL (by omega)
        · rw [T.intersection_symm]
          exact hcon
  omega

/-- The components of a numerical type with at least three components, each meeting at most two
others and at least one meeting fewer, can be listed as a chain: two of them meet exactly when
their positions agree or are consecutive. The ends of the chain are not joined, since otherwise
every component would meet exactly two others. -/
public lemma exists_path_ordering (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hdeg : ∀ i, neighborCount T i ≤ 2) (hsmall : ∃ i, neighborCount T i < 2) :
    ∃ v : Fin T.componentCount → Fin T.componentCount, Function.Injective v ∧
      (∀ i, ∃ a, v a = i) ∧
      ∀ a b : Fin T.componentCount, T.intersection (v a) (v b) ≠ 0 ↔
        (a.val + 1 = b.val ∨ b.val + 1 = a.val ∨ a = b) := by
  classical
  have hdeg' : ∀ i, (neighbors T i).card ≤ 2 := hdeg
  have hdiag : ∀ i, T.intersection i i ≠ 0 := fun i =>
    ne_of_lt (intersection_self_neg_of_one_lt_componentCount T (by omega) i)
  obtain ⟨v, hvinj, hvadj⟩ := exists_spanning_chain_univ T (by omega) hdeg'
  have hvsurj : Function.Surjective v := Finite.injective_iff_surjective.mp hvinj
  have hinterior := chain_interior_neighbours T hdeg' v hvinj hvadj
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin T.componentCount, i0.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨iL, hiL⟩ : ∃ iL : Fin T.componentCount, iL.val = T.componentCount - 1 :=
    ⟨⟨T.componentCount - 1, by omega⟩, rfl⟩
  have hopen := chain_ends_not_meet_of_exists_neighborCount_lt_two T hn hsmall v hvinj hvadj
    i0 iL hi0 hiL
  refine ⟨v, hvinj, fun i => hvsurj i, fun a b => ?_⟩
  by_cases hab : a = b
  · subst hab
    exact iff_of_true (hdiag (v a)) (Or.inr (Or.inr rfl))
  constructor
  · intro hint
    by_cases ha : 0 < a.val ∧ a.val + 1 < T.componentCount
    · rcases hinterior a b ha.1 ha.2 (Ne.symm hab) hint with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · by_cases hb : 0 < b.val ∧ b.val + 1 < T.componentCount
      · rcases hinterior b a hb.1 hb.2 hab (by rwa [T.intersection_symm]) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exfalso
        have haLt := a.isLt
        have hbLt := b.isLt
        have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
        obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ : (a.val = 0 ∧ b.val = T.componentCount - 1) ∨
            (b.val = 0 ∧ a.val = T.componentCount - 1) := by omega
        · rw [(Fin.ext (by omega) : a = i0), (Fin.ext (by omega) : b = iL)] at hint
          exact hint hopen
        · rw [(Fin.ext (by omega) : a = iL), (Fin.ext (by omega) : b = i0),
            T.intersection_symm] at hint
          exact hint hopen
  · rintro (h | h | h)
    · exact hvadj a b h.symm
    · rw [T.intersection_symm]
      exact hvadj b a h.symm
    · exact absurd h hab

/-! ### Weights along the cycle -/

/-- A constant five-term vector. -/
private lemma vec5_const {R : Type*} (a : R) (r : Fin 5) :
    (![a, a, a, a, a] : Fin 5 → R) r = a := by
  fin_cases r <;> simp

/-- A five-term vector constant away from its last entry. -/
private lemma vec5_eq_of_ne_four {R : Type*} (a b : R) (r : Fin 5) (hr : r.val ≠ 4) :
    (![a, a, a, a, b] : Fin 5 → R) r = a := by
  fin_cases r <;> simp_all

/-- If the last vertex of a Dynkin ordering of five consecutive components of a cycle meets
only the fourth, then it is an end of the window: an interior position of the window meets two
of the other four. -/
private lemma dynkin_last_is_window_end (T : NumericalType)
    (c : Fin 5 → Fin T.componentCount)
    (hadj : ∀ p q : Fin 5, T.intersection (c p) (c q) ≠ 0 ↔
      (p.val + 1 = q.val ∨ q.val + 1 = p.val ∨ p.val = q.val))
    (σ : Equiv.Perm (Fin 5))
    (h0 : T.intersection (c (σ 4)) (c (σ 0)) = 0)
    (h1 : T.intersection (c (σ 4)) (c (σ 1)) = 0)
    (h2 : T.intersection (c (σ 4)) (c (σ 2)) = 0) :
    (σ 4).val = 0 ∨ (σ 4).val = 4 := by
  by_contra hcon
  have hlt := (σ 4).isLt
  have hkey : ∀ q : Fin 5, T.intersection (c (σ 4)) (c q) ≠ 0 → q.val ≠ (σ 4).val →
      q = σ 3 := by
    intro q hq hqne
    obtain ⟨s, hs⟩ : ∃ s, σ s = q := ⟨σ.symm q, σ.apply_symm_apply q⟩
    have hs4 : s.val ≠ 4 := by
      intro h
      have : s = 4 := Fin.ext (by simpa using h)
      rw [this] at hs
      exact hqne (by rw [← hs])
    rw [← hs] at hq
    fin_cases s
    · exact absurd h0 hq
    · exact absurd h1 hq
    · exact absurd h2 hq
    · exact hs.symm
    · simp at hs4
  obtain ⟨pm, hpm⟩ : ∃ pm : Fin 5, pm.val = (σ 4).val - 1 := ⟨⟨(σ 4).val - 1, by omega⟩, rfl⟩
  obtain ⟨pp, hpp⟩ : ∃ pp : Fin 5, pp.val = (σ 4).val + 1 := ⟨⟨(σ 4).val + 1, by omega⟩, rfl⟩
  have hamp : T.intersection (c (σ 4)) (c pm) ≠ 0 :=
    (hadj (σ 4) pm).mpr (Or.inr (Or.inl (by omega)))
  have happ : T.intersection (c (σ 4)) (c pp) ≠ 0 :=
    (hadj (σ 4) pp).mpr (Or.inl (by omega))
  have hpm3 := hkey pm hamp (by omega)
  have hpp3 := hkey pp happ (by omega)
  have hpe : pm = pp := hpm3.trans hpp3.symm
  rw [hpe] at hpm
  omega

/-- Reading the weights of five components off a reordered weight vector `![a, a, a, a, b]`:
every component other than the one placed last has weight `a`. -/
private lemma weight_eq_of_vec5 (T : NumericalType) {c : Fin 5 → Fin T.componentCount}
    {σ : Equiv.Perm (Fin 5)} {a b : ℤ}
    (hwts : (fun r => T.weight (c (σ r))) = ![a, a, a, a, b])
    (q : Fin 5) (hq : q.val ≠ (σ 4).val) : T.weight (c q) = a := by
  have hne : (σ.symm q).val ≠ 4 := by
    intro h
    have h4 : σ.symm q = 4 := Fin.ext (by simpa using h)
    have hq4 : q = σ 4 := by rw [← h4, σ.apply_symm_apply]
    exact hq (congrArg Fin.val hq4)
  have hval := congrFun hwts (σ.symm q)
  rw [σ.apply_symm_apply] at hval
  rw [hval]
  exact vec5_eq_of_ne_four a b _ hne

/-- Reading the weights of five components off a reordered constant weight vector. -/
private lemma weight_eq_of_vec5_const (T : NumericalType) {c : Fin 5 → Fin T.componentCount}
    {σ : Equiv.Perm (Fin 5)} {a : ℤ}
    (hwts : (fun r => T.weight (c (σ r))) = ![a, a, a, a, a]) (q : Fin 5) :
    T.weight (c q) = a := by
  have hval := congrFun hwts (σ.symm q)
  rw [σ.apply_symm_apply] at hval
  rw [hval]
  exact vec5_const a _

/-- The three interior weights of five consecutive components of a cycle of minus-two indices
agree. The five form a proper chain, so up to reordering they are of type `A₅`, `C₅` or `B₅`;
in the last two cases exactly one of the five weights differs from the other four and the
component carrying it meets only one other component of the chain, hence is an end of the
window. -/
public lemma weight_interior_eq_of_five_window (T : NumericalType) (hn : 5 < T.componentCount)
    (c : Fin 5 → Fin T.componentCount) (hinj : Function.Injective c)
    (hminus : ∀ p, IsMinusTwoIndex T (c p))
    (hadj : ∀ p q : Fin 5, T.intersection (c p) (c q) ≠ 0 ↔
      (p.val + 1 = q.val ∨ q.val + 1 = p.val ∨ p.val = q.val)) :
    ∃ W : ℤ, 0 < W ∧ (∀ p : Fin 5, 1 ≤ p.val → p.val ≤ 3 → T.weight (c p) = W) ∧
      (T.weight (c 0) = W ∨ T.weight (c 0) = 2 * W ∨ 2 * T.weight (c 0) = W) ∧
      (T.weight (c 4) = W ∨ T.weight (c 4) = 2 * W ∨ 2 * T.weight (c 4) = W) := by
  classical
  have v0 : (0 : Fin 5).val = 0 := by decide
  have v4 : (4 : Fin 5).val = 4 := by decide
  obtain ⟨σ, w, hwpos, hcfg⟩ := five_chain_is_A5_or_C5_or_B5 T hn c hinj hminus
    (fun r => (hadj r.castSucc r.succ).mpr (Or.inl (by simp)))
  rcases hcfg with ⟨hwts, -⟩ | ⟨hwts, hmat, -⟩ | ⟨hwts, hmat, -⟩
  · have hall := weight_eq_of_vec5_const T (c := c) (σ := σ) (a := w) (by simpa using hwts)
    exact ⟨w, hwpos, fun p _ _ => hall p, Or.inl (hall 0), Or.inl (hall 4)⟩
  all_goals
    have hend := dynkin_last_is_window_end T c hadj σ
      (by simpa using congrFun (congrFun hmat 4) 0)
      (by simpa using congrFun (congrFun hmat 4) 1)
      (by simpa using congrFun (congrFun hmat 4) 2)
    -- the weight `b` sits at the end `σ 4` of the window, all other weights are `a`
    have key : ∀ a b : ℤ, 0 < a → (b = 2 * a ∨ 2 * b = a) →
        (fun r => T.weight (c (σ r))) = ![a, a, a, a, b] →
        ∃ W : ℤ, 0 < W ∧ (∀ p : Fin 5, 1 ≤ p.val → p.val ≤ 3 → T.weight (c p) = W) ∧
          (T.weight (c 0) = W ∨ T.weight (c 0) = 2 * W ∨ 2 * T.weight (c 0) = W) ∧
          (T.weight (c 4) = W ∨ T.weight (c 4) = 2 * W ∨ 2 * T.weight (c 4) = W) := by
      intro a b ha hb hwts'
      have hspec : T.weight (c (σ 4)) = b := by simpa using congrFun hwts' 4
      have hend' : ∀ e : Fin 5, (σ 4).val = e.val →
          T.weight (c e) = a ∨ T.weight (c e) = 2 * a ∨ 2 * T.weight (c e) = a := by
        intro e he
        rw [← Fin.ext he, hspec]
        omega
      refine ⟨a, ha, fun p hp1 hp3 => weight_eq_of_vec5 T hwts' p (by omega), ?_, ?_⟩
      · by_cases h0 : (σ 4).val = 0
        · exact hend' 0 h0
        · exact Or.inl (weight_eq_of_vec5 T hwts' 0 (by omega))
      · by_cases h4 : (σ 4).val = 4
        · exact hend' 4 h4
        · exact Or.inl (weight_eq_of_vec5 T hwts' 4 (by omega))
  · exact key w (2 * w) hwpos (Or.inl rfl) (by simpa using hwts)
  · exact key (2 * w) w (by omega) (Or.inr (by ring)) (by simpa using hwts)

/-- Reading a congruence between small residues. -/
private lemma modEq_iff_eq_of_lt {n x y : ℕ} (hx : x < n) (hy : y < n) :
    x ≡ y [MOD n] ↔ x = y := by
  unfold Nat.ModEq
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- A window of `t` consecutive components of a cycle of more than `t` components consists of
distinct components, and two of them meet exactly when their positions in the window are
adjacent. -/
private lemma window_data (T : NumericalType) {t : ℕ} (hn : t + 1 ≤ T.componentCount)
    (c : ℕ → Fin T.componentCount)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount])
    (hcadj : ∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
      (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
        k ≡ l [MOD T.componentCount]))
    (base : ℕ) :
    Function.Injective (fun p : Fin t => c (base + p.val)) ∧
      ∀ p q : Fin t, T.intersection (c (base + p.val)) (c (base + q.val)) ≠ 0 ↔
        (p.val + 1 = q.val ∨ q.val + 1 = p.val ∨ p.val = q.val) := by
  have key : ∀ x y : ℕ, x ≤ t → y ≤ t →
      (base + x ≡ base + y [MOD T.componentCount] ↔ x = y) := fun x y hx hy =>
    ⟨fun h => (modEq_iff_eq_of_lt (by omega) (by omega)).mp (Nat.ModEq.add_left_cancel' base h),
      fun h => h ▸ Nat.ModEq.refl _⟩
  have key' : ∀ x y : ℕ, x + 1 ≤ t → y ≤ t →
      (base + x + 1 ≡ base + y [MOD T.componentCount] ↔ x + 1 = y) := fun x y hx hy => by
    rw [Nat.add_assoc]
    exact key (x + 1) y hx hy
  refine ⟨fun p q h => Fin.ext ((key p q p.isLt.le q.isLt.le).mp ((hceq _ _).mp h)), fun p q => ?_⟩
  have hp := p.isLt
  have hq := q.isLt
  rw [hcadj, key' _ _ (by omega) (by omega), key' _ _ (by omega) (by omega),
    key _ _ (by omega) (by omega)]

/-- Shifting a position of a cycle by the number of components gives the same component. -/
private lemma cycle_apply_add_componentCount (T : NumericalType) (c : ℕ → Fin T.componentCount)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount]) (k : ℕ) :
    c (k + T.componentCount) = c k :=
  (hceq _ _).mpr (by unfold Nat.ModEq; exact Nat.add_mod_right k _)

/-- Adjacent components of a cycle of at least six minus-two indices have equal weights. -/
private lemma weight_eq_of_succ (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (c : ℕ → Fin T.componentCount)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount])
    (hcadj : ∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
      (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
        k ≡ l [MOD T.componentCount]))
    (k : ℕ) : T.weight (c k) = T.weight (c (k + 1)) := by
  obtain ⟨hinj, hadj⟩ := window_data T (t := 5) (by omega) c hceq hcadj
    (k + T.componentCount - 1)
  obtain ⟨W, -, hW, -, -⟩ := weight_interior_eq_of_five_window T (by omega)
    (fun p : Fin 5 => c (k + T.componentCount - 1 + p.val)) hinj (fun p => hminus _) hadj
  have e1 : c (k + T.componentCount - 1 + 1) = c k := by
    rw [show k + T.componentCount - 1 + 1 = k + T.componentCount by omega]
    exact cycle_apply_add_componentCount T c hceq k
  have e2 : c (k + T.componentCount - 1 + 2) = c (k + 1) := by
    rw [show k + T.componentCount - 1 + 2 = k + 1 + T.componentCount by omega]
    exact cycle_apply_add_componentCount T c hceq (k + 1)
  obtain ⟨p1, hp1⟩ : ∃ p : Fin 5, p.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨p2, hp2⟩ : ∃ p : Fin 5, p.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  have hw1 := hW p1 (by omega) (by omega)
  have hw2 := hW p2 (by omega) (by omega)
  rw [hp1, e1] at hw1
  rw [hp2, e2] at hw2
  rw [hw1, hw2]

/-- All the weights along a cycle of at least six minus-two indices agree. -/
private lemma weight_eq_zero_of_cycle (T : NumericalType) (hn : 6 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (c : ℕ → Fin T.componentCount)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount])
    (hcadj : ∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
      (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
        k ≡ l [MOD T.componentCount]))
    (k : ℕ) : T.weight (c k) = T.weight (c 0) := by
  induction k with
  | zero => rfl
  | succ j ih => exact (weight_eq_of_succ T hn hminus c hceq hcadj j).symm.trans ih

/-- Positions at cyclic distance one, two or none give distinct components when there are at
least three of them. -/
private lemma cycle_ne_of_small_offset (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (c : ℕ → Fin T.componentCount)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount])
    (k : ℕ) (a b : ℕ) (ha : a < 3) (hb : b < 3) (hab : a ≠ b) :
    c (k + a) ≠ c (k + b) := by
  rw [Ne, hceq]
  intro h
  have h' := Nat.ModEq.add_left_cancel' k (n := T.componentCount) (a := a) (b := b) h
  exact hab ((modEq_iff_eq_of_lt (by omega) (by omega)).mp h')

/-! ### Intersection numbers along the cycle -/

/-- The intersection number of two adjacent components of a cycle of at least six minus-two
indices is the common weight. -/
private lemma intersection_eq_weight_of_cycle (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (c : ℕ → Fin T.componentCount)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount])
    (hcadj : ∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
      (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
        k ≡ l [MOD T.componentCount]))
    (hWc : ∀ j, T.weight (c j) = T.weight (c 0))
    (k : ℕ) : T.intersection (c k) (c (k + 1)) = T.weight (c 0) := by
  have hne : c k ≠ c (k + 1) := by
    have h := cycle_ne_of_small_offset T (by omega) c hceq k 0 1 (by omega) (by omega)
      (by omega)
    simpa using h
  have hpos : 0 < T.intersection (c k) (c (k + 1)) :=
    lt_of_le_of_ne (T.intersection_nonneg _ _ hne)
      (Ne.symm ((hcadj k (k + 1)).mpr (Or.inl (Nat.ModEq.refl _))))
  rw [intersection_eq_max_weight_of_intersects T (by omega) _ _ (hminus _) (hminus _) hpos,
    hWc k, hWc (k + 1), max_self]

/-! ### Multiplicities along the cycle -/

/-- The balance relation at a component of a cycle of at least six minus-two indices: twice its
multiplicity is the sum of the multiplicities of its two neighbours. -/
private lemma multiplicity_balance_of_cycle (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (c : ℕ → Fin T.componentCount) (hsurj : ∀ i, ∃ k, c k = i)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount])
    (hcadj : ∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
      (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
        k ≡ l [MOD T.componentCount]))
    (hWc : ∀ j, T.weight (c j) = T.weight (c 0))
    (k : ℕ) :
    T.multiplicity (c k) + T.multiplicity (c (k + 2)) = 2 * T.multiplicity (c (k + 1)) := by
  classical
  have hW := hWc
  have hWpos : 0 < T.weight (c 0) := T.weight_pos _
  have h01 : c k ≠ c (k + 1) := by
    simpa using cycle_ne_of_small_offset T (by omega) c hceq k 0 1 (by omega) (by omega)
      (by omega)
  have h02 : c k ≠ c (k + 2) := by
    simpa using cycle_ne_of_small_offset T (by omega) c hceq k 0 2 (by omega) (by omega)
      (by omega)
  have h12 : c (k + 1) ≠ c (k + 2) :=
    cycle_ne_of_small_offset T (by omega) c hceq k 1 2 (by omega) (by omega) (by omega)
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin T.componentCount),
      S = {c k, c (k + 1), c (k + 2)} := ⟨_, rfl⟩
  have hmemS : ∀ x : Fin T.componentCount,
      (x = c k ∨ x = c (k + 1) ∨ x = c (k + 2)) → x ∈ S := by
    intro x hx
    rw [hS]
    rcases hx with h | h | h
    · rw [h]
      exact Finset.mem_insert_self _ _
    · rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [h]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hzero : ∀ x ∈ (Finset.univ : Finset (Fin T.componentCount)), x ∉ S →
      T.intersection (c (k + 1)) x * T.multiplicity x = 0 := by
    intro x _ hxS
    obtain ⟨l, rfl⟩ := hsurj x
    have hint : T.intersection (c (k + 1)) (c l) = 0 := by
      by_contra hcon
      rcases (hcadj (k + 1) l).mp hcon with h | h | h
      · refine hxS (hmemS _ (Or.inr (Or.inr ?_)))
        exact (hceq l (k + 2)).mpr (Nat.ModEq.symm (by simpa [Nat.add_assoc] using h))
      · refine hxS (hmemS _ (Or.inl ?_))
        exact (hceq l k).mpr (Nat.ModEq.add_right_cancel' 1 h)
      · refine hxS (hmemS _ (Or.inr (Or.inl ?_)))
        exact (hceq l (k + 1)).mpr (Nat.ModEq.symm h)
    rw [hint, zero_mul]
  have hsum : ∑ x ∈ S, T.intersection (c (k + 1)) x * T.multiplicity x = 0 := by
    rw [Finset.sum_subset (Finset.subset_univ S) hzero]
    exact T.intersection_mul_multiplicity (c (k + 1))
  rw [hS, Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
    Finset.sum_singleton] at hsum
  have he0 : T.intersection (c (k + 1)) (c k) = T.weight (c 0) := by
    rw [T.intersection_symm]
    exact intersection_eq_weight_of_cycle T hn hminus c hceq hcadj hWc k
  have he2 : T.intersection (c (k + 1)) (c (k + 2)) = T.weight (c 0) := by
    simpa [Nat.add_assoc] using
      intersection_eq_weight_of_cycle T hn hminus c hceq hcadj hWc (k + 1)
  have he1 : T.intersection (c (k + 1)) (c (k + 1)) = -2 * T.weight (c 0) := by
    rw [(hminus (c (k + 1))).2, hW (k + 1)]
  rw [he0, he1, he2] at hsum
  have hfac : T.weight (c 0) * (T.multiplicity (c k) + T.multiplicity (c (k + 2)) -
      2 * T.multiplicity (c (k + 1))) = 0 := by linarith
  rcases mul_eq_zero.mp hfac with h | h
  · omega
  · linarith

/-- All the multiplicities along a cycle of at least six minus-two indices agree: the balance
relation makes them an arithmetic progression, and the progression closes up. -/
private lemma multiplicity_eq_zero_of_cycle (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (c : ℕ → Fin T.componentCount) (hsurj : ∀ i, ∃ k, c k = i)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount])
    (hcadj : ∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
      (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
        k ≡ l [MOD T.componentCount]))
    (hWc : ∀ j, T.weight (c j) = T.weight (c 0))
    (k : ℕ) : T.multiplicity (c k) = T.multiplicity (c 0) := by
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = T.multiplicity (c 1) - T.multiplicity (c 0) := ⟨_, rfl⟩
  have hprog : ∀ j : ℕ, T.multiplicity (c j) = T.multiplicity (c 0) + (j : ℤ) * d ∧
      T.multiplicity (c (j + 1)) = T.multiplicity (c 0) + ((j : ℤ) + 1) * d := by
    intro j
    induction j with
    | zero =>
        refine ⟨by simp, ?_⟩
        rw [hd]
        norm_num
    | succ i ih =>
        refine ⟨by push_cast; exact ih.2, ?_⟩
        have hrec := multiplicity_balance_of_cycle T hn hminus c hsurj hceq hcadj hWc i
        have hval : T.multiplicity (c (i + 2)) =
            T.multiplicity (c 0) + ((i : ℤ) + 2) * d := by
          have h1 := ih.1
          have h2 := ih.2
          linarith
        rw [show i + 1 + 1 = i + 2 from by omega, hval]
        push_cast
        ring
  have hcycle : T.multiplicity (c T.componentCount) = T.multiplicity (c 0) := by
    rw [← zero_add T.componentCount, cycle_apply_add_componentCount T c hceq 0]
  have hnd : (T.componentCount : ℤ) * d = 0 := by
    have h := (hprog T.componentCount).1
    linarith
  have hdz : d = 0 := by
    rcases mul_eq_zero.mp hnd with h | h
    · exact absurd h (by omega)
    · exact h
  have h := (hprog k).1
  rw [hdz] at h
  linarith

/-! ### The five-component cycle -/

/-- A constant four-term vector. -/
private lemma vec4_const {R : Type*} (a : R) (r : Fin 4) :
    (![a, a, a, a] : Fin 4 → R) r = a := by
  fin_cases r <;> simp

/-- The entries of a four-term vector. -/
private lemma vec4_vals (a b d e : ℤ) (r : Fin 4) :
    (![a, b, d, e] : Fin 4 → ℤ) r = a ∨ (![a, b, d, e] : Fin 4 → ℤ) r = b ∨
      (![a, b, d, e] : Fin 4 → ℤ) r = d ∨ (![a, b, d, e] : Fin 4 → ℤ) r = e := by
  fin_cases r <;> simp

/-- A permutation of four points taking consecutive pairs to consecutive pairs is the identity
or the reversal: those are the only two orderings of a four-vertex chain. -/
private lemma perm_four_of_preserves_chain (σ : Equiv.Perm (Fin 4))
    (h : ∀ p q : Fin 4, p.val + 1 = q.val →
      ((σ p).val + 1 = (σ q).val ∨ (σ q).val + 1 = (σ p).val)) :
    (∀ p : Fin 4, (σ p).val = p.val) ∨ (∀ p : Fin 4, (σ p).val + p.val = 3) := by
  revert σ
  decide

/-- A reordering of four consecutive components of a chain under which the reordered
consecutive pairs still meet is the identity or the reversal. -/
private lemma perm_four_of_intersections (T : NumericalType)
    (cw : Fin 4 → Fin T.componentCount)
    (hadj : ∀ p q : Fin 4, T.intersection (cw p) (cw q) ≠ 0 ↔
      (p.val + 1 = q.val ∨ q.val + 1 = p.val ∨ p.val = q.val))
    (σ : Equiv.Perm (Fin 4)) (A : Fin 4 → Fin 4 → ℤ)
    (hmat : (fun p q => T.intersection (cw (σ p)) (cw (σ q))) = A)
    (h01 : A 0 1 ≠ 0) (h12 : A 1 2 ≠ 0) (h23 : A 2 3 ≠ 0) :
    (∀ p : Fin 4, (σ p).val = p.val) ∨ (∀ p : Fin 4, (σ p).val + p.val = 3) := by
  have hchain : ∀ p q : Fin 4, p.val + 1 = q.val →
      T.intersection (cw (σ p)) (cw (σ q)) ≠ 0 := by
    intro p q hpq
    have hq := q.isLt
    have hA : T.intersection (cw (σ p)) (cw (σ q)) = A p q := congrFun (congrFun hmat p) q
    rw [hA]
    have hp3 : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 := by omega
    rcases hp3 with h | h | h
    · rw [show p = 0 from Fin.ext (by omega), show q = 1 from Fin.ext (by omega)]
      exact h01
    · rw [show p = 1 from Fin.ext (by omega), show q = 2 from Fin.ext (by omega)]
      exact h12
    · rw [show p = 2 from Fin.ext (by omega), show q = 3 from Fin.ext (by omega)]
      exact h23
  refine perm_four_of_preserves_chain σ fun p q hpq => ?_
  have hpqne : p ≠ q := by
    intro h
    rw [h] at hpq
    omega
  have hσne : (σ p).val ≠ (σ q).val := fun h => hpqne (σ.injective (Fin.ext h))
  have hc := (hadj (σ p) (σ q)).mp (hchain p q hpq)
  omega

/-- Reading the weight of one of four components off a reordered weight vector. -/
private lemma weight_mem_of_vec4 (T : NumericalType) {cw : Fin 4 → Fin T.componentCount}
    {σ : Equiv.Perm (Fin 4)} {a b d e : ℤ}
    (hw : (fun p => T.weight (cw (σ p))) = ![a, b, d, e]) (q : Fin 4) :
    T.weight (cw q) = a ∨ T.weight (cw q) = b ∨ T.weight (cw q) = d ∨ T.weight (cw q) = e := by
  have hval := congrFun hw (σ.symm q)
  simp only [Equiv.apply_symm_apply] at hval
  rw [hval]
  exact vec4_vals a b d e _

/-- Under the identity or the reversal, a weight vector `![a, b, d, e]` with at most one change
of weight, of the shape `a = b = d` or `a = b, d = e`, gives four consecutive components at most
one adjacent pair of which has unequal weights. -/
private lemma weight_pattern_of_vec4 (T : NumericalType) {cw : Fin 4 → Fin T.componentCount}
    {σ : Equiv.Perm (Fin 4)}
    (hσ : (∀ p : Fin 4, (σ p).val = p.val) ∨ (∀ p : Fin 4, (σ p).val + p.val = 3))
    {a b d e : ℤ} (hw : (fun p => T.weight (cw (σ p))) = ![a, b, d, e])
    (hpat : (a = b ∧ b = d) ∨ (a = b ∧ d = e)) :
    (T.weight (cw 0) = T.weight (cw 1) ∧ T.weight (cw 1) = T.weight (cw 2)) ∨
      (T.weight (cw 1) = T.weight (cw 2) ∧ T.weight (cw 2) = T.weight (cw 3)) ∨
      (T.weight (cw 0) = T.weight (cw 1) ∧ T.weight (cw 2) = T.weight (cw 3)) := by
  have h0 : T.weight (cw (σ 0)) = a := by simpa using congrFun hw 0
  have h1 : T.weight (cw (σ 1)) = b := by simpa using congrFun hw 1
  have h2 : T.weight (cw (σ 2)) = d := by simpa using congrFun hw 2
  have h3 : T.weight (cw (σ 3)) = e := by simpa using congrFun hw 3
  rcases hσ with h | h
  · rw [show σ 0 = 0 from Fin.ext (h 0)] at h0
    rw [show σ 1 = 1 from Fin.ext (h 1)] at h1
    rw [show σ 2 = 2 from Fin.ext (h 2)] at h2
    rw [show σ 3 = 3 from Fin.ext (h 3)] at h3
    omega
  · rw [show σ 0 = 3 from Fin.ext (by have := h 0; omega)] at h0
    rw [show σ 1 = 2 from Fin.ext (by have := h 1; omega)] at h1
    rw [show σ 2 = 1 from Fin.ext (by have := h 2; omega)] at h2
    rw [show σ 3 = 0 from Fin.ext (by have := h 3; omega)] at h3
    omega

/-- Among four consecutive components of a cycle of minus-two indices, at most one of the three
adjacent pairs has unequal weights. Up to reordering the four are of type `A₄`, `C₄`, `B₄` or
`F₄`, and the reordering is the identity or the reversal because the four lie on a chain; each
of the resulting seven weight patterns has at most one change. -/
public lemma weight_pattern_of_four_window (T : NumericalType) (hn : 4 < T.componentCount)
    (cw : Fin 4 → Fin T.componentCount) (hinj : Function.Injective cw)
    (hminus : ∀ p, IsMinusTwoIndex T (cw p))
    (hadj : ∀ p q : Fin 4, T.intersection (cw p) (cw q) ≠ 0 ↔
      (p.val + 1 = q.val ∨ q.val + 1 = p.val ∨ p.val = q.val)) :
    ∃ W : ℤ, 0 < W ∧ (∀ p : Fin 4, T.weight (cw p) = W ∨ T.weight (cw p) = 2 * W) ∧
      ((T.weight (cw 0) = T.weight (cw 1) ∧ T.weight (cw 1) = T.weight (cw 2)) ∨
        (T.weight (cw 1) = T.weight (cw 2) ∧ T.weight (cw 2) = T.weight (cw 3)) ∨
        (T.weight (cw 0) = T.weight (cw 1) ∧ T.weight (cw 2) = T.weight (cw 3))) := by
  classical
  have v0 : (0 : Fin 4).val = 0 := by decide
  have v1 : (1 : Fin 4).val = 1 := by decide
  have v2 : (2 : Fin 4).val = 2 := by decide
  have v3 : (3 : Fin 4).val = 3 := by decide
  have hvec : ![cw 0, cw 1, cw 2, cw 3] = cw := by
    funext p
    fin_cases p <;> rfl
  obtain ⟨σ, w, hdata⟩ := four_minus_two_indices T hn (cw 0) (cw 1) (cw 2) (cw 3)
    (by rw [hvec]; exact hinj) (hminus 0) (hminus 1) (hminus 2) (hminus 3)
    ((hadj 0 1).mpr (Or.inl (by omega))) ((hadj 1 2).mpr (Or.inl (by omega)))
    ((hadj 2 3).mpr (Or.inl (by omega)))
  simp only [hvec, Function.comp_def] at hdata
  have hpos : ∀ r : Fin 4, ∀ x : ℤ, T.weight (cw (σ r)) = x → 0 < x :=
    fun r x h => h ▸ T.weight_pos _
  have h2pos : ∀ x : ℤ, 0 < x → 2 * x ≠ 0 := fun x hx => by omega
  rcases hdata with ⟨hwts, -⟩ | ⟨hwts, hmat, -⟩ | ⟨hwts, hmat, -⟩ | ⟨hwts, hmat, -⟩
  · -- type A₄: all four weights agree
    have hall : ∀ p : Fin 4, T.weight (cw p) = w := fun p => by
      rcases weight_mem_of_vec4 T hwts p with h | h | h | h <;> exact h
    exact ⟨w, hall 0 ▸ T.weight_pos _, fun p => Or.inl (hall p),
      Or.inl ⟨by rw [hall 0, hall 1], by rw [hall 1, hall 2]⟩⟩
  · -- type C₄
    have hwpos := hpos 0 w (by simpa using congrFun hwts 0)
    refine ⟨w, hwpos, fun p => ?_, weight_pattern_of_vec4 T ?_ hwts (by omega)⟩
    · rcases weight_mem_of_vec4 T hwts p with h | h | h | h <;> omega
    · exact perm_four_of_intersections T cw hadj σ _ hmat (by simpa using hwpos.ne')
        (by simpa using hwpos.ne') (by simpa using h2pos w hwpos)
  · -- type B₄
    have hwpos := hpos 3 w (by simpa using congrFun hwts 3)
    refine ⟨w, hwpos, fun p => ?_, weight_pattern_of_vec4 T ?_ hwts (by omega)⟩
    · rcases weight_mem_of_vec4 T hwts p with h | h | h | h <;> omega
    · exact perm_four_of_intersections T cw hadj σ _ hmat (by simpa using h2pos w hwpos)
        (by simpa using h2pos w hwpos) (by simpa using h2pos w hwpos)
  · -- type F₄
    have hwpos := hpos 0 w (by simpa using congrFun hwts 0)
    refine ⟨w, hwpos, fun p => ?_, weight_pattern_of_vec4 T ?_ hwts (by omega)⟩
    · rcases weight_mem_of_vec4 T hwts p with h | h | h | h <;> omega
    · exact perm_four_of_intersections T cw hadj σ _ hmat (by simpa using hwpos.ne')
        (by simpa using h2pos w hwpos) (by simpa using h2pos w hwpos)

/-! ### The cycle configuration -/

/-- Two components of a cycle at cyclic distance one, read through the positions of the
`n`-cycle coefficient table. -/
private lemma cycle_adjacent_iff (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (c : ℕ → Fin T.componentCount)
    (hcadj : ∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
      (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
        k ≡ l [MOD T.componentCount]))
    (a b : ℕ) (hi : a < T.componentCount) (hj : b < T.componentCount) (hne : a ≠ b) :
    T.intersection (c a) (c b) ≠ 0 ↔
      (max a b = min a b + 1 ∨ (min a b = 0 ∧ max a b = T.componentCount - 1)) := by
  have e1 : (a + 1 ≡ b [MOD T.componentCount]) ↔
      (a + 1 = b ∨ (a + 1 = T.componentCount ∧ b = 0)) := by
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hj]
    exact mod_succ_eq_iff T a b hi hj
  have e2 : (b + 1 ≡ a [MOD T.componentCount]) ↔
      (b + 1 = a ∨ (b + 1 = T.componentCount ∧ a = 0)) := by
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hi]
    exact mod_succ_eq_iff T b a hj hi
  have e3 : (a ≡ b [MOD T.componentCount]) ↔ a = b := modEq_iff_eq_of_lt hi hj
  rw [hcadj, e1, e2, e3]
  omega

/-- The intersection number of two cyclically adjacent components of a cycle of at least six
minus-two indices is the common weight. -/
private lemma cycle_intersection_eq_weight (T : NumericalType) (hn : 3 ≤ T.componentCount)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (c : ℕ → Fin T.componentCount)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount])
    (hcadj : ∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
      (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
        k ≡ l [MOD T.componentCount]))
    (hWc : ∀ j, T.weight (c j) = T.weight (c 0))
    (a b : ℕ) (hb : b < T.componentCount)
    (hadj : b = a + 1 ∨ (a = 0 ∧ b = T.componentCount - 1)) :
    T.intersection (c a) (c b) = T.weight (c 0) := by
  rcases hadj with h | ⟨h0, h1⟩
  · rw [h]
    exact intersection_eq_weight_of_cycle T hn hminus c hceq hcadj hWc a
  · have hzero : c (T.componentCount - 1 + 1) = c 0 := by
      rw [show T.componentCount - 1 + 1 = T.componentCount by omega]
      simpa using cycle_apply_add_componentCount T c hceq 0
    have h := intersection_eq_weight_of_cycle T hn hminus c hceq hcadj hWc
      (T.componentCount - 1)
    rw [hzero] at h
    rw [h0, h1, T.intersection_symm]
    exact h

/-- A cycle of minus-two indices with constant weights and constant multiplicities matches the
coefficient table of the `n`-cycle. -/
private lemma matchesCoefficients_cycle (T : NumericalType) (n : ℕ)
    (hn : T.componentCount = n) (h3 : 3 ≤ n)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (c : ℕ → Fin T.componentCount)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount])
    (hcadj : ∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
      (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
        k ≡ l [MOD T.componentCount]))
    (hW : ∀ j, T.weight (c j) = T.weight (c 0))
    (hM : ∀ j, T.multiplicity (c j) = T.multiplicity (c 0)) :
    MatchesCoefficients T n (GenusOne.longMultiplicity .cycle n)
      (GenusOne.longWeight .cycle n) (GenusOne.longIntersection .cycle n) := by
  classical
  have hlt : ∀ i : Fin n, i.val < T.componentCount := by
    intro i
    rw [hn]
    exact i.isLt
  have hcinj : Function.Injective (fun i : Fin n => c i.val) := by
    intro i j h
    exact Fin.ext ((modEq_iff_eq_of_lt (hlt i) (hlt j)).mp ((hceq i.val j.val).mp h))
  obtain ⟨e, he⟩ : ∃ e : Fin n ≃ Fin T.componentCount, ∀ i, e i = c i.val :=
    ⟨Equiv.ofBijective _ (Fintype.bijective_iff_injective_and_card _ |>.mpr
      ⟨hcinj, by simp [hn]⟩), fun _ => rfl⟩
  refine ⟨e, T.multiplicity (c 0), T.weight (c 0), T.multiplicity_pos _, T.weight_pos _,
    ?_, ?_, ?_, ?_⟩
  · intro i
    rw [he i, hM i.val]
    simp [GenusOne.longMultiplicity]
  · intro i
    rw [he i, hW i.val]
    simp [GenusOne.longWeight]
  · intro i j
    rw [he i, he j]
    by_cases hij : i = j
    · subst hij
      rw [(hminus (c i.val)).2, hW i.val]
      simp [GenusOne.longIntersection, GenusOne.longWeight]
    · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      have hadj := cycle_adjacent_iff T (by omega) c hcadj i.val j.val (hlt i) (hlt j) hne
      rw [hn] at hadj
      by_cases hcase : max i.val j.val = min i.val j.val + 1 ∨
          (min i.val j.val = 0 ∧ max i.val j.val = n - 1)
      · have hval : T.intersection (c i.val) (c j.val) = T.weight (c 0) := by
          rcases Nat.lt_or_ge i.val j.val with h | h
          · exact cycle_intersection_eq_weight T (by omega) hminus c hceq hcadj hW i.val j.val
              (hlt j) (by omega)
          · rw [T.intersection_symm]
            exact cycle_intersection_eq_weight T (by omega) hminus c hceq hcadj hW j.val i.val
              (hlt i) (by omega)
        rw [hval]
        have hedge : GenusOne.longIntersection GenusOne.LongFamily.cycle n i j = 1 := by
          simp only [GenusOne.longIntersection, GenusOne.longEdge, ite_eq_right hij]
          rcases hcase with h | ⟨h0, h1⟩
          · simp [h]
          · simp [h0, h1]
        rw [hedge]
        ring
      · have hzero : T.intersection (c i.val) (c j.val) = 0 := by
          by_contra hcon
          exact hcase (hadj.mp hcon)
        rw [hzero]
        have hedge : GenusOne.longIntersection GenusOne.LongFamily.cycle n i j = 0 := by
          simp only [GenusOne.longIntersection, GenusOne.longEdge]
          rw [ite_eq_right hij]
          exact ite_eq_right hcase
        rw [hedge]
        ring
  · intro i
    rw [he i]
    exact (hminus (c i.val)).1

/-- All the weights along a cycle of exactly five minus-two indices agree: any four consecutive
of them admit at most one change of weight, and five such windows around a cycle of length five
leave no change at all. -/
private lemma weight_const_of_five_cycle (T : NumericalType) (hn : T.componentCount = 5)
    (hminus : ∀ i, IsMinusTwoIndex T i)
    (c : ℕ → Fin T.componentCount)
    (hceq : ∀ k l, c k = c l ↔ k ≡ l [MOD T.componentCount])
    (hcadj : ∀ k l, T.intersection (c k) (c l) ≠ 0 ↔
      (k + 1 ≡ l [MOD T.componentCount] ∨ l + 1 ≡ k [MOD T.componentCount] ∨
        k ≡ l [MOD T.componentCount]))
    (k : ℕ) : T.weight (c k) = T.weight (c 0) := by
  have hper : ∀ j, c j = c (j % T.componentCount) := by
    intro j
    rw [hceq]
    exact (Nat.mod_mod_of_dvd j dvd_rfl).symm
  have hshift : ∀ j, c (j + 5) = c j := by
    intro j
    rw [hceq]
    unfold Nat.ModEq
    rw [hn]
    exact Nat.add_mod_right j 5
  have hwin : ∀ b : ℕ,
      (T.weight (c b) = T.weight (c (b + 1)) ∧
        T.weight (c (b + 1)) = T.weight (c (b + 2))) ∨
      (T.weight (c (b + 1)) = T.weight (c (b + 2)) ∧
        T.weight (c (b + 2)) = T.weight (c (b + 3))) ∨
      (T.weight (c b) = T.weight (c (b + 1)) ∧
        T.weight (c (b + 2)) = T.weight (c (b + 3))) := by
    intro b
    obtain ⟨hinj, hadjw⟩ := window_data T (t := 4) (by omega) c hceq hcadj b
    obtain ⟨W, -, -, hpat⟩ := weight_pattern_of_four_window T (by omega)
      (fun p : Fin 4 => c (b + p.val)) hinj (fun p => hminus _) hadjw
    simpa using hpat
  have d0 := hwin 0
  have d1 := hwin 1
  have d2 := hwin 2
  have d3 := hwin 3
  have d4 := hwin 4
  norm_num at d0 d1 d2 d3 d4
  have e5 : c 5 = c 0 := by simpa using hshift 0
  have e6 : c 6 = c 1 := by simpa using hshift 1
  have e7 : c 7 = c 2 := by simpa using hshift 2
  rw [e5] at d2 d3 d4
  rw [e6] at d3 d4
  rw [e7] at d4
  have hall : T.weight (c 0) = T.weight (c 1) ∧ T.weight (c 1) = T.weight (c 2) ∧
      T.weight (c 2) = T.weight (c 3) ∧ T.weight (c 3) = T.weight (c 4) := by omega
  have hj : ∀ j, j < 5 → T.weight (c j) = T.weight (c 0) := by
    intro j hj5
    interval_cases j <;> omega
  have hmod : k % T.componentCount < 5 := by
    have := Nat.mod_lt k (show 0 < T.componentCount by omega)
    omega
  rw [hper k]
  exact hj _ hmod

/-- **Stacks Project, Tag 0C8T**, the converse for a numerical type each of whose components
meets at least two others. Such a minimal numerical type of genus one with at least five
components is the `n`-cycle: all its weights agree, all its intersection numbers along the
cycle equal that weight, and all its multiplicities agree. That is case (16) of the source's
list for five components and case (25), the `n`-cycle family, for six or more. -/
public theorem isGenusOneConfiguration_of_two_le_neighborCount (T : NumericalType)
    (hmin : IsMinimal T) (hgenus : genus T = 1) (hn : 5 ≤ T.componentCount)
    (hdeg : ∀ i, 2 ≤ neighborCount T i) :
    IsGenusOneConfiguration T := by
  classical
  have hminus : ∀ i, IsMinusTwoIndex T i :=
    forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one T hmin hgenus (by omega)
  have hdeg2 : ∀ i, neighborCount T i = 2 :=
    neighborCount_eq_two_of_two_le_neighborCount T hmin hgenus (by omega) hdeg
  obtain ⟨c, hceq, hsurj, hcadj⟩ := exists_cyclic_ordering T (by omega) hdeg2
  by_cases h5 : T.componentCount = 5
  · have hW := weight_const_of_five_cycle T h5 hminus c hceq hcadj
    have hM := multiplicity_eq_zero_of_cycle T (by omega) hminus c hsurj hceq hcadj hW
    have hMC := matchesCoefficients_cycle T 5 h5 (by omega) hminus c hceq hcadj hW hM
    refine Or.inr (Or.inl ⟨([1, 1, 1, 1, 1], [1, 1, 1, 1, 1],
      [[-2, 1, 0, 0, 1], [1, -2, 1, 0, 0], [0, 1, -2, 1, 0], [0, 0, 1, -2, 1],
        [1, 0, 0, 1, -2]]), by decide, ?_⟩)
    obtain ⟨e, m, w, hm, hw, hmul, hwt, hint, hgen⟩ := hMC
    refine ⟨e, m, w, hm, hw, fun i => ?_, fun i => ?_, fun i j => ?_, hgen⟩
    · rw [hmul i]
      fin_cases i <;> rfl
    · rw [hwt i]
      fin_cases i <;> rfl
    · rw [hint i j]
      fin_cases i <;> fin_cases j <;> rfl
  · have hn6 : 6 ≤ T.componentCount := by omega
    have hW := weight_eq_zero_of_cycle T hn6 hminus c hceq hcadj
    have hM := multiplicity_eq_zero_of_cycle T (by omega) hminus c hsurj hceq hcadj hW
    exact Or.inr (Or.inr ⟨T.componentCount, .cycle, hn6,
      matchesCoefficients_cycle T T.componentCount rfl (by omega) hminus c hceq hcadj hW hM⟩)

/-- **Stacks Project, Tag 0C8T** for a numerical type each of whose components meets at least
two others and which has at least five components: it is minimal of genus one exactly when it
is the `n`-cycle, case (16) for five components and case (25) for six or more. -/
@[stacks 0C8T "the classification when every component meets at least two others and there are \
at least five of them: the n-cycle, case (16) for five components and case (25) for six or \
more"]
public theorem isMinimal_and_genus_eq_one_iff_of_two_le_neighborCount (T : NumericalType)
    (hn : 5 ≤ T.componentCount) (hdeg : ∀ i, 2 ≤ neighborCount T i) :
    (IsMinimal T ∧ genus T = 1) ↔ IsGenusOneConfiguration T :=
  ⟨fun h => isGenusOneConfiguration_of_two_le_neighborCount T h.1 h.2 hn hdeg,
    isMinimal_and_genus_eq_one_of_isGenusOneConfiguration T⟩

/-! ### The reduction for a component meeting exactly one other -/

/-- The reduction driving the rest of the converse. If a component `l` of a minimal numerical
type of genus one with at least three components meets exactly one other component `x`, then the
remaining components form a connected *proper* set of minus-two indices, so Proposition 0C8Q
applies to them: they are, after reordering, one of the finite Dynkin configurations on one
fewer component. What the classification still needs after this reduction is the enumeration of
the ways `l` can be attached to each Dynkin diagram — the affine extensions. -/
public lemma exists_dynkinConfiguration_of_erase_leaf (T : NumericalType)
    (hmin : IsMinimal T) (hgenus : genus T = 1) (hn : 3 ≤ T.componentCount)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x) :
    ∃ (t : ℕ) (v : Fin t → Fin T.componentCount), t + 1 = T.componentCount ∧
      Function.Injective v ∧ (∀ r, v r ≠ l) ∧ (∀ y, y ≠ l → ∃ r, v r = y) ∧
      ∃ (d : DynkinShape) (w : ℤ), IsDynkinConfiguration T v d w := by
  classical
  have hminus : ∀ i, IsMinusTwoIndex T i :=
    forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one T hmin hgenus (by omega)
  have hmemU : l ∈ (Finset.univ : Finset (Fin T.componentCount)) := Finset.mem_univ l
  have hcard : (Finset.univ.erase l : Finset (Fin T.componentCount)).card + 1 =
      T.componentCount := by
    rw [Finset.card_erase_add_one hmemU]
    simp
  have hconn := connected_erase_leaf T Finset.univ l x hmemU (Finset.mem_univ x) hlx
    (fun y _ hyl hint => hleaf y hyl hint) (univ_connected T)
  obtain ⟨v, hvinj, hvrange, d, w, hcfg⟩ :=
    classify_connected_proper_minusTwo_subgraph T (Finset.univ.erase l) (by omega)
      (by omega) (fun i _ => hminus i) hconn
  refine ⟨_, v, hcard, hvinj, ?_, ?_, d, w, hcfg⟩
  · intro r hr
    have hmem : v r ∈ ((Finset.univ.erase l : Finset (Fin T.componentCount)) :
        Set (Fin T.componentCount)) := by
      rw [← hvrange]
      exact ⟨r, rfl⟩
    simp only [Finset.coe_erase, Set.mem_sdiff] at hmem
    exact hmem.2 (by simpa using hr)
  · intro y hy
    have hmem : y ∈ ((Finset.univ.erase l : Finset (Fin T.componentCount)) :
        Set (Fin T.componentCount)) := by
      simp [Finset.coe_erase, hy]
    rw [← hvrange] at hmem
    exact hmem

/-- Every component of a numerical type with more than one component meets another. -/
public lemma one_le_neighborCount (T : NumericalType) (hn : 1 < T.componentCount)
    (i : Fin T.componentCount) : 1 ≤ neighborCount T i := by
  classical
  rcases Nat.eq_zero_or_pos (neighborCount T i) with h0 | h
  · exfalso
    have hempty : neighbors T i = ∅ := Finset.card_eq_zero.mp h0
    obtain ⟨j, hj⟩ : ∃ j : Fin T.componentCount, j ≠ i := by
      obtain ⟨a, ha⟩ : ∃ a : Fin T.componentCount, a.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b : Fin T.componentCount, b.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
      by_cases h : a = i
      · exact ⟨b, fun hbi => by rw [← h] at hbi; rw [hbi] at hb; omega⟩
      · exact ⟨a, h⟩
    refine T.connected ⟨{i}, ⟨i, rfl⟩, ?_, ?_⟩
    · intro h
      exact hj (by simpa using (h ▸ Set.mem_univ j : j ∈ ({i} : Set (Fin T.componentCount))))
    · intro a ha b hb
      have hai : a = i := by simpa using ha
      have hbi : b ≠ i := fun h => hb (by simp [h])
      subst hai
      by_contra hcon
      have := (mem_neighbors_iff T a b).mpr ⟨fun h => hbi h.symm, hcon⟩
      rw [hempty] at this
      simp at this
  · exact h

/-- **Stacks Project, Tag 0C8T**, the state of the converse for five or more components. Either
every component meets at least two others, and then the type is the `n`-cycle; or some component
meets exactly one other, and then deleting it leaves one of the finite Dynkin configurations on
one fewer component. -/
public lemma isGenusOneConfiguration_or_exists_dynkin_erase_leaf (T : NumericalType)
    (hmin : IsMinimal T) (hgenus : genus T = 1) (hn : 5 ≤ T.componentCount) :
    IsGenusOneConfiguration T ∨
      ∃ l x : Fin T.componentCount, l ≠ x ∧
        (∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x) ∧
        ∃ (t : ℕ) (v : Fin t → Fin T.componentCount), t + 1 = T.componentCount ∧
          Function.Injective v ∧ (∀ r, v r ≠ l) ∧ (∀ y, y ≠ l → ∃ r, v r = y) ∧
          ∃ (d : DynkinShape) (w : ℤ), IsDynkinConfiguration T v d w := by
  classical
  by_cases hdeg : ∀ i, 2 ≤ neighborCount T i
  · exact Or.inl (isGenusOneConfiguration_of_two_le_neighborCount T hmin hgenus hn hdeg)
  · right
    push Not at hdeg
    obtain ⟨l, hl⟩ := hdeg
    have hone : neighborCount T l = 1 := by
      have := one_le_neighborCount T (by omega) l
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
    have hxmem : x ∈ neighbors T l := by rw [hx]; exact Finset.mem_singleton_self x
    have hlx : l ≠ x := ((mem_neighbors_iff T l x).mp hxmem).1
    have hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x := by
      intro y hyl hint
      have hymem : y ∈ neighbors T l :=
        (mem_neighbors_iff T l y).mpr ⟨fun h => hyl h.symm, hint⟩
      rw [hx] at hymem
      exact Finset.mem_singleton.mp hymem
    exact ⟨l, x, hlx, hleaf,
      exists_dynkinConfiguration_of_erase_leaf T hmin hgenus (by omega) l x hlx hleaf⟩

end AlgebraicGeometry.NumericalType
