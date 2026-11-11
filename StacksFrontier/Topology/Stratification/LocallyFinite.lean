module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally finite stratifications and the associated closed sets

For a locally finite stratification `{X i}` of a topological space `α` indexed by a partially
ordered type `I`, the unions `Z i = ⋃_{j ≤ i} X j` are closed and satisfy
`Z i ∩ Z j = ⋃_{k ≤ i, k ≤ j} Z k`. Conversely, a locally finite family of closed sets covering
`α` and satisfying that identity arises this way, the strata being
`X i = Z i \ ⋃_{j < i} Z j`.

## Main definitions

* `IsPartition`: a family of pairwise disjoint locally closed subsets covering the space.
* `IsGoodPartition`: a good stratification, a partition in which a part meeting the closure of
  another part is contained in that closure.
* `IsStratification`: a partition satisfying `closure (X j) ⊆ ⋃_{i ≤ j} X i`.
* `IsLocallyFiniteStratification`: a stratification whose strata form a locally finite family.

## Main results

* `closedZ_of_locallyFiniteStratification`: each `Z i` is closed, and the intersection of two of
  them is the union of the `Z k` below both.
* `locallyFiniteStratification_of_closedZ`: the strata recovered from such a family of closed
  sets form a locally finite stratification.
-/

@[expose] public section

variable {α : Type*} [TopologicalSpace α] {I : Type*}

/-- A family `X : I → Set α` is a *partition* of the topological space `α` if
each part is locally closed, the parts are pairwise disjoint, and they cover
`α`. -/
structure IsPartition (X : I → Set α) : Prop where
  /-- Each part is locally closed in `α`. -/
  locallyClosed : ∀ i, IsLocallyClosed (X i)
  /-- The parts are pairwise disjoint. -/
  disjoint : ∀ i i', i ≠ i' → Disjoint (X i) (X i')
  /-- The parts cover `α`. -/
  cover : ⋃ i, X i = Set.univ

/-- **Stacks 09Y0**.
A *good stratification* of the topological space `α` is a partition `X : I → Set α` of `α`
(into pairwise disjoint locally closed parts covering `α`) such that for all `i, j` with
`X i ∩ closure (X j) ≠ ∅` we have `X i ⊆ closure (X j)`. -/
@[stacks 09Y0]
structure IsGoodPartition (X : I → Set α) : Prop where
  /-- The family is a partition. -/
  isPartition : IsPartition X
  /-- A part meeting the closure of a part is contained in that closure. -/
  subset_closure_of_inter_closure_nonempty :
    ∀ i j, (X i ∩ closure (X j)).Nonempty → X i ⊆ closure (X j)

/-- In a good stratification, the closure of a part `X j` is the union of the parts `X i`
with `X i ⊆ closure (X j)`. -/
theorem IsGoodPartition.closure_eq_iUnion {X : I → Set α} (h : IsGoodPartition X) (j : I) :
    closure (X j) = ⋃ i ∈ {i | X i ⊆ closure (X j)}, X i := by
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion₂_subset fun i hi => hi)
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (h.isPartition.cover ▸ Set.mem_univ x)
  exact Set.mem_biUnion
    (h.subset_closure_of_inter_closure_nonempty i j ⟨x, hxi, hx⟩) hxi

/-- **Stacks 09Y1**.
A family `X : I → Set α`, with `I` a partially ordered set, is a
*stratification* if it is a partition and for every `j` the closure of `X j` is
contained in `⋃ (i ≤ j) X i`. The parts `X i` are the *strata*. -/
@[stacks 09Y1]
structure IsStratification [PartialOrder I] (X : I → Set α) : Prop where
  /-- The family is a partition. -/
  isPartition : IsPartition X
  /-- The stratification condition: `closure (X j) ⊆ ⋃ (i ≤ j) X i`. -/
  closure_subset : ∀ j, closure (X j) ⊆ ⋃ i ∈ {i | i ≤ j}, X i

/-- A *locally finite stratification* is a stratification whose family of strata
is locally finite (in the sense of `LocallyFinite`: every point has a
neighbourhood meeting only finitely many strata). -/
structure IsLocallyFiniteStratification [PartialOrder I] (X : I → Set α) : Prop where
  /-- The family is a stratification. -/
  isStratification : IsStratification X
  /-- The family of strata is locally finite. -/
  locallyFinite : LocallyFinite X

/-! ### Unions of a locally finite family over an index set -/

/-- The closure of the union of a locally finite family over an index set is the union of the
closures. -/
lemma LocallyFinite.closure_biUnion {f : I → Set α} (hf : LocallyFinite f) (s : Set I) :
    closure (⋃ i ∈ s, f i) = ⋃ i ∈ s, closure (f i) := by
  rw [Set.biUnion_eq_iUnion, Set.biUnion_eq_iUnion]
  exact (hf.comp_injective Subtype.val_injective).closure_iUnion

/-- The union of a locally finite family of closed sets over an index set is closed. -/
@[ega "IV 21.6.1" "more general"]
lemma LocallyFinite.isClosed_biUnion {f : I → Set α} (hf : LocallyFinite f)
    (hcl : ∀ i, IsClosed (f i)) (s : Set I) : IsClosed (⋃ i ∈ s, f i) := by
  rw [Set.biUnion_eq_iUnion]
  exact (hf.comp_injective Subtype.val_injective).isClosed_iUnion fun i => hcl i

/-- For a locally finite stratification, the union `⋃ (j ≤ i) X j` of the strata below `i` is
closed: local finiteness turns its closure into the union of the closures, and each
`closure (X j)` with `j ≤ i` is already contained in the union. -/
private lemma isClosed_biUnion_le_of_isLocallyFiniteStratification [PartialOrder I]
    {X : I → Set α} (h : IsLocallyFiniteStratification X) (i : I) :
    IsClosed (⋃ j ∈ {j | j ≤ i}, X j) := by
  rw [← closure_subset_iff_isClosed, h.locallyFinite.closure_biUnion]
  exact Set.iUnion₂_subset fun j hj => (h.isStratification.closure_subset j).trans <|
    Set.biUnion_subset_biUnion_left fun l hl => hl.trans hj

/-- For a locally finite stratification and `Z i = ⋃ (j ≤ i) X j`, the intersection
`Z i ∩ Z j` is the union of the `Z k` with `k ≤ i` and `k ≤ j`: a point of the intersection
lies in a single stratum `X l`, and disjointness of the strata forces the two indices
witnessing membership to agree. -/
private lemma inter_eq_biUnion_of_isLocallyFiniteStratification [PartialOrder I]
    {X : I → Set α} (h : IsLocallyFiniteStratification X) {Z : I → Set α}
    (hZ : ∀ i, Z i = ⋃ j ∈ {j | j ≤ i}, X j) (i j : I) :
    Z i ∩ Z j = ⋃ k ∈ {k | k ≤ i ∧ k ≤ j}, Z k := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨hxi, hxj⟩
    rw [hZ i] at hxi
    rw [hZ j] at hxj
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hxi hxj
    obtain ⟨l, hli, hxl⟩ := hxi
    obtain ⟨m, hmj, hxm⟩ := hxj
    have hlm : l = m := by
      by_contra hne
      exact (h.isStratification.isPartition.disjoint l m hne).le_bot ⟨hxl, hxm⟩
    subst hlm
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨l, ⟨hli, hmj⟩, ?_⟩
    rw [hZ l]
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨l, le_refl l, hxl⟩
  · apply Set.iUnion₂_subset
    intro k hk
    obtain ⟨hki, hkj⟩ := hk
    have hmono : ∀ m, k ≤ m → Z k ⊆ Z m := fun m hkm => by
      rw [hZ k, hZ m]
      exact Set.biUnion_subset_biUnion_left fun l hl => hl.trans hkm
    exact Set.subset_inter (hmono i hki) (hmono j hkj)

/-- **Stacks 09Y2** (1).
Let `X` be a locally finite stratification of `α` with partial order `≤` on `I`,
and for each `i` let `Z i = ⋃ (j ≤ i) X j`. Then each `Z i` is closed, and for
all `i, j` one has `Z i ∩ Z j = ⋃ (k ≤ i ∧ k ≤ j) Z k`. -/
@[stacks 09Y2 "(1)"]
theorem closedZ_of_locallyFiniteStratification [PartialOrder I] {X : I → Set α}
    (h : IsLocallyFiniteStratification X)
    (Z : I → Set α) (hZ : ∀ i, Z i = ⋃ j ∈ {j | j ≤ i}, X j) :
    (∀ i, IsClosed (Z i)) ∧
    (∀ i j, Z i ∩ Z j = ⋃ k ∈ {k | k ≤ i ∧ k ≤ j}, Z k) := by
  refine ⟨fun i => ?_, inter_eq_biUnion_of_isLocallyFiniteStratification h hZ⟩
  rw [hZ i]
  exact isClosed_biUnion_le_of_isLocallyFiniteStratification h i

/-! ### Recovering the strata from a family of closed sets -/

section
omit [TopologicalSpace α]

/-- Membership in the stratum `Z i \ ⋃ (j < i) Z j`. -/
lemma mem_sdiff_biUnion_lt_iff [Preorder I] (Z : I → Set α) (i : I) (x : α) :
    x ∈ Z i \ ⋃ j ∈ {j | j < i}, Z j ↔ x ∈ Z i ∧ ∀ j, j < i → x ∉ Z j := by
  simp

/-- A point of the stratum `Z i \ ⋃ (j < i) Z j` lies in no `Z k` with `k ≤ i` other than
`Z i` itself. -/
lemma eq_of_mem_sdiff_biUnion_lt [PartialOrder I] {Z : I → Set α} {x : α} {i k : I}
    (hx : x ∈ Z i \ ⋃ j ∈ {j | j < i}, Z j) (hki : k ≤ i) (hxk : x ∈ Z k) : k = i :=
  hki.lt_or_eq.resolve_left fun hlt => ((mem_sdiff_biUnion_lt_iff Z i x).mp hx).2 k hlt hxk

/-- A point of `Z i ∩ Z j` lies in some `Z k` with `k ≤ i` and `k ≤ j`. -/
private lemma exists_le_mem_of_mem_inter [Preorder I] {Z : I → Set α}
    (hint : ∀ i j, Z i ∩ Z j = ⋃ k ∈ {k | k ≤ i ∧ k ≤ j}, Z k) {x : α} {i j : I}
    (hx : x ∈ Z i ∩ Z j) : ∃ k, (k ≤ i ∧ k ≤ j) ∧ x ∈ Z k := by
  rw [hint i j] at hx
  simpa using hx

/-- Distinct strata `Z i \ ⋃ (j < i) Z j` are disjoint, for a family of sets satisfying
`Z i ∩ Z j = ⋃ (k ≤ i ∧ k ≤ j) Z k`. -/
lemma disjoint_sdiff_biUnion_lt [PartialOrder I] {Z : I → Set α}
    (hint : ∀ i j, Z i ∩ Z j = ⋃ k ∈ {k | k ≤ i ∧ k ≤ j}, Z k) {i i' : I} (hii' : i ≠ i') :
    Disjoint (Z i \ ⋃ j ∈ {j | j < i}, Z j) (Z i' \ ⋃ j ∈ {j | j < i'}, Z j) := by
  refine Set.disjoint_left.mpr fun x hxi hxi' => hii' ?_
  obtain ⟨k, ⟨hki, hki'⟩, hxk⟩ := exists_le_mem_of_mem_inter hint ⟨hxi.1, hxi'.1⟩
  exact eq_of_mem_sdiff_biUnion_lt hxi hki hxk ▸ eq_of_mem_sdiff_biUnion_lt hxi' hki' hxk

end

/-- Every point lies in the stratum of an index minimal among those whose set contains it. -/
lemma exists_mem_sdiff_biUnion_lt [PartialOrder I] {Z : I → Set α} (hlf : LocallyFinite Z)
    (hcover : ⋃ i, Z i = Set.univ) (x : α) :
    ∃ i, x ∈ Z i \ ⋃ j ∈ {j | j < i}, Z j := by
  have hne : {i | x ∈ Z i}.Nonempty := by
    have hx : x ∈ ⋃ i, Z i := by rw [hcover]; trivial
    exact Set.mem_iUnion.mp hx
  obtain ⟨m, hms, hmin⟩ := (hlf.point_finite x).exists_minimalFor id {i | x ∈ Z i} hne
  exact ⟨m, (mem_sdiff_biUnion_lt_iff Z m x).mpr
    ⟨hms, fun j hj hxj => absurd (le_antisymm hj.le (hmin hxj hj.le)) hj.ne⟩⟩

/-- The closure of a stratum `Z j \ ⋃ (l < j) Z l` is covered by the strata indexed by `i ≤ j`. -/
lemma closure_sdiff_biUnion_lt_subset [PartialOrder I] {Z : I → Set α}
    (hclosed : ∀ i, IsClosed (Z i)) (hcover : ⋃ i, Z i = Set.univ) (hlf : LocallyFinite Z)
    (hint : ∀ i j, Z i ∩ Z j = ⋃ k ∈ {k | k ≤ i ∧ k ≤ j}, Z k) (j : I) :
    closure (Z j \ ⋃ l ∈ {l | l < j}, Z l) ⊆
      ⋃ i ∈ {i | i ≤ j}, (Z i \ ⋃ l ∈ {l | l < i}, Z l) := by
  intro x hx
  obtain ⟨i, hxi⟩ := exists_mem_sdiff_biUnion_lt hlf hcover x
  obtain ⟨k, ⟨hki, hkj⟩, hxk⟩ := exists_le_mem_of_mem_inter hint
    ⟨hxi.1, (hclosed j).closure_subset_iff.mpr Set.sdiff_subset hx⟩
  exact Set.mem_biUnion (s := {i | i ≤ j}) (eq_of_mem_sdiff_biUnion_lt hxi hki hxk ▸ hkj) hxi

/-- **Stacks 09Y2** (2).
Let `I` be a partially ordered set and `{Z i}` a family of closed subsets of `α`
that cover `α`, are locally finite, and satisfy
`Z i ∩ Z j = ⋃ (k ≤ i ∧ k ≤ j) Z k`. Then the sets `X i = Z i \ ⋃ (j < i) Z j`,
with the partial order `≤` on `I`, form a locally finite stratification of
`α`. -/
@[stacks 09Y2 "(2)"]
theorem locallyFiniteStratification_of_closedZ [PartialOrder I] {Z : I → Set α}
    (hclosed : ∀ i, IsClosed (Z i))
    (hcover : ⋃ i, Z i = Set.univ)
    (hlf : LocallyFinite Z)
    (hint : ∀ i j, Z i ∩ Z j = ⋃ k ∈ {k | k ≤ i ∧ k ≤ j}, Z k)
    (X : I → Set α) (hX : ∀ i, X i = Z i \ ⋃ j ∈ {j | j < i}, Z j) :
    IsLocallyFiniteStratification X := by
  obtain rfl : X = fun i => Z i \ ⋃ j ∈ {j | j < i}, Z j := funext hX
  refine ⟨⟨⟨fun i => ?_, fun _ _ hii' => disjoint_sdiff_biUnion_lt hint hii', ?_⟩,
      closure_sdiff_biUnion_lt_subset hclosed hcover hlf hint⟩,
    hlf.subset fun _ => Set.sdiff_subset⟩
  · rw [Set.sdiff_eq]
    exact (hclosed i).isLocallyClosed.inter
      (hlf.isClosed_biUnion hclosed _).isOpen_compl.isLocallyClosed
  · exact Set.eq_univ_of_forall fun x =>
      Set.mem_iUnion.mpr (exists_mem_sdiff_biUnion_lt hlf hcover x)
