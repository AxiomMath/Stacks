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
public import Mathlib.SetTheory.ZFC.PSet
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
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Refining a finite partition by a finite stratification

Every finite partition of a topological space `X` into locally closed subsets is refined by a
finite stratification of `X`, that is, by a finite partition indexed by a partially ordered type
such that `closure (X_j) ⊆ ⋃_{i ≤ j} X_i`.

The refinement is built from the closures `T_i = closure X_i` and the boundaries
`Δ_i = T_i \ X_i`: their finite intersections `Z(A, B)` form a finite family `cSet` of closed
sets, each `s ∈ cSet` carries the stratum `Y_s = s \ ⋃ {t ∈ cSet | t ⊊ s}`, and the strata with
non-empty `Y_s` are ordered by inclusion of the underlying closed sets.

## Main definitions

* `TopPartition`: a family of pairwise disjoint locally closed subsets covering `X`.
* `TopPartition.Refines`: one partition refines another.
* `TopStratification`: a partition over a partially ordered index type satisfying the closure
  condition.
* `tcl`, `Δb`, `zcl`, `cSet`, `yset`, `cKept`: the pieces of the construction above.

## Main results

* `exists_finite_stratification_refining_finite_partition`: a finite partition is refined by a
  finite stratification.
-/

@[expose] public section

-- suggested change: `TopPartition`/`TopStratification` here and
-- `IsPartition`/`IsStratification` in `Topology/Stratification/LocallyFinite.lean` are two
-- encodings of the same two notions; one should subsume the other (bundled `parts` vs. a
-- predicate on a family), so the two tags share their vocabulary.
/-- A *partition* of a topological space `X` by a family of subsets indexed by `ι`:
pairwise disjoint locally closed subsets whose union covers `X`. -/
structure TopPartition (X : Type*) [TopologicalSpace X] (ι : Type*) where
  /-- The parts of the partition. -/
  parts : ι → Set X
  /-- Each part is locally closed in `X`. -/
  locallyClosed : ∀ i, IsLocallyClosed (parts i)
  /-- The parts are pairwise disjoint. -/
  pairwiseDisjoint : Pairwise (Function.onFun Disjoint parts)
  /-- The parts cover all of `X`. -/
  iUnion_eq_univ : ⋃ i, parts i = Set.univ

/-- A partition `P` (indexed by `κ`) *refines* a partition `Q` (indexed by `ι`)
when every part of `P` is contained in some part of `Q`. -/
def TopPartition.Refines {X : Type*} [TopologicalSpace X] {ι κ : Type*}
    (P : TopPartition X κ) (Q : TopPartition X ι) : Prop :=
  ∀ j : κ, ∃ i : ι, P.parts j ⊆ Q.parts i

/-- A *stratification* of `X` indexed by a partially ordered type `ι`:
a partition `{X_i}_{i ∈ ι}` such that for every `j`, the closure of `X_j` is
contained in the union of the parts indexed by `i ≤ j`. -/
structure TopStratification (X : Type*) [TopologicalSpace X] (ι : Type*)
    [PartialOrder ι] extends TopPartition X ι where
  /-- For every `j`, `closure (parts j) ⊆ ⋃_{i ≤ j} parts i`. -/
  closure_subset : ∀ j : ι, closure (parts j) ⊆ ⋃ i, ⋃ (_ : i ≤ j), parts i

namespace Construction

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] (P : TopPartition X ι)

/-- Closure of the `i`-th part. -/
def tcl (i : ι) : Set X := closure (P.parts i)

/-- Boundary of the `i`-th part in its closure: `Δ_i = closure X_i \ X_i`. -/
def Δb (i : ι) : Set X := tcl P i \ P.parts i

/-- For `(A, B) : Finset ι × Finset ι`, the closed set
`Z(A, B) = (⋂_{i ∈ A} T_i) ∩ (⋂_{j ∈ B} Δ_j)`. -/
def zcl (p : Finset ι × Finset ι) : Set X :=
  (⋂ i ∈ p.1, tcl P i) ∩ (⋂ j ∈ p.2, Δb P j)

/-- The (set of) closed sets that can be obtained as some `zcl P p`. -/
def cSet : Set (Set X) := Set.range (zcl P)

/-- The stratum `Y_s = s \ ⋃₀ { t ∈ cSet | t ⊊ s }`. -/
def yset (s : Set X) : Set X := s \ ⋃₀ { t | t ∈ cSet P ∧ t ⊂ s }

/-- The (set of) closed sets in `cSet` whose `yset` is non-empty. -/
def cKept : Set (Set X) := { s ∈ cSet P | (yset P s).Nonempty }

end Construction

open Construction

section HelperLemmas

variable {X : Type*} [TopologicalSpace X] {ι : Type*} (P : TopPartition X ι)

/-- For a locally closed set `s`, the frontier `closure s \ s` is closed. -/
@[ega "I 4.1.3" "partial", ega "IV 5.1.10" "partial"]
lemma isClosed_closure_diff_of_locallyClosed
    {Y : Type*} [TopologicalSpace Y] {s : Set Y} (h : IsLocallyClosed s) :
    IsClosed (closure s \ s) :=
  isOpen_compl_iff.mp h.isOpen_coborder

/-- Each `T_i = closure (parts i)` is closed. -/
lemma Tcl_isClosed (i : ι) : IsClosed (tcl P i) := isClosed_closure

/-- Each `Δ_i = closure (parts i) \ parts i` is closed. -/
lemma Δb_isClosed (i : ι) : IsClosed (Δb P i) := by
  unfold Δb tcl
  exact isClosed_closure_diff_of_locallyClosed (P.locallyClosed i)

/-- The first factor of `zcl P p` is closed, as a finite intersection of closures. -/
lemma Zcl_first_isClosed (p : Finset ι × Finset ι) :
    IsClosed (⋂ i ∈ p.1, tcl P i) :=
  isClosed_biInter (fun i _ => Tcl_isClosed P i)

/-- The second factor of `zcl P p` is closed, as a finite intersection of `Δ_i`'s. -/
lemma Zcl_second_isClosed (p : Finset ι × Finset ι) :
    IsClosed (⋂ j ∈ p.2, Δb P j) :=
  isClosed_biInter (fun j _ => Δb_isClosed P j)

/-- Each `zcl P p` is closed. -/
lemma Zcl_isClosed (p : Finset ι × Finset ι) : IsClosed (zcl P p) :=
  (Zcl_first_isClosed P p).inter (Zcl_second_isClosed P p)

/-- Each element of `cSet P` is closed. -/
lemma cSet_isClosed {s : Set X} (hs : s ∈ cSet P) : IsClosed s := by
  rcases hs with ⟨p, rfl⟩
  exact Zcl_isClosed P p

/-- `cSet P` is finite, as the image of the finite type `Finset ι × Finset ι`. -/
lemma cSet_finite [Finite ι] : (cSet P).Finite := by
  unfold cSet
  exact Set.finite_range _

/-- `cKept P ⊆ cSet P`. -/
lemma cKept_subset_cSet : cKept P ⊆ cSet P := fun _ h => h.1

/-- `cKept P` is finite. -/
lemma cKept_finite [Finite ι] : (cKept P).Finite :=
  (cSet_finite P).subset (cKept_subset_cSet P)

/-- Membership in `zcl P (A, B)`: lie in every `tcl P i` for `i ∈ A` and every
`Δb P j` for `j ∈ B`. -/
lemma mem_Zcl_iff (A B : Finset ι) (x : X) :
    x ∈ zcl P (A, B) ↔ (∀ i ∈ A, x ∈ tcl P i) ∧ (∀ j ∈ B, x ∈ Δb P j) := by
  unfold zcl
  simp [Set.mem_inter_iff, Set.mem_iInter]

/-- Monotonicity of `zcl`: enlarging the index finsets shrinks the set. -/
lemma Zcl_subset_of_subset (A A' B B' : Finset ι) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    zcl P (A, B) ⊆ zcl P (A', B') := by
  intro x hx
  rw [mem_Zcl_iff] at hx ⊢
  exact ⟨fun i hi => hx.1 i (hA hi), fun j hj => hx.2 j (hB hj)⟩

/-- `tcl P k ∈ cSet P`. -/
lemma Tcl_mem_cSet (k : ι) : tcl P k ∈ cSet P := by
  classical
  refine ⟨({k}, ∅), ?_⟩
  unfold zcl
  simp [tcl]

/-- `Δb P k ∈ cSet P`. -/
lemma Δb_mem_cSet (k : ι) : Δb P k ∈ cSet P := by
  classical
  refine ⟨({k}, {k}), ?_⟩
  unfold zcl
  simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
  rw [Set.inter_eq_right]
  exact fun _ hx => hx.1

/-- `cSet P` is closed under pairwise intersection: if `s = zcl P (A₁, B₁)` and
`t = zcl P (A₂, B₂)` then `s ∩ t = zcl P (A₁ ∪ A₂, B₁ ∪ B₂)`. -/
lemma cSet_inter_mem {s t : Set X} (hs : s ∈ cSet P) (ht : t ∈ cSet P) :
    s ∩ t ∈ cSet P := by
  classical
  obtain ⟨⟨A₁, B₁⟩, hp⟩ := hs
  obtain ⟨⟨A₂, B₂⟩, hq⟩ := ht
  refine ⟨(A₁ ∪ A₂, B₁ ∪ B₂), ?_⟩
  rw [← hp, ← hq]
  ext x
  simp only [Set.mem_inter_iff, mem_Zcl_iff, Finset.mem_union]
  exact ⟨fun ⟨hT, hΔ⟩ =>
      ⟨⟨fun i hi => hT i (.inl hi), fun j hj => hΔ j (.inl hj)⟩,
        fun i hi => hT i (.inr hi), fun j hj => hΔ j (.inr hj)⟩,
    fun ⟨⟨hT₁, hΔ₁⟩, hT₂, hΔ₂⟩ =>
      ⟨fun i hi => hi.elim (hT₁ i) (hT₂ i), fun j hj => hj.elim (hΔ₁ j) (hΔ₂ j)⟩⟩

/-- The union of proper sub-elements of `s` inside `cSet P` is closed. -/
lemma sUnion_propSubsets_isClosed [Finite ι] {s : Set X} :
    IsClosed (⋃₀ { t | t ∈ cSet P ∧ t ⊂ s }) := by
  rw [Set.sUnion_eq_biUnion]
  exact ((cSet_finite P).subset fun _ ht => ht.1).isClosed_biUnion
    fun _ ht => cSet_isClosed P ht.1

/-- For `s ∈ cSet P`, the stratum `yset P s` is locally closed. -/
lemma Yset_locallyClosed [Finite ι] {s : Set X} (hs : s ∈ cSet P) :
    IsLocallyClosed (yset P s) := by
  have hsCl : IsClosed s := cSet_isClosed P hs
  have hUCl : IsClosed (⋃₀ { t | t ∈ cSet P ∧ t ⊂ s }) :=
    sUnion_propSubsets_isClosed P
  unfold yset
  rw [Set.sdiff_eq]
  exact hsCl.isLocallyClosed.inter hUCl.isOpen_compl.isLocallyClosed

/-- `yset P` strata are pairwise disjoint on `cSet P`. -/
lemma Yset_pairwiseDisjoint :
    (cSet P).PairwiseDisjoint (yset P) := by
  intro s hs t ht hst
  refine Set.disjoint_left.mpr (fun x ⟨hxs, hxs_not⟩ ⟨hxt, hxt_not⟩ => ?_)
  have hxs_min : ∀ u, u ∈ cSet P → u ⊂ s → x ∉ u := by
    intro u hu hus hxu
    exact hxs_not ⟨u, ⟨hu, hus⟩, hxu⟩
  have hxt_min : ∀ u, u ∈ cSet P → u ⊂ t → x ∉ u := by
    intro u hu hut hxu
    exact hxt_not ⟨u, ⟨hu, hut⟩, hxu⟩
  have hst_mem : s ∩ t ∈ cSet P := cSet_inter_mem P hs ht
  by_cases hcase : s ∩ t = s
  · have hst_sub : s ⊆ t := by rw [← hcase]; exact Set.inter_subset_right
    have hst_proper : s ⊂ t :=
      ⟨hst_sub, fun h => hst (hst_sub.antisymm h)⟩
    exact hxt_min s hs hst_proper hxs
  · have hst_inter_sub : s ∩ t ⊆ s := Set.inter_subset_left
    have hst_inter_proper : s ∩ t ⊂ s :=
      ⟨hst_inter_sub, fun h => hcase (hst_inter_sub.antisymm h)⟩
    exact hxs_min (s ∩ t) hst_mem hst_inter_proper ⟨hxs, hxt⟩

/-- Every point of `X` lies in `yset P s` for some `s ∈ cSet P`. -/
lemma Yset_covers [Finite ι] (x : X) : ∃ s ∈ cSet P, x ∈ yset P s := by
  classical
  have := Fintype.ofFinite ι
  set A : Finset ι := Finset.univ.filter (fun i => x ∈ tcl P i)
  set B : Finset ι := Finset.univ.filter (fun j => x ∈ Δb P j)
  refine ⟨zcl P (A, B), ⟨(A, B), rfl⟩, ?_, ?_⟩
  · rw [mem_Zcl_iff]
    exact ⟨fun i hi => (Finset.mem_filter.mp hi).2, fun j hj => (Finset.mem_filter.mp hj).2⟩
  · rintro ⟨t, ⟨ht_cSet, ht_lt⟩, hxt⟩
    obtain ⟨⟨A', B'⟩, rfl⟩ := ht_cSet
    rw [mem_Zcl_iff] at hxt
    exact ht_lt.2 (Zcl_subset_of_subset P A A' B B'
      (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxt.1 i hi⟩)
      (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxt.2 j hj⟩))

/-- If a point of the stratum `yset P s` lies in a member `t` of `cSet P`, then all of `s` lies
in `t`: otherwise `s ∩ t` would be a strictly smaller member of `cSet P` meeting `yset P s`. -/
lemma Yset_inter_subset {s t : Set X} (hs : s ∈ cSet P) (ht : t ∈ cSet P)
    (hne : (yset P s ∩ t).Nonempty) : s ⊆ t := by
  by_contra hcontra
  obtain ⟨x, ⟨hxs, hxs_not⟩, hxt⟩ := hne
  exact hxs_not ⟨s ∩ t, ⟨cSet_inter_mem P hs ht,
    ⟨Set.inter_subset_left, fun hsubeq => hcontra fun y hy => (hsubeq hy).2⟩⟩, hxs, hxt⟩

/-- If a point of `yset P s` lies in `tcl P k`, then all of `s` lies in `tcl P k`. -/
lemma Yset_inter_Tcl_subset {s : Set X} (hs : s ∈ cSet P) (k : ι)
    (hne : (yset P s ∩ tcl P k).Nonempty) : s ⊆ tcl P k :=
  Yset_inter_subset P hs (Tcl_mem_cSet P k) hne

/-- If a point of `yset P s` lies in `Δb P k`, then all of `s` lies in `Δb P k`. -/
lemma Yset_inter_Δb_subset {s : Set X} (hs : s ∈ cSet P) (k : ι)
    (hne : (yset P s ∩ Δb P k).Nonempty) : s ⊆ Δb P k :=
  Yset_inter_subset P hs (Δb_mem_cSet P k) hne

/-- Each non-empty stratum is contained in some part `P.parts i`. -/
lemma Yset_refines {s : Set X} (hs : s ∈ cKept P) :
    ∃ i : ι, yset P s ⊆ P.parts i := by
  obtain ⟨hsC, x, hx⟩ := hs
  obtain ⟨i₀, hxi₀⟩ := Set.mem_iUnion.mp (P.iUnion_eq_univ.symm.subset (Set.mem_univ x))
  refine ⟨i₀, fun y hy => ?_⟩
  by_contra hyN
  have hsT := Yset_inter_Tcl_subset P hsC i₀ ⟨x, hx, subset_closure hxi₀⟩
  exact (Yset_inter_Δb_subset P hsC i₀ ⟨y, hy, hsT hy.1, hyN⟩ hx.1).2 hxi₀

/-- `yset P s ⊆ s`. -/
lemma Yset_subset_self (s : Set X) : yset P s ⊆ s := fun _ hx => hx.1

/-- Every `s ∈ cSet P` is covered by the strata `yset P t` for `t ∈ cKept P` with
`t ⊆ s`. -/
lemma cSet_subset_iUnion_Yset [Finite ι] {s : Set X} (hs : s ∈ cSet P) :
    s ⊆ ⋃ (t ∈ cKept P) (_ : t ⊆ s), yset P t := by
  intro x hx
  set T_x : Set (Set X) := { t | t ∈ cSet P ∧ x ∈ t ∧ t ⊆ s }
  obtain ⟨t, ⟨ht_cset, ht_x, ht_sub⟩, ht_min⟩ :=
    ((cSet_finite P).subset fun t ht => ht.1).exists_minimalFor (id : Set X → Set X) T_x
      ⟨s, hs, hx, subset_rfl⟩
  have hx_y : x ∈ yset P t := by
    refine ⟨ht_x, ?_⟩
    rintro ⟨u, ⟨hu_cset, hu_ssub⟩, hx_u⟩
    exact hu_ssub.not_subset (ht_min ⟨hu_cset, hx_u, hu_ssub.le.trans ht_sub⟩ hu_ssub.le)
  simp only [Set.mem_iUnion]
  exact ⟨t, ⟨ht_cset, x, hx_y⟩, ht_sub, hx_y⟩

/-- The closure of a stratum lies in the union of strata indexed by `t ⊆ s`. -/
lemma Yset_closure_subset [Finite ι] {s : Set X} (hs : s ∈ cKept P) :
    closure (yset P s) ⊆ ⋃ (t ∈ cKept P) (_ : t ⊆ s), yset P t :=
  (closure_minimal (Yset_subset_self P s) (cSet_isClosed P hs.1)).trans
    (cSet_subset_iUnion_Yset P hs.1)

end HelperLemmas

/-- **Stacks 09Y3**.
Every finite partition of a topological space by locally closed subsets is refined
by a finite stratification. -/
@[stacks 09Y3]
theorem exists_finite_stratification_refining_finite_partition
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι] (P : TopPartition X ι) :
    ∃ (κ : Type) (_ : Finite κ) (_ : PartialOrder κ) (S : TopStratification X κ),
      S.toTopPartition.Refines P := by
  have : Fintype ι := Fintype.ofFinite ι
  classical
  have hF : (cKept P).Finite := cKept_finite P
  set N : ℕ := hF.toFinset.card
  let enc : Fin N → Set X := fun i => (hF.toFinset.equivFin.symm i).val
  have enc_inj : Function.Injective enc := fun _ _ hij =>
    hF.toFinset.equivFin.symm.injective (Subtype.ext hij)
  have enc_mem : ∀ i, enc i ∈ cKept P := fun i =>
    (Set.Finite.mem_toFinset _).mp (hF.toFinset.equivFin.symm i).property
  have enc_surj : ∀ s ∈ cKept P, ∃ i, enc i = s := fun s hs =>
    ⟨hF.toFinset.equivFin ⟨s, (Set.Finite.mem_toFinset _).mpr hs⟩, by simp [enc]⟩
  let po : PartialOrder (Fin N) := PartialOrder.lift enc enc_inj
  refine ⟨Fin N, inferInstance, po,
    { parts := fun i => yset P (enc i)
      locallyClosed := fun i => Yset_locallyClosed P (enc_mem i).1
      pairwiseDisjoint := fun i j hij =>
        Yset_pairwiseDisjoint P (enc_mem i).1 (enc_mem j).1 (enc_inj.ne hij)
      iUnion_eq_univ := ?_
      closure_subset := ?_ }, fun i => Yset_refines P (enc_mem i)⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨s, hsC, hxs⟩ := Yset_covers P x
    obtain ⟨i, rfl⟩ := enc_surj s ⟨hsC, x, hxs⟩
    exact Set.mem_iUnion.mpr ⟨i, hxs⟩
  · intro i₀ x hx
    have h := Yset_closure_subset P (enc_mem i₀) hx
    simp only [Set.mem_iUnion, exists_prop] at h
    obtain ⟨t, ht_kept, ht_sub, hxYt⟩ := h
    obtain ⟨j, rfl⟩ := enc_surj t ht_kept
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨j, ht_sub, hxYt⟩
