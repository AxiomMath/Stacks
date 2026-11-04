module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.OpenSubgroup
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# The open mapping lemma for topological abelian groups

Let `u : N → M` be a continuous homomorphism of topological abelian groups. Assume that `M` is
separated and that `N` is complete, linearly topologized, and has a countable fundamental system
of neighbourhoods of `0`. Then exactly one of the following holds: `u` is open, or there is an
open subgroup `N'` of `N` whose image `u(N')` is nowhere dense in `M`.

## Main definitions

* `IsLinearlyTopologized`: `0` has a fundamental system of neighbourhoods consisting of open
  subgroups.
* `HasCountableFundamentalSystem`: the neighbourhood filter of `0` is countably generated.
* `IsGroupCauchy`: a nontrivial filter along which the differences `p.2 - p.1` tend to `0`.
* `IsGroupComplete`: separated, and every group-Cauchy filter converges.

## Main results

* `open_mapping_lemma_exclusive`: if `u` is open, no open subgroup has nowhere dense image.
* `open_mapping_lemma_dichotomy`: if no open subgroup has nowhere dense image, `u` is open.
* `open_mapping_lemma`: exactly one of the two alternatives holds.

## References

* [Stacks Project, Tag 0CQW](https://stacks.math.columbia.edu/tag/0CQW)
* [Stacks Project, Tag 07E7](https://stacks.math.columbia.edu/tag/07E7)
-/

open Topology Filter

/-- A topological additive group `M` is *linearly topologized* if `0` has a fundamental system
of neighbourhoods consisting of open subgroups, i.e. the neighbourhood filter of `0` has a basis
consisting of the underlying sets of open subgroups of `M`. -/
def IsLinearlyTopologized (M : Type*) [AddGroup M] [TopologicalSpace M] : Prop :=
  (𝓝 (0 : M)).HasBasis (fun U : AddSubgroup M => IsOpen (U : Set M)) (fun U => (U : Set M))

/-- In a linearly topologized group the neighbourhood filter of `0` has a basis consisting
of the open subgroups. -/
theorem IsLinearlyTopologized.hasBasis_open_addSubgroup {M : Type*} [AddGroup M]
    [TopologicalSpace M] (h : IsLinearlyTopologized M) :
    (𝓝 (0 : M)).HasBasis (fun U : AddSubgroup M => IsOpen (U : Set M))
      (fun U => (U : Set M)) := h

/-- A topological group `N` *has a countable fundamental system of neighbourhoods of `0`* if the
neighbourhood filter of `0` is countably generated. -/
def HasCountableFundamentalSystem (N : Type*) [Zero N] [TopologicalSpace N] : Prop :=
  (𝓝 (0 : N)).IsCountablyGenerated

/-- The neighbourhood filter of `0` of a group with a countable fundamental system of
neighbourhoods of `0` is countably generated. -/
theorem HasCountableFundamentalSystem.isCountablyGenerated {N : Type*} [Zero N]
    [TopologicalSpace N] (h : HasCountableFundamentalSystem N) :
    (𝓝 (0 : N)).IsCountablyGenerated := h

/-- A filter `F` on a topological additive group is *Cauchy* for the group uniformity if it is
nontrivial and the differences `p.2 - p.1` tend to `0` along `F ×ˢ F`. -/
def IsGroupCauchy {N : Type*} [AddGroup N] [TopologicalSpace N] (F : Filter N) : Prop :=
  F.NeBot ∧ Tendsto (fun p : N × N => p.2 - p.1) (F ×ˢ F) (𝓝 0)

/-- A group-Cauchy filter is nontrivial. -/
theorem IsGroupCauchy.neBot {N : Type*} [AddGroup N] [TopologicalSpace N] {F : Filter N}
    (h : IsGroupCauchy F) : F.NeBot := h.1

/-- Along a group-Cauchy filter the differences `p.2 - p.1` tend to `0`. -/
theorem IsGroupCauchy.tendsto_sub {N : Type*} [AddGroup N] [TopologicalSpace N]
    {F : Filter N} (h : IsGroupCauchy F) :
    Tendsto (fun p : N × N => p.2 - p.1) (F ×ˢ F) (𝓝 0) := h.2

/-- A topological additive group `N` is *complete* if it is separated (`T2Space N`) and every
group-Cauchy filter on `N` converges. -/
@[sga "6 V 1.3" "partial"]
def IsGroupComplete (N : Type*) [AddGroup N] [TopologicalSpace N] : Prop :=
  T2Space N ∧ ∀ F : Filter N, IsGroupCauchy F → ∃ x : N, F ≤ 𝓝 x

/-- A complete topological additive group is separated. -/
theorem IsGroupComplete.t2Space {N : Type*} [AddGroup N] [TopologicalSpace N]
    (h : IsGroupComplete N) : T2Space N := h.1

/-- In a complete topological additive group every group-Cauchy filter converges. -/
theorem IsGroupComplete.exists_le_nhds {N : Type*} [AddGroup N] [TopologicalSpace N]
    (h : IsGroupComplete N) {F : Filter N} (hF : IsGroupCauchy F) : ∃ x : N, F ≤ 𝓝 x :=
  h.2 F hF

/-- An additive subgroup with nonempty interior is open. -/
theorem AddSubgroup.isOpen_of_interior_nonempty {M : Type*} [AddGroup M]
    [TopologicalSpace M] [SeparatelyContinuousAdd M] (H : AddSubgroup M)
    (h : (interior (H : Set M)).Nonempty) : IsOpen (H : Set M) :=
  let ⟨_, hx⟩ := h
  H.isOpen_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)

/-- If the image `u '' N'` of a subgroup `N'` is not nowhere dense, then its topological closure
`closure (u '' N')` is an *open* subgroup of `M`. -/
theorem isOpen_topologicalClosure_map_of_not_isNowhereDense
    {N : Type*} [AddGroup N]
    {M : Type*} [AddGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (u : N →+ M) {N' : AddSubgroup N}
    (h : ¬ IsNowhereDense (u '' (N' : Set N))) :
    IsOpen (((N'.map u).topologicalClosure) : Set M) := by
  refine AddSubgroup.isOpen_of_interior_nonempty _ ?_
  simpa using Set.nonempty_iff_ne_empty.mpr h

/-- If `z` lies in the closure of `u '' S` and `H` is an open subgroup, then `z` differs from
some `u a` with `a ∈ S` by an element of `H`. -/
theorem exists_sub_mem_of_mem_closure_image {N M : Type*} [AddGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] (u : N → M) (S : Set N) (H : AddSubgroup M)
    (hH : IsOpen (H : Set M)) {z : M} (hz : z ∈ closure (u '' S)) : ∃ a ∈ S, z - u a ∈ H := by
  have hnbhd : {p : M | p - z ∈ (H : Set M)} ∈ 𝓝 z :=
    (continuous_sub_right z).continuousAt.preimage_mem_nhds
      (by simpa using hH.mem_nhds H.zero_mem)
  obtain ⟨_, hp, a, ha, rfl⟩ := mem_closure_iff_nhds.mp hz _ hnbhd
  exact ⟨a, ha, by simpa using H.neg_mem hp⟩

/-- In a regular target, the closures of the images of a neighbourhood basis of `x` under a map
continuous at `x` are eventually contained in any neighbourhood of `f x`. -/
theorem exists_closure_image_subset_of_mem_nhds {N M : Type*} [TopologicalSpace N]
    [TopologicalSpace M] [RegularSpace M] {f : N → M} {x : N} (hf : ContinuousAt f x)
    {ι : Sort*} {p : ι → Prop} {s : ι → Set N} (hs : (𝓝 x).HasBasis p s) {V : Set M}
    (hV : V ∈ 𝓝 (f x)) : ∃ i, p i ∧ closure (f '' s i) ⊆ V := by
  obtain ⟨V', ⟨hV'n, hV'c⟩, hV'V⟩ := (closed_nhds_basis (f x)).mem_iff.mp hV
  obtain ⟨i, hi, hK⟩ := hs.mem_iff.mp (hf.preimage_mem_nhds hV'n)
  exact ⟨i, hi, (closure_minimal (Set.image_subset_iff.mpr hK) hV'c).trans hV'V⟩

/-- If `y i ∈ Nseq i` along a decreasing neighbourhood basis `Nseq` of `0` consisting of
subgroups, then the partial sums of `y` form a group-Cauchy sequence. -/
theorem isGroupCauchy_map_partialSums {N : Type*} [AddCommGroup N] [TopologicalSpace N]
    (Nseq : ℕ → AddSubgroup N)
    (hNseq_basis : (𝓝 (0 : N)).HasAntitoneBasis (fun i => ((Nseq i) : Set N)))
    (y : ℕ → N) (hy : ∀ i, y i ∈ Nseq i) :
    IsGroupCauchy (map (fun m => ∑ i ∈ Finset.range m, y i) atTop) := by
  have hle : ∀ k p q, k ≤ p → p ≤ q →
      ∑ i ∈ Finset.range q, y i - ∑ i ∈ Finset.range p, y i ∈ Nseq k := by
    intro k p q hkp hpq
    rw [← Finset.sum_Ico_eq_sub _ hpq]
    exact (Nseq k).sum_mem fun i hi =>
      hNseq_basis.antitone (hkp.trans (Finset.mem_Ico.mp hi).1) (hy i)
  refine ⟨atTop_neBot.map _, ?_⟩
  rw [Filter.prod_map_map_eq, Filter.tendsto_map'_iff,
    hNseq_basis.toHasBasis.tendsto_right_iff]
  intro k _
  rw [Filter.eventually_prod_iff]
  refine ⟨(k ≤ ·), eventually_ge_atTop k, (k ≤ ·), eventually_ge_atTop k, ?_⟩
  intro a ha b hb
  rcases le_total a b with h | h
  · exact hle k a b ha h
  · simpa using (Nseq k).neg_mem (hle k b a hb h)

/-- If `u` is open, then no open subgroup of `N` has nowhere dense image. -/
theorem open_mapping_lemma_exclusive
    {N : Type*} [AddGroup N] [TopologicalSpace N]
    {M : Type*} [AddGroup M] [TopologicalSpace M]
    (u : N →+ M)
    (hopen : IsOpenMap u) :
    ¬ ∃ N' : AddSubgroup N, IsOpen (N' : Set N) ∧ IsNowhereDense (u '' (N' : Set N)) := by
  rintro ⟨N', hN'open, hnd⟩
  have hne : (u '' (N' : Set N)).Nonempty := ⟨u 0, 0, N'.zero_mem, rfl⟩
  have h1 := (hopen _ hN'open).subset_interior_closure
  rw [hnd] at h1
  exact hne.ne_empty (Set.subset_empty_iff.mp h1)

section

variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- Let `N` be complete and `M` separated, let `Nseq` be an antitone neighbourhood basis of `0`
in `N` consisting of open subgroups, and suppose every `closure (u '' Nₖ)` is open. Then
`closure (u '' Nₙ) ⊆ u '' Nₙ` for each `n`. -/
theorem closure_image_subset_image_of_isGroupComplete
    [T2Space M]
    (u : N →+ M) (hu : Continuous u)
    (hNcomplete : IsGroupComplete N)
    (Nseq : ℕ → AddSubgroup N)
    (hNseq_open : ∀ i, IsOpen ((Nseq i) : Set N))
    (hNseq_basis : (𝓝 (0 : N)).HasAntitoneBasis (fun i => ((Nseq i) : Set N)))
    (hMn_open : ∀ i, IsOpen (((Nseq i).map u).topologicalClosure : Set M))
    (n : ℕ) :
    (closure (u '' ((Nseq n) : Set N))) ⊆ u '' ((Nseq n) : Set N) := by
  set Msub : ℕ → AddSubgroup M := fun k => ((Nseq k).map u).topologicalClosure with hMsub_def
  have hMcoe : ∀ k, (Msub k : Set M) = closure (u '' (Nseq k : Set N)) := fun k => by
    simp only [hMsub_def, AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map]
  have hNanti : Antitone (fun i => (Nseq i : Set N)) := hNseq_basis.antitone
  have hManti : ∀ j l, j ≤ l → (Msub l : Set M) ⊆ Msub j := fun j l hjl => by
    rw [hMcoe, hMcoe]
    exact closure_mono (Set.image_mono (hNanti hjl))
  have hkey : ∀ k, ∀ z ∈ (Msub k : Set M), ∃ a ∈ Nseq k, z - u a ∈ Msub (k+1) := fun k z hz =>
    exists_sub_mem_of_mem_closure_image u _ _ (hMn_open (k+1)) (by rwa [hMcoe] at hz)
  intro x hx
  rw [← hMcoe n] at hx
  let xpair : (i : ℕ) → { z : M // z ∈ Msub (n + i) } :=
    fun i => Nat.rec (motive := fun i => { z : M // z ∈ Msub (n + i) })
      ⟨x, hx⟩
      (fun i prev =>
        ⟨prev.val - u (Classical.choose (hkey (n + i) prev.val prev.property)), by
          rw [Nat.succ_eq_add_one, ← Nat.add_assoc]
          exact (Classical.choose_spec (hkey (n + i) prev.val prev.property)).2⟩)
      i
  let yseq : ℕ → N := fun i => Classical.choose (hkey (n + i) (xpair i).val (xpair i).property)
  let xseq : ℕ → M := fun i => (xpair i).val
  have hxseq_mem : ∀ i, xseq i ∈ Msub (n + i) := fun i => (xpair i).property
  have hyseq_mem : ∀ i, yseq i ∈ Nseq (n + i) := fun i =>
    (Classical.choose_spec (hkey (n + i) (xpair i).val (xpair i).property)).1
  have hstep : ∀ i, xseq (i + 1) = xseq i - u (yseq i) := fun _ => rfl
  let sseq : ℕ → N := fun m => ∑ i ∈ Finset.range m, yseq i
  have htele : ∀ m, u (sseq m) = x - xseq m := by
    intro m
    induction m with
    | zero => simp [sseq, show xseq 0 = x from rfl]
    | succ k ih =>
      rw [show sseq (k + 1) = sseq k + yseq k from Finset.sum_range_succ _ _, map_add, ih,
        hstep k]
      abel
  obtain ⟨y, hy⟩ := hNcomplete.exists_le_nhds (isGroupCauchy_map_partialSums Nseq hNseq_basis yseq
    fun i => hNanti (Nat.le_add_left i n) (hyseq_mem i))
  have hy : Tendsto sseq atTop (𝓝 y) := hy
  have hyNn : y ∈ (Nseq n : Set N) :=
    ((Nseq n).isClosed_of_isOpen (hNseq_open n)).mem_of_tendsto hy <| .of_forall fun _ =>
      (Nseq n).sum_mem fun i _ => hNanti (Nat.le_add_right n i) (hyseq_mem i)
  have hxseq_tendsto : Tendsto xseq atTop (𝓝 0) := by
    refine tendsto_def.mpr fun V hV => ?_
    obtain ⟨K, -, hK⟩ := exists_closure_image_subset_of_mem_nhds hu.continuousAt
      hNseq_basis.toHasBasis (by simpa using hV)
    exact mem_atTop_sets.mpr ⟨K, fun m hm =>
      hK ((hMcoe K).subset (hManti K (n + m) (by omega) (hxseq_mem m)))⟩
  exact ⟨y, hyNn, tendsto_nhds_unique ((hu.tendsto y).comp hy)
    (by simpa [Function.comp_def, htele] using hxseq_tendsto.const_sub x)⟩

/-- If `u : N →+ M` is a group homomorphism and the images `u '' s i` of the members of a
neighbourhood basis `s` of `0` in `N` are open in `M`, then `u` is an open map. -/
theorem isOpenMap_of_hasBasis_image_isOpen
    (u : N →+ M) {ι : Sort*} {p : ι → Prop} {s : ι → Set N}
    (hs : (𝓝 (0 : N)).HasBasis p s) (himg_open : ∀ i, p i → IsOpen (u '' s i)) :
    IsOpenMap u := by
  intro W hW
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨w, hwW, rfl⟩
  have hpre : (fun n => n + w) ⁻¹' W ∈ 𝓝 (0 : N) :=
    (continuous_add_const w).continuousAt.preimage_mem_nhds (by simpa using hW.mem_nhds hwW)
  obtain ⟨i, hi, hn⟩ := hs.mem_iff.mp hpre
  have hsub : (fun m => u w + m) '' (u '' s i) ⊆ u '' W := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a + w, hn ha, by simp [map_add, add_comm]⟩
  exact Filter.mem_of_superset ((isOpenMap_add_left (u w) _ (himg_open i hi)).mem_nhds
    ⟨0, ⟨0, mem_of_mem_nhds (hs.mem_of_mem hi), map_zero u⟩, add_zero _⟩) hsub

/-- Let `u : N →+ M` be continuous, with `M` separated and `N` complete, linearly topologized
and with a countable fundamental system of neighbourhoods of `0`. If no open subgroup of `N` has
nowhere dense image under `u`, then `u` is open. -/
theorem open_mapping_lemma_dichotomy
    [T2Space M]
    (u : N →+ M) (hu : Continuous u)
    (hNcomplete : IsGroupComplete N)
    (hNlin : IsLinearlyTopologized N)
    (hNcount : HasCountableFundamentalSystem N)
    (h : ∀ N' : AddSubgroup N, IsOpen (N' : Set N) → ¬ IsNowhereDense (u '' (N' : Set N))) :
    IsOpenMap u := by
  have : (𝓝 (0 : N)).IsCountablyGenerated := hNcount.isCountablyGenerated
  obtain ⟨Nseq, hNseq_open, hNseq_basis⟩ :=
    hNlin.hasBasis_open_addSubgroup.exists_antitone_subbasis
  have hMn_open : ∀ i, IsOpen (((Nseq i).map u).topologicalClosure : Set M) := fun i =>
    isOpen_topologicalClosure_map_of_not_isNowhereDense u (h (Nseq i) (hNseq_open i))
  refine isOpenMap_of_hasBasis_image_isOpen u hNseq_basis.toHasBasis fun i _ => ?_
  have := hMn_open i
  rw [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_map] at this
  rwa [subset_closure.antisymm (closure_image_subset_image_of_isGroupComplete u hu hNcomplete
    Nseq hNseq_open hNseq_basis hMn_open i)]

/-- Let `u : N → M` be a continuous homomorphism of topological abelian groups. Assume that `M`
is separated, and that `N` is complete (which, by `IsGroupComplete`, includes separatedness of
`N`), linearly topologized, and has a countable fundamental system of neighbourhoods of `0`. Then
exactly one of the following two statements holds:

1. `u` is open; or
2. there exists an open subgroup `N' ⊆ N` such that the image `u(N')` is nowhere dense in `M`. -/
@[stacks 0CQW]
theorem open_mapping_lemma
    {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [T2Space M]
    (u : N →+ M) (hu : Continuous u)
    (hNcomplete : IsGroupComplete N)
    (hNlin : IsLinearlyTopologized N)
    (hNcount : HasCountableFundamentalSystem N) :
    Xor (IsOpenMap u)
      (∃ N' : AddSubgroup N, IsOpen (N' : Set N) ∧ IsNowhereDense (u '' (N' : Set N))) := by
  by_cases h2 : ∃ N' : AddSubgroup N, IsOpen (N' : Set N) ∧ IsNowhereDense (u '' (N' : Set N))
  · exact Or.inr ⟨h2, fun hopen => open_mapping_lemma_exclusive u hopen h2⟩
  · exact Or.inl ⟨open_mapping_lemma_dichotomy u hu hNcomplete hNlin hNcount
      fun N' hN' hnd => h2 ⟨N', hN', hnd⟩, h2⟩

end
