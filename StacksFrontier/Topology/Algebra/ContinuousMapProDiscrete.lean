module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import StacksFrontier.Topology.Profinite.CechExactness

/-!
# Continuous functions on a compact space with nonarchimedean values

Let `X` be a compact space and `Y` a nonarchimedean topological abelian group. The group `C(X, Y)`
with the compact-open topology is again nonarchimedean: the functions with values in an open
subgroup of `Y` form an open subgroup, and these form a basis of neighbourhoods of zero. If `Y`
is moreover complete with respect to its open subgroups, in the sense that every compatible
family of approximations has a limit, so is `C(X, Y)`: the limit is computed pointwise, and it
is continuous because it is uniformly approximated modulo every open subgroup.

## Main results

* `ContinuousMap.nonarchimedeanAddGroup`: `C(X, Y)` is nonarchimedean.
* `ContinuousMap.isProDiscrete`: `C(X, Y)` is pro-discrete when `Y` is.
-/

@[expose] public section

open Topology Filter Set

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [AddCommGroup Y] [TopologicalSpace Y]
  [NonarchimedeanAddGroup Y]

/-- The continuous functions with values in an open subgroup, an open subgroup of `C(X, Y)`
when `X` is compact. -/
def valuesIn (N : OpenAddSubgroup Y) : OpenAddSubgroup C(X, Y) where
  carrier := {f | ∀ x, f x ∈ N}
  zero_mem' _ := N.zero_mem
  add_mem' hf hg x := N.add_mem (hf x) (hg x)
  neg_mem' hf x := N.neg_mem (hf x)
  isOpen' := by
    have := isOpen_setOfPred_range_subset (X := X) N.isOpen
    convert this using 1
    ext f
    simp [Set.range_subset_iff]

/-- A continuous function lies in `valuesIn N` if and only if all of its values lie in `N`. -/
lemma mem_valuesIn {N : OpenAddSubgroup Y} {f : C(X, Y)} : f ∈ valuesIn N ↔ ∀ x, f x ∈ N :=
  Iff.rfl

/-- Every neighbourhood of zero in `C(X, Y)` contains `valuesIn N` for some open subgroup `N`
of `Y`. -/
lemma exists_valuesIn_subset {s : Set C(X, Y)} (hs : s ∈ 𝓝 (0 : C(X, Y))) :
    ∃ N : OpenAddSubgroup Y, ((valuesIn N : OpenAddSubgroup C(X, Y)) : Set C(X, Y)) ⊆ s := by
  obtain ⟨S, hS, hSU, hsub⟩ := ContinuousMap.mem_nhds_iff.1 hs
  have hT : (⋂ KU ∈ S, {y : Y | KU.1.Nonempty → y ∈ KU.2}) ∈ 𝓝 (0 : Y) := by
    refine (Filter.biInter_mem hS).2 fun KU hKU ↦ ?_
    obtain ⟨-, hU, h0⟩ := hSU KU.1 KU.2 hKU
    by_cases hK : KU.1.Nonempty
    · obtain ⟨k, hk⟩ := hK
      exact Filter.mem_of_superset (hU.mem_nhds (h0 hk)) fun y hy _ ↦ hy
    · exact Filter.univ_mem' fun y h ↦ absurd h hK
  obtain ⟨N, hN⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hT
  refine ⟨N, fun f hf ↦ hsub fun K U hKU x hx ↦ ?_⟩
  have := hN (hf x)
  simp only [Set.mem_iInter] at this
  exact this (K, U) hKU ⟨x, hx⟩

/-- **Continuous functions on a compact space with nonarchimedean values form a nonarchimedean
group.** -/
instance nonarchimedeanAddGroup : NonarchimedeanAddGroup C(X, Y) where
  is_nonarchimedean _ hs := by
    obtain ⟨N, hN⟩ := exists_valuesIn_subset hs
    exact ⟨valuesIn N, hN⟩

/-- **Continuous functions on a compact space with pro-discrete values are pro-discrete.** -/
theorem isProDiscrete (hY : Stacks.ProfiniteCech.IsProDiscrete Y) :
    Stacks.ProfiniteCech.IsProDiscrete C(X, Y) := by
  intro f hf
  have hx : ∀ x : X, ∃ y : Y, ∀ N : OpenAddSubgroup Y, y - f (valuesIn N) x ∈ N := fun x ↦
    hY (fun N ↦ f (valuesIn N) x) fun N N' hNN' ↦ by
      have := hf (valuesIn N) (valuesIn N') fun g hg x ↦ hNN' (hg x)
      simpa using this x
  choose y hy using hx
  have hcont : Continuous y := by
    refine continuous_iff_continuousAt.2 fun x ↦ ?_
    intro U hU
    have h0 : (fun z ↦ z + y x) ⁻¹' U ∈ 𝓝 (0 : Y) := by
      apply ContinuousAt.preimage_mem_nhds (continuous_id.add continuous_const).continuousAt
      simpa using hU
    obtain ⟨N, hN⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
    have hev : ∀ᶠ x' in 𝓝 x, f (valuesIn N) x' - f (valuesIn N) x ∈ N := by
      have hc : Continuous fun x' ↦ f (valuesIn N) x' - f (valuesIn N) x :=
        (f (valuesIn N)).continuous.sub continuous_const
      exact hc.continuousAt.preimage_mem_nhds (by simpa using N.isOpen.mem_nhds N.zero_mem)
    refine Filter.mem_map.2 (Filter.mem_of_superset hev fun x' hx' ↦ ?_)
    have hmem : y x' - y x ∈ N := by
      have e : y x' - y x = (y x' - f (valuesIn N) x') +
          (f (valuesIn N) x' - f (valuesIn N) x) - (y x - f (valuesIn N) x) := by abel
      rw [e]
      exact N.sub_mem (N.add_mem (hy x' N) hx') (hy x N)
    have := hN hmem
    simpa using this
  refine ⟨⟨y, hcont⟩, fun N ↦ ?_⟩
  obtain ⟨M, hM⟩ := exists_valuesIn_subset (N.isOpen.mem_nhds N.zero_mem)
  have hMN : valuesIn M ≤ N := hM
  have h1 : ⟨y, hcont⟩ - f (valuesIn M) ∈ N := hMN fun x ↦ hy x M
  have h2 : f (valuesIn M) - f N ∈ N := hf _ _ hMN
  have := N.add_mem h1 h2
  simpa using this

end ContinuousMap
