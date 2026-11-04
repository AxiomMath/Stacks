module

public import Mathlib.Topology.ShrinkingLemma

/-!
# Shrinking an open cover of a quasi-compact Hausdorff space

Extract a finite subcover, replace the remaining members by the empty set, and apply Mathlib's
shrinking lemma to this point-finite cover. The refinement retains the original index set.

## Main results

* `relatively_compact_refinement` (Stacks 09UV): every open cover of a quasi-compact Hausdorff
  space admits an open cover with the same index set satisfying `closure (V i) ⊆ U i`.

## References

* [Stacks Project, Tag 09UV](https://stacks.math.columbia.edu/tag/09UV)
-/

@[expose] public section

open Set

/-- **Stacks 09UV.** Let `X` be a quasi-compact Hausdorff space and `U : I → Set X` an open cover.
Then there is an open cover `V : I → Set X` with the same index set such that
`closure (V i) ⊆ U i` for every `i`.

A quasi-compact Hausdorff space is normal, so the shrinking lemma applies once the cover has been
made point-finite: extract a finite subcover indexed by `J : Finset I` and replace `U i` by `∅`
for `i ∉ J`. -/
@[stacks 09UV]
theorem relatively_compact_refinement
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {I : Type*} (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcov : ⋃ i, U i = Set.univ) :
    ∃ V : I → Set X, (∀ i, IsOpen (V i)) ∧ (⋃ i, V i = Set.univ) ∧
      (∀ i, closure (V i) ⊆ U i) := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : Finset I, (Set.univ : Set X) ⊆ ⋃ i ∈ J, U i :=
    isCompact_univ.elim_finite_subcover U hUopen hUcov.ge
  let U' : I → Set X := fun i ↦ if i ∈ J then U i else ∅
  have hU'_subset (i) : U' i ⊆ U i := by by_cases h : i ∈ J <;> simp [U', h]
  have hU'_open (i) : IsOpen (U' i) := by by_cases h : i ∈ J <;> simp [U', h, hUopen i]
  have hU'_cov : ⋃ i, U' i = Set.univ := by
    refine eq_univ_of_univ_subset fun x hx ↦ ?_
    obtain ⟨i, hiJ, hxU⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion.mpr ⟨i, by simp [U', hiJ, hxU]⟩
  have hU'_pointFinite (x : X) : {i | x ∈ U' i}.Finite :=
    J.finite_toSet.subset fun i hi ↦ by
      have hi' : i ∈ J ∧ x ∈ U i := by simpa [U'] using hi
      exact hi'.1
  obtain ⟨V, hVcov, hVopen, hVcl⟩ :=
    exists_iUnion_eq_closure_subset hU'_open hU'_pointFinite hU'_cov
  exact ⟨V, hVopen, hVcov, fun i ↦ (hVcl i).trans (hU'_subset i)⟩
