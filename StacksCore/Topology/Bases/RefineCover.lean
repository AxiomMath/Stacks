module

public import Mathlib.Topology.Bases

/-!
# A basis refines any open covering

## Main results

* `refine_open_cover_by_basis` (Stacks 004Q): given a topological basis `ℬ` of `X` and an open
  covering `𝓤` of an open set `U`, the basis elements contained in some `𝓤 i` still cover `U`, so
  every open covering of `U` is refined by a covering by basis elements.

## References

* [Stacks Project, Tag 004Q](https://stacks.math.columbia.edu/tag/004Q)
-/

@[expose] public section

/-- **Stacks 004Q.** A basis refines any open covering of an open set: given a topological basis
`ℬ` of `X` and an open covering `𝓤` of an open `U ⊆ X`, the set `V` of basis elements contained in
some `𝓤 i` satisfies `⋃₀ V = U`. -/
@[stacks 004Q]
theorem refine_open_cover_by_basis
    {X : Type*} [TopologicalSpace X]
    {ℬ : Set (Set X)} (hℬ : TopologicalSpace.IsTopologicalBasis ℬ)
    {U : Set X}
    {I : Type*} (𝓤 : I → Set X) (h𝓤 : ∀ i, IsOpen (𝓤 i)) (hU : U = ⋃ i, 𝓤 i) :
    ∃ V : Set (Set X),
      V ⊆ ℬ ∧
      ⋃₀ V = U ∧
      ∀ v ∈ V, ∃ i, v ⊆ 𝓤 i := by
  refine ⟨{B | B ∈ ℬ ∧ ∃ i, B ⊆ 𝓤 i}, fun _ hB ↦ hB.left, ?_, fun _ hv ↦ hv.right⟩
  rw [hU]
  ext x
  simp only [Set.mem_sUnion, Set.mem_ofPred_eq, Set.mem_iUnion]
  refine ⟨fun ⟨_, ⟨_, i, hvi⟩, hxv⟩ ↦ ⟨i, hvi hxv⟩, fun ⟨i, hxi⟩ ↦ ?_⟩
  obtain ⟨B, hBℬ, hxB, hBUi⟩ := hℬ.exists_subset_of_mem_open hxi (h𝓤 i)
  exact ⟨B, ⟨hBℬ, i, hBUi⟩, hxB⟩
