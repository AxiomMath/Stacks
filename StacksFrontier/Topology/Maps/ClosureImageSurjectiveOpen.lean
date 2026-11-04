module

public import Mathlib.Topology.LocallyClosed
public import StacksCore.Tactic.StacksAttribute

/-!
# Images of closures along a surjective open map

Let `q : X → Y` be a surjective open continuous map and let `π : Y → Z` be any map. If a closed
subset `T ⊆ X` contains the preimage `q ⁻¹' A` of a subset `A ⊆ Y`, then it already contains the
preimage of the closure of `A`, so the image of `closure A` under `π` is contained in the image of
`T` under `π ∘ q`.

## Main results

* `IsOpenMap.image_closure_subset_image_of_preimage_subset`: the inclusion
  `π '' closure A ⊆ (π ∘ q) '' T`.
-/

@[expose] public section

/-- For a surjective open continuous map `q : X → Y`, a closed subset `T ⊆ X` containing
`q ⁻¹' A` also contains `q ⁻¹' closure A`; hence the image of `closure A` along any map
`π : Y → Z` is contained in the image of `T` along `π ∘ q`. -/
@[stacks 0H29 "the closure step of the proof, along a surjective open map"]
theorem IsOpenMap.image_closure_subset_image_of_preimage_subset
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] {q : X → Y}
    (hopen : IsOpenMap q) (hcont : Continuous q) (hsurj : Function.Surjective q) (π : Y → Z)
    {A : Set Y} {T : Set X} (hT : IsClosed T) (h : q ⁻¹' A ⊆ T) :
    π '' closure A ⊆ (π ∘ q) '' T := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, rfl⟩ := hsurj y
  refine ⟨x, ?_, rfl⟩
  exact hT.closure_subset_iff.mpr h
    (by rw [← hopen.preimage_closure_eq_closure_preimage hcont]; exact hy)

end
