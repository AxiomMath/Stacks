module

public import Mathlib.Topology.Compactness.LocallyCompact
import StacksCore.Tactic.StacksAttribute

/-!
# Locally quasi-compact spaces

Stacks 0068 defines a topological space to be *locally quasi-compact* if every point has a
fundamental system of quasi-compact neighbourhoods.

This is Mathlib's `LocallyCompactSpace`, whose single field
`∀ x, ∀ n ∈ 𝓝 x, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s` spells out that condition. Note that Mathlib's
`WeaklyLocallyCompactSpace` is instead the weaker convention, mentioned in the Stacks footnote,
that each point merely has *some* quasi-compact neighbourhood.

## Main results

* `LocallyCompactSpace` (Stacks 0068): the class of locally quasi-compact spaces.
* `IsOpenMap.hasBasis_nhds_isOpen_isCompact`: a fundamental system of quasi-compact *open*
  neighbourhoods is carried along a continuous open surjection, by taking images.

## References

* [Stacks Project, Tag 0068](https://stacks.math.columbia.edu/tag/0068)
-/

@[expose] public section

add_to_stacks 0068 "a locally quasi-compact space" LocallyCompactSpace

/-- A continuous open surjection carries a fundamental system of quasi-compact open
neighbourhoods to one: the image of such a neighbourhood of a preimage of `y` is open because
the map is open, quasi-compact because it is continuous, and contains `y`. -/
theorem IsOpenMap.hasBasis_nhds_isOpen_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hopen : IsOpenMap f) (hcont : Continuous f)
    (hsurj : Function.Surjective f)
    (hbasis : ∀ x : X, (nhds x).HasBasis (fun U : Set X ↦ IsOpen U ∧ IsCompact U ∧ x ∈ U) id)
    (y : Y) :
    (nhds y).HasBasis (fun V : Set Y ↦ IsOpen V ∧ IsCompact V ∧ y ∈ V) id := by
  obtain ⟨x, rfl⟩ := hsurj y
  have himage := (hbasis x).map f
  rw [hopen.map_nhds_eq hcont.continuousAt] at himage
  refine himage.to_hasBasis' ?_ ?_
  · rintro U ⟨hU, hUc, hxU⟩
    exact ⟨f '' U, ⟨hopen U hU, hUc.image hcont, ⟨x, hxU, rfl⟩⟩, Set.Subset.rfl⟩
  · rintro V ⟨hV, -, hxV⟩
    exact hV.mem_nhds hxV
