module

public import Mathlib.Topology.LocallyClosed
import StacksCore.Tactic.StacksAttribute

/-!
# Surjective closed continuous maps are submersive

A surjective closed continuous map `f : X → Y` identifies the topology of `Y` with the quotient
topology, so closedness, openness and local closedness of a subset `T ⊆ Y` can all be tested on
`f ⁻¹' T`, and the closure of `T` is the image of the closure of `f ⁻¹' T`.

## Main results

* `IsClosedMap.image_closure_preimage_eq_closure` (Stacks 0AAU, part 1):
  `f '' closure (f ⁻¹' T) = closure T` whenever `T ⊆ Set.range f`.
* `Topology.IsCoinducing.isClosed_preimage` (part 2) and
  `Topology.IsCoinducing.isOpen_preimage` (part 3) are registered directly from Mathlib.
* `isLocallyClosed_iff_preimage_isLocallyClosed` (part 4): `T` is locally closed exactly when
  `f ⁻¹' T` is.
* `IsClosedMap.isQuotientMap` is registered for the submersive conclusion.

## References

* [Stacks Project, Tag 0AAU](https://stacks.math.columbia.edu/tag/0AAU)
-/

@[expose] public section

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- **Stacks 0AAU** (part 1). A closed continuous map carries the closure of the preimage of
a subset of its range onto the closure of that subset. -/
@[stacks 0AAU "(1)"]
theorem IsClosedMap.image_closure_preimage_eq_closure
    (hf_closed : IsClosedMap f) (hf_cont : Continuous f) {T : Set Y}
    (hT : T ⊆ range f) :
    f '' closure (f ⁻¹' T) = closure T := by
  rw [← hf_closed.closure_image_eq_of_continuous hf_cont, image_preimage_eq_of_subset hT]

add_to_stacks 0AAU "(2)" IsCoinducing.isClosed_preimage

add_to_stacks 0AAU "(3)" IsCoinducing.isOpen_preimage

add_to_stacks 0AAU "submersive" IsClosedMap.isQuotientMap

/-- **Stacks 0AAU** (part 4). For a surjective closed continuous map `f : X → Y` and any `T ⊆ Y`,
`T` is locally closed iff `f ⁻¹' T` is locally closed. -/
@[stacks 0AAU "(4)"]
theorem isLocallyClosed_iff_preimage_isLocallyClosed
    (hf_surj : Function.Surjective f) (hf_cont : Continuous f)
    (hf_closed : IsClosedMap f) (T : Set Y) :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := by
  refine ⟨fun h ↦ h.preimage hf_cont, fun h ↦ ?_⟩
  rw [isLocallyClosed_iff_isOpen_coborder, coborder, isOpen_compl_iff] at h ⊢
  simpa [image_sdiff_preimage, ← hf_closed.closure_image_eq_of_continuous hf_cont,
    hf_surj.image_preimage] using hf_closed _ h
