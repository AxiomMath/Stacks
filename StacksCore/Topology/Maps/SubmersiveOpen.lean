module

public import Mathlib.Topology.LocallyClosed
import StacksCore.Tactic.StacksAttribute

/-!
# Surjective open continuous maps are submersive

A surjective open continuous map `f : X → Y` identifies the topology of `Y` with the quotient
topology, so closedness, openness and local closedness of a subset `T ⊆ Y` can all be tested on
`f ⁻¹' T`, and closure commutes with taking preimages.

## Main results

* `IsOpenMap.preimage_closure_eq_closure_preimage` (Stacks 02YB, part 1) is registered directly
  from Mathlib and does not require surjectivity.
* `Topology.IsCoinducing.isClosed_preimage` (part 2) and
  `Topology.IsCoinducing.isOpen_preimage` (part 3) are registered directly from Mathlib.
* `Topology.IsCoinducing.isLocallyClosed_iff_preimage` (part 4): an open coinducing map detects
  locally closed subsets.
* `IsOpenMap.isQuotientMap` is registered for the submersive conclusion.

## References

* [Stacks Project, Tag 02YB](https://stacks.math.columbia.edu/tag/02YB)
-/

@[expose] public section

open Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

add_to_stacks 02YB "(1)" IsOpenMap.preimage_closure_eq_closure_preimage

add_to_stacks 02YB "(2)" IsCoinducing.isClosed_preimage

add_to_stacks 02YB "(3)" IsCoinducing.isOpen_preimage

/-- **Stacks 02YB** (part 4). An open coinducing map detects locally closed subsets. -/
@[stacks 02YB "(4)"]
theorem Topology.IsCoinducing.isLocallyClosed_iff_preimage
    {f : X → Y} (hf : IsCoinducing f) (hopen : IsOpenMap f) (T : Set Y) :
    IsLocallyClosed T ↔ IsLocallyClosed (f ⁻¹' T) := by
  simp [isLocallyClosed_iff_isOpen_coborder, coborder_preimage hopen hf.continuous,
    hf.isOpen_preimage]

add_to_stacks 02YB "submersive" IsOpenMap.isQuotientMap
add_to_sga "1 IX 2.2" "a) surjective open case" IsOpenMap.isQuotientMap
