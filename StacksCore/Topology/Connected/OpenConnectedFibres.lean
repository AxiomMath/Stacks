module

public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# An open map with connected fibres is a bijection on connected components

A continuous open map with connected fibres is surjective, since its fibres are nonempty.
It is therefore a quotient map, and Mathlib's
`Topology.IsCoinducing.connectedComponentsMap_bijective` gives the bijection on connected
components.

## Main results

* `bijective_connectedComponentsMap_of_isOpenMap` (Stacks 0378): a continuous open map with
  connected fibres induces a bijection between the sets of connected components.

## References

* [Stacks Project, Tag 0378](https://stacks.math.columbia.edu/tag/0378)
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Stacks 0378.** A continuous open map with connected fibres induces a bijection between the
sets of connected components. -/
@[stacks 0378]
theorem bijective_connectedComponentsMap_of_isOpenMap
    (f : X → Y) (hf_cont : Continuous f) (hf_open : IsOpenMap f)
    (hf_fib : ∀ y : Y, IsConnected (f ⁻¹' {y})) :
    Function.Bijective (hf_cont.connectedComponentsMap) := by
  have hquot := hf_open.isQuotientMap hf_cont fun y ↦ (hf_fib y).nonempty
  exact hquot.isCoinducing.connectedComponentsMap_bijective hf_fib
