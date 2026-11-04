module

public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Connected fibres and bijections on connected components

A map with connected fibres that detects closed subsets induces a bijection on connected
components. The closed-set condition is `Topology.IsCoinducing f`, expressed by
`Topology.isCoinducing_iff_isClosed`. This condition implies continuity, so the separate
continuity assumption of Tag 0377 is redundant in the formal statement.

## Main results

* `connectedComponentsMap_bijective_of_isClosed_iff` (Stacks 0377): such an `f` induces a bijection
  between the sets of connected components of `X` and of `Y`.

## References

* [Stacks Project, Tag 0377](https://stacks.math.columbia.edu/tag/0377)
-/

@[expose] public section

/-- **Stacks 0377.** Let `f : X → Y` be a map of topological spaces such that all fibres of `f` are
connected and a subset `T ⊆ Y` is closed if and only if `f ⁻¹' T` is closed. Then `f` induces a
bijection between the sets of connected components of `X` and `Y`. -/
@[stacks 0377]
theorem connectedComponentsMap_bijective_of_isClosed_iff
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hfib : ∀ y, IsConnected (f ⁻¹' {y}))
    (hcl : ∀ T : Set Y, IsClosed (f ⁻¹' T) ↔ IsClosed T) :
    Function.Bijective
      ((Topology.isCoinducing_iff_isClosed.mpr hcl).continuous.connectedComponentsMap) :=
  (Topology.isCoinducing_iff_isClosed.mpr hcl).connectedComponentsMap_bijective hfib
