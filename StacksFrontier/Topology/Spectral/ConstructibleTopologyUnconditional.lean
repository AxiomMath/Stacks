module
public import StacksFrontier.Topology.Spectral.ConstructibleTopology
import all StacksFrontier.Topology.Spectral.ConstructibleTopology

public import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Closed sets of the constructible topology

On a quasi-compact quasi-separated space, constructible subsets are closed in the constructible
topology.

## Main results

* `WithConstructibleTopology.isClosed_preimage_ofConstructible_of_isConstructible`: the preimage
  of a constructible subset in `WithConstructibleTopology X` is closed.
-/

@[expose] public section

open Set Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]

namespace WithConstructibleTopology

/-- **A constructible subset is closed in the constructible topology.** For `X` quasi-compact
and quasi-separated and `Z ⊆ X` constructible, the preimage of `Z` in the type synonym
`WithConstructibleTopology X` is closed. -/
theorem isClosed_preimage_ofConstructible_of_isConstructible [CompactSpace X]
    [QuasiSeparatedSpace X] {Z : Set X} (hZ : Topology.IsConstructible Z) :
    IsClosed (ofConstructible ⁻¹' Z : Set (WithConstructibleTopology X)) := by
  rw [← isOpen_compl_iff, ← Set.preimage_compl, isOpen_preimage_ofConstructible,
    constructibleTopology_eq_generateFrom_isConstructible X]
  exact TopologicalSpace.isOpen_generateFrom_of_mem hZ.compl

end WithConstructibleTopology

namespace Topology

end Topology
