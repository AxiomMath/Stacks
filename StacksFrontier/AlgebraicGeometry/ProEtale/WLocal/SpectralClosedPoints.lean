module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Spectral.Basic

/-!
# Closed points in the connected components of a spectral space

A spectral space is compact and Kolmogorov, and each of its connected components is closed.
Applying to a connected component the fact that a nonempty closed subset of a compact
Kolmogorov space contains a point closed in the ambient space, one finds a point of the
component whose singleton is closed in the whole space. This is the input used when a w-local
space is analysed one connected component at a time: the chosen point is closed in the space,
not merely in the component.

## Main results

* `SpectralSpace.exists_isClosed_singleton_mem_connectedComponent`: every connected component
  of a spectral space contains a point which is closed in the ambient space.

## Implementation notes

Closedness is asserted for the singleton inside the ambient space, which is stronger than
closedness in the subspace topology of the connected component and is what the consumers need.

## References

* [Stacks Project, Tag 005E](https://stacks.math.columbia.edu/tag/005E)
* [Stacks Project, Tag 004T](https://stacks.math.columbia.edu/tag/004T)
-/

@[expose] public section

namespace SpectralSpace

/-- Every connected component of a spectral space contains a point that is closed in the
ambient space. -/
theorem exists_isClosed_singleton_mem_connectedComponent
    {X : Type*} [TopologicalSpace X] [SpectralSpace X] (x : X) :
    ∃ y ∈ connectedComponent x, IsClosed ({y} : Set X) :=
  isClosed_connectedComponent.exists_closed_singleton ⟨x, mem_connectedComponent⟩

end SpectralSpace

end
