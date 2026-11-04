module

public import Mathlib.Topology.Constructible
import StacksCore.Tactic.StacksAttribute

/-!
# Images of quasi-compact spaces and of quasi-compact maps

## Main results

* `isCompact_range` (Stacks 04Z9, part 1) is registered directly from Mathlib: the continuous
  image of a quasi-compact space is quasi-compact.
* `IsSpectralMap.isRetrocompact_range` (Stacks 04Z9, part 2): the image of a quasi-compact
  continuous map is retrocompact. Mathlib's `IsSpectralMap` expresses continuity and
  quasi-compactness of preimages of quasi-compact opens, without requiring spectral spaces.

## References

* [Stacks Project, Tag 04Z9](https://stacks.math.columbia.edu/tag/04Z9)
-/

@[expose] public section

add_to_stacks 04Z9 "(1)" isCompact_range

/-- **Stacks 04Z9** (part 2). If `f : X → Y` is continuous and quasi-compact as a map, then its
image `f(X)` is retrocompact in `Y`: it meets every quasi-compact open in a quasi-compact set. -/
@[stacks 04Z9 "part (2)"]
theorem IsSpectralMap.isRetrocompact_range
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsSpectralMap f) :
    IsRetrocompact (Set.range f) := fun _ hUcompact hUopen ↦ by
  rw [Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  exact (hf.isCompact_preimage_of_isOpen hUopen hUcompact).image hf.continuous
