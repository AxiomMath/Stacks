module

public import Mathlib.Topology.Spectral.Prespectral

/-!
# Quasi-compact images of locally finite families

Stacks 02R2 says that a quasi-compact morphism of schemes carries a locally finite family of
closed subsets to a locally finite family, after taking closures of the images. The scheme
hypotheses play no role: what the argument uses is that the map is spectral — the preimage of a
quasi-compact open is quasi-compact — and that the target has a basis of quasi-compact opens.
Both hold for a quasi-compact morphism of schemes, whose underlying spaces are spectral.

Around a point of the target choose a quasi-compact open neighbourhood `V`. The closure of the
image of `Z i` meets `V` exactly when the image of `Z i` does, because `V` is open; and that
happens exactly when `Z i` meets the preimage of `V`, which is quasi-compact. Local finiteness
of `Z` then bounds the number of such `i`.

## Main results

* `Stacks.Chow.locallyFinite_closure_image_of_isSpectralMap` — Stacks 02R2.

## References

* [Stacks Project, Tag 02R2](https://stacks.math.columbia.edu/tag/02R2)
-/

public section

open TopologicalSpace

universe u v w

namespace Stacks.Chow

/-- **Stacks 02R2.** Under a spectral map to a prespectral space, the closures of the images of
a locally finite family of subsets form a locally finite family. -/
@[stacks 02R2]
theorem locallyFinite_closure_image_of_isSpectralMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [PrespectralSpace Y] (f : X → Y)
    (hf : IsSpectralMap f) {I : Type w} (Z : I → Set X) (hZ : LocallyFinite Z) :
    LocallyFinite fun i ↦ closure (f '' Z i) := fun y ↦ by
  obtain ⟨V, ⟨ho, hc⟩, hv, -⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  refine ⟨V, ho.mem_nhds hv, ?_⟩
  simpa only [closure_inter_open_nonempty_iff ho, Set.image_inter_nonempty_iff] using
    hZ.finite_nonempty_inter_compact (hf.isCompact_preimage_of_isOpen ho hc)

end Stacks.Chow

end
