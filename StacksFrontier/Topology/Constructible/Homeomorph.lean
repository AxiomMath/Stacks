module

public import Mathlib.Topology.Constructible

/-!
# Constructibility is a homeomorphism invariant

A homeomorphism is an open embedding with retrocompact — indeed full — range, so it reflects
and preserves both constructibility and local constructibility.

## Main results

* `Homeomorph.isConstructible_preimage_iff`
* `Homeomorph.isLocallyConstructible_preimage_iff`
-/

@[expose] public section

open Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A subset of the target of a homeomorphism is constructible exactly when its preimage
is. -/
theorem Homeomorph.isConstructible_preimage_iff (e : X ≃ₜ Y) (s : Set Y) :
    IsConstructible (e ⁻¹' s) ↔ IsConstructible s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.preimage_of_isOpenEmbedding e.isOpenEmbedding⟩
  simpa [Set.preimage_preimage] using h.preimage_of_isOpenEmbedding e.symm.isOpenEmbedding

/-- A subset of the target of a homeomorphism is locally constructible exactly when its
preimage is. -/
theorem Homeomorph.isLocallyConstructible_preimage_iff (e : X ≃ₜ Y) (s : Set Y) :
    IsLocallyConstructible (e ⁻¹' s) ↔ IsLocallyConstructible s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.preimage_of_isOpenEmbedding e.isOpenEmbedding⟩
  simpa [Set.preimage_preimage] using h.preimage_of_isOpenEmbedding e.symm.isOpenEmbedding

end
