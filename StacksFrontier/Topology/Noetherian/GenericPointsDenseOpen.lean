module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Generic points of a Noetherian space lie in every dense open subset

In a Noetherian space a generic point of an irreducible component lies in every dense open
subset.

## Main results

* `TopologicalSpace.NoetherianSpace.mem_of_mem_genericPoints_of_dense`: a generic point of an
  irreducible component of a Noetherian space belongs to every dense open subset.
-/

@[expose] public section

open TopologicalSpace

namespace TopologicalSpace

/-- In a Noetherian space a generic point of an irreducible component lies in every dense open
subset. -/
theorem NoetherianSpace.mem_of_mem_genericPoints_of_dense {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] {D : Set T} (hD : IsOpen D) (hd : Dense D) {x : T}
    (hx : x ∈ genericPoints T) : x ∈ D := by
  obtain ⟨V, hV, hVne, hVZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure ({x} : Set T)) hx
  obtain ⟨z, hzV, hzD⟩ := hd.inter_open_nonempty V hV hVne
  exact (specializes_iff_mem_closure.mpr (hVZ hzV)).mem_open hD hzD

end TopologicalSpace
