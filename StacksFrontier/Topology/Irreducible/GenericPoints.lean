module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import StacksFrontier.Topology.Sober.Generization

/-!
# Generic points of irreducible components under a homeomorphism

A homeomorphism matches up the irreducible components of two spaces, hence their generic
points.

## Main results

* `Homeomorph.mem_genericPoints`: a homeomorphism carries a generic point of an irreducible
  component to a generic point of an irreducible component.
* `Homeomorph.mem_genericPoints_iff`: the two conditions are equivalent, so the generic points
  of one space are exactly the preimages of those of the other.
* `Homeomorph.bijOn_genericPoints`: the homeomorphism therefore restricts to a bijection of the
  two sets of generic points.
-/

@[expose] public section

open TopologicalSpace

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism carries the generic point of an irreducible component to the generic point
of an irreducible component. -/
theorem mem_genericPoints (e : X ≃ₜ Y) {x : X} (hx : x ∈ genericPoints X) :
    e x ∈ genericPoints Y := by
  change closure ({e x} : Set Y) ∈ irreducibleComponents Y
  rw [← Set.image_singleton, ← e.image_closure]
  exact image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous e.isOpenMap
    (fun _ ↦ (Set.subsingleton_singleton.preimage e.injective).isPreirreducible) e.surjective hx

/-- A homeomorphism identifies the generic points of the irreducible components of its source
with those of its target. -/
theorem mem_genericPoints_iff (e : X ≃ₜ Y) (x : X) :
    e x ∈ genericPoints Y ↔ x ∈ genericPoints X :=
  ⟨fun hx ↦ by simpa using e.symm.mem_genericPoints hx, e.mem_genericPoints⟩

/-- A homeomorphism restricts to a bijection from the generic points of its source onto those of
its target. -/
theorem bijOn_genericPoints (e : X ≃ₜ Y) :
    Set.BijOn e (genericPoints X) (genericPoints Y) :=
  ⟨fun _ hx ↦ e.mem_genericPoints hx, e.injective.injOn,
    fun y hy ↦ ⟨e.symm y, e.symm.mem_genericPoints hy, e.apply_symm_apply y⟩⟩

end Homeomorph

end
