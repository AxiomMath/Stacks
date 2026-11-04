module

public import StacksFrontier.Topology.Dimension.Codimension

/-!
# Codimension under a homeomorphism

A homeomorphism `h : X ≃ₜ Y` induces an order isomorphism between the posets of irreducible
closed subsets of `X` and of `Y`, sending `T` to `h(T)`. The codimension of Stacks 02I3 is the
coheight in that poset, so it is preserved.

## Main definitions

* `TopologicalSpace.IrreducibleCloseds.orderIsoOfHomeomorph`: the order isomorphism of
  irreducible closed subsets induced by a homeomorphism.

## Main results

* `codimension_orderIsoOfHomeomorph`: a homeomorphism preserves codimension.

## References

* [Stacks Project, Tag 02I3](https://stacks.math.columbia.edu/tag/02I3)
-/

@[expose] public section

open TopologicalSpace

namespace TopologicalSpace.IrreducibleCloseds

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The image of an irreducible closed subset `T` under a homeomorphism `h` has underlying set
`h '' T`: that image is closed, so that no closure is taken. -/
theorem coe_map_homeomorph (h : X ≃ₜ Y) (T : IrreducibleCloseds X) :
    (map h h.continuous T : Set Y) = h '' T := by
  rw [coe_map, (h.isClosedMap _ T.isClosed).closure_eq]

/-- **The irreducible closed subsets under a homeomorphism.** A homeomorphism `h : X ≃ₜ Y`
induces an order isomorphism `T ↦ h(T)` between the irreducible closed subsets of `X` and those
of `Y`. -/
def orderIsoOfHomeomorph (h : X ≃ₜ Y) : IrreducibleCloseds X ≃o IrreducibleCloseds Y where
  toFun := map h h.continuous
  invFun := map h.symm h.symm.continuous
  left_inv T := by
    refine IrreducibleCloseds.ext ?_
    rw [coe_map_homeomorph, coe_map_homeomorph, ← Set.image_comp]
    simp
  right_inv T := by
    refine IrreducibleCloseds.ext ?_
    rw [coe_map_homeomorph, coe_map_homeomorph, ← Set.image_comp]
    simp
  map_rel_iff' {T T'} := by
    change (map h h.continuous T : Set Y) ⊆ map h h.continuous T' ↔ (T : Set X) ⊆ T'
    rw [coe_map_homeomorph, coe_map_homeomorph]
    exact Set.image_subset_image_iff h.injective

/-- The underlying set of the image of `T` under `orderIsoOfHomeomorph h` is `h '' T`. -/
@[simp]
theorem coe_orderIsoOfHomeomorph (h : X ≃ₜ Y) (T : IrreducibleCloseds X) :
    (orderIsoOfHomeomorph h T : Set Y) = h '' T :=
  coe_map_homeomorph h T

end TopologicalSpace.IrreducibleCloseds

/-- **A homeomorphism preserves codimension.** -/
theorem codimension_orderIsoOfHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (T : IrreducibleCloseds X) :
    codimension (IrreducibleCloseds.orderIsoOfHomeomorph h T) = codimension T :=
  Order.coheight_orderIso _ T

end
