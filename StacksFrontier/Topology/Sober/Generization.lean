module

public import Mathlib.Topology.Sober

/-!
# Generic points of irreducible components and generization

A point of a Kolmogorov space whose singleton has an irreducible component as closure admits
no generization but itself: a generization has a larger closure, which is irreducible, so
maximality makes the two closures equal. The converse needs the space to be quasi-sober — the
component containing the point has to have a generic point before the hypothesis can be
applied to it — and it genuinely fails without that: an infinite set with the cofinite
topology is Kolmogorov, every point of it admits no generization but itself, and yet it is
irreducible, so its unique irreducible component is the whole space and no singleton closure
is a component (`not_quasiSober_cofiniteTopology`,
`irreducibleComponents_cofiniteTopology`).

## Main results

* `TopologicalSpace.forall_specializes_eq_of_mem_genericPoints`: on a Kolmogorov space a
  generic point of an irreducible component has no proper generization.
* `TopologicalSpace.mem_genericPoints_of_forall_specializes_eq`: on a sober space the
  converse.
* `TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq`: the two together.
* `TopologicalSpace.exists_isGenericPoint_irreducibleComponents_iff`: the same criterion for a
  generic point of an irreducible component of a closed subset, read in the ambient space.
-/

@[expose] public section

namespace TopologicalSpace

variable {α : Type*} [TopologicalSpace α]

/-- On a Kolmogorov space a generic point of an irreducible component has no generization but
itself: the closure of a generization contains the component, is irreducible, and so equals
it by maximality. -/
theorem forall_specializes_eq_of_mem_genericPoints [T0Space α] {x : α}
    (hx : x ∈ genericPoints α) (y : α) (hyx : y ⤳ x) : y = x :=
  have hback : closure ({y} : Set α) ⊆ closure ({x} : Set α) :=
    hx.2 isIrreducible_singleton.closure (specializes_iff_closure_subset.mp hyx)
  (hyx.antisymm (specializes_iff_closure_subset.mpr hback)).eq

/-- On a sober space a point with no generization but itself is a generic point of an
irreducible component: the component containing it has a generic point, which is one of its
generizations and therefore the point itself. -/
theorem mem_genericPoints_of_forall_specializes_eq [T0Space α] [QuasiSober α] {x : α}
    (h : ∀ y : α, y ⤳ x → y = x) : x ∈ genericPoints α := by
  set Z : irreducibleComponents α :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hZ : (genericPoints.ofComponent Z : α) = x :=
    h _ ((genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent)
  exact hZ ▸ (genericPoints.ofComponent Z).2

/-- On a sober space a point is a generic point of an irreducible component exactly when it
has no generization but itself. -/
theorem mem_genericPoints_iff_forall_specializes_eq [T0Space α] [QuasiSober α] (x : α) :
    x ∈ genericPoints α ↔ ∀ y : α, y ⤳ x → y = x :=
  ⟨forall_specializes_eq_of_mem_genericPoints, mem_genericPoints_of_forall_specializes_eq⟩

/-- On a sober space a point is a generic point of an irreducible component of a closed subset
`T` exactly when it lies in `T` and no other point of `T` generizes it.  The components are
taken in the subspace `T`, which is sober because it is closed, and read in the ambient space
through the inclusion, a closed embedding. -/
theorem exists_isGenericPoint_irreducibleComponents_iff [T0Space α] [QuasiSober α] {T : Set α}
    (hT : IsClosed T) (x : α) :
    (∃ Z : irreducibleComponents T, IsGenericPoint x (Subtype.val '' Z.1)) ↔
      x ∈ T ∧ ∀ y ∈ T, y ⤳ x → y = x := by
  have : QuasiSober T := hT.isClosedEmbedding_subtypeVal.quasiSober
  constructor
  · rintro ⟨Z, hZ⟩
    obtain ⟨⟨x', hx'⟩, -, rfl⟩ := hZ.mem
    have hmem : (⟨x', hx'⟩ : T) ∈ genericPoints T := by
      have : closure ({⟨x', hx'⟩} : Set T) = Z.1 :=
        Set.image_injective.mpr Subtype.val_injective <| by
          rw [← hT.isClosedEmbedding_subtypeVal.closure_image_eq, Set.image_singleton]
          exact hZ
      rw [genericPoints, Set.mem_ofPred_eq, this]
      exact Z.2
    exact ⟨hx', fun y hy hyx => congrArg Subtype.val <|
      forall_specializes_eq_of_mem_genericPoints hmem ⟨y, hy⟩
        ((subtype_specializes_iff _ _).mpr hyx)⟩
  · rintro ⟨hx, hmin⟩
    have hgen : (⟨x, hx⟩ : T) ∈ genericPoints T :=
      mem_genericPoints_of_forall_specializes_eq fun y hy =>
        Subtype.ext (hmin y.1 y.2 ((subtype_specializes_iff _ _).mp hy))
    refine ⟨genericPoints.component ⟨_, hgen⟩, ?_⟩
    rw [isGenericPoint_def, ← (genericPoints.isGenericPoint ⟨_, hgen⟩).def,
      ← hT.isClosedEmbedding_subtypeVal.closure_image_eq, Set.image_singleton]

end TopologicalSpace

end
