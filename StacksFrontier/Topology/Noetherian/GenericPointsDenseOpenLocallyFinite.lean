module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Sober
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic points lie in every dense open subset, for locally finite irreducible components

Let `T` be a topological space whose irreducible components form a locally finite collection.
Then a generic point of an irreducible component lies in every dense open subset of `T`. Were a
generic point `x` outside a dense open set `D`, then `D`, meeting no irreducible component in a
generic point of it, would be covered by the components other than `closure {x}`; their union is
closed, because a locally finite union of closed sets is closed, so it would contain the closure
of `D`, which is everything; and then `closure {x}` would sit inside a component other than
itself.

This is the Noetherian statement
`TopologicalSpace.NoetherianSpace.mem_of_mem_genericPoints_of_dense` with the finiteness of the
collection of irreducible components relaxed to local finiteness.

## Main results

* `TopologicalSpace.mem_of_mem_genericPoints_of_dense_of_locallyFinite`.
-/

@[expose] public section

open TopologicalSpace

namespace TopologicalSpace

/-- **A dense open subset of a space with locally finite irreducible components contains every
generic point.** This is `TopologicalSpace.NoetherianSpace.mem_of_mem_genericPoints_of_dense`
with the finiteness of the collection of irreducible components relaxed to local finiteness.

Suppose a generic point `x` were outside the dense open set `D`. Every point of `D` lies on some
irreducible component, and not on `closure {x}`, which is disjoint from `D`; so `D` is contained
in the union of the components other than `closure {x}`. That union is closed, local finiteness
of the collection making a union of closed sets closed, so it contains `closure D`, which is the
whole space. Then `x` itself lies on a component other than `closure {x}`, whence `closure {x}`
is contained in it, and maximality of `closure {x}` makes the two equal. -/
@[ega "IV 15.7.4" "special case", sga "3 VIB 5.4.1" "partial"]
theorem mem_of_mem_genericPoints_of_dense_of_locallyFinite {T : Type*} [TopologicalSpace T]
    (hlf : LocallyFinite fun C : irreducibleComponents T ↦ (C : Set T))
    {D : Set T} (hD : IsOpen D) (hd : Dense D) {x : T} (hx : x ∈ genericPoints T) : x ∈ D := by
  by_contra hxD
  have hxc : closure {x} ∈ irreducibleComponents T := hx
  -- The components other than `closure {x}`.
  have hclosed : IsClosed (⋃ C : {C : irreducibleComponents T // (C : Set T) ≠ closure {x}},
      (C.1 : Set T)) :=
    (hlf.comp_injective Subtype.val_injective).isClosed_iUnion fun C ↦
      isClosed_of_mem_irreducibleComponents _ C.1.2
  -- `closure {x}` misses the dense open set, so these components cover it.
  have hxcompl : closure {x} ⊆ Dᶜ :=
    hD.isClosed_compl.closure_subset_iff.2 (Set.singleton_subset_iff.2 hxD)
  have hDsub : D ⊆ ⋃ C : {C : irreducibleComponents T // (C : Set T) ≠ closure {x}},
      (C.1 : Set T) := by
    intro y hy
    obtain ⟨W, hW, hyW⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {y} isIrreducible_singleton
    exact Set.mem_iUnion.2 ⟨⟨⟨W, hW⟩, fun h ↦ hxcompl (h ▸ hyW rfl) hy⟩, hyW rfl⟩
  -- Hence they cover the whole space, and in particular `x`.
  obtain ⟨⟨C, hne⟩, hxC⟩ := Set.mem_iUnion.1
    ((hd.closure_eq ▸ closure_minimal hDsub hclosed : Set.univ ⊆ _) (Set.mem_univ x))
  have hle : closure {x} ⊆ (C : Set T) :=
    closure_minimal (Set.singleton_subset_iff.2 hxC)
      (isClosed_of_mem_irreducibleComponents _ C.2)
  exact hne (Set.Subset.antisymm (hxc.2 C.2.1 hle) hle)

end TopologicalSpace
