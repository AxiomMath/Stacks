module

public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Irreducible

/-!
# Subfamilies of the irreducible components, and their unions

Two elementary facts used when a space is split along a subfamily of its irreducible
components: a subfamily of a locally finite family of components is again locally finite, and
the supremum, in the lattice of closed sets, of a family of closed sets with closed union is
that union.

## Main results

* `TopologicalSpace.locallyFinite_component_subfamily`: the irreducible components satisfying a
  given predicate form a locally finite family as soon as all of them do.
* `TopologicalSpace.coe_iSup_closure_eq_iUnion_of_isClosed`: the supremum of a family of closed
  sets, in the lattice of closed sets, is their union when that union is closed.

## Implementation notes

The subfamily is indexed by the subtype of sets which are irreducible components and satisfy
the predicate, which is how a split of a scheme along the components contained in a closed
subscheme is presented; local finiteness is transported along the injection of that subtype
into the type of all components. In the second result the family is indexed by an arbitrary
sort, so it applies to such a subtype directly.

## References

* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
-/

@[expose] public section

namespace TopologicalSpace

/-- **The supremum in the lattice of closed sets of a family of closed sets whose union is
closed is that union.** -/
theorem coe_iSup_closure_eq_iUnion_of_isClosed
    {X : Type*} [TopologicalSpace X] {ι : Sort*} (C : ι → Set X)
    (hC : ∀ i, IsClosed (C i)) (hUnion : IsClosed (⋃ i, C i)) :
    (↑(⨆ i, Closeds.closure (C i)) : Set X) = ⋃ i, C i := by
  have hSet : (⋃₀ ((↑) '' Set.range fun i => Closeds.closure (C i))) = ⋃ i, C i := by
    ext x
    simp [Closeds.coe_closure]
  rw [iSup, Closeds.coe_sSup, hSet, hUnion.closure_eq]

/-- **A subfamily of a locally finite family of irreducible components is locally finite.** -/
theorem locallyFinite_component_subfamily
    {X : Type*} [TopologicalSpace X]
    (hcomponents : LocallyFinite (fun C : irreducibleComponents X => (C : Set X)))
    (P : Set X → Prop) :
    LocallyFinite (fun C : {C : Set X // C ∈ irreducibleComponents X ∧ P C} => C.1) :=
  hcomponents.comp_injective
    (g := fun C : {C : Set X // C ∈ irreducibleComponents X ∧ P C} =>
      (⟨C.1, C.2.1⟩ : irreducibleComponents X))
    fun _ _ h => Subtype.ext (congrArg (fun Z : irreducibleComponents X => (Z : Set X)) h)

end TopologicalSpace

end
