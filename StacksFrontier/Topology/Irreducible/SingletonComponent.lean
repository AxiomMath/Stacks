module

public import StacksFrontier.Topology.Irreducible.DisjointComponentLocus

/-!
# A one-point irreducible component is open

An irreducible component which is a single point lies on no other irreducible component, by
maximality; so if there are only finitely many components it is the complement of the closed
union of the others, and therefore open as well as closed.

## Main results

* `Stacks.Topology.Irreducible.isOpen_singleton_of_mem_irreducibleComponents`: a one-point
  irreducible component of a space with finitely many irreducible components is open.

## Implementation notes

The finiteness is taken as the hypothesis `(irreducibleComponents X).Finite` rather than
`TopologicalSpace.NoetherianSpace X`, which is what produces it in both of the current uses but
is more than the statement needs. The point is the generic point of its own component, being a
closed point, so
`Stacks.Topology.Irreducible.genericPoint_mem_disjointLocus` places it in the disjointness locus
of the components; its component piece is then an open subset of the component, which is the
point itself.
-/

@[expose] public section

open Set TopologicalSpace

namespace Stacks.Topology.Irreducible

variable {X : Type*} [TopologicalSpace X]

/-- **A one-point irreducible component is open**, provided the space has only finitely many
irreducible components: the point lies on no other component, so its component piece in the
disjointness locus of the components is the point itself, and component pieces of a finite family
of closed sets are open. -/
public theorem isOpen_singleton_of_mem_irreducibleComponents
    (hfin : (irreducibleComponents X).Finite) (x : X)
    (hx : ({x} : Set X) ∈ irreducibleComponents X) :
    IsOpen ({x} : Set X) := by
  have : Finite {W : Set X // W ∈ irreducibleComponents X} := hfin.to_subtype
  have hgp : IsGenericPoint x ({x} : Set X) :=
    (isClosed_of_mem_irreducibleComponents _ hx).closure_eq
  have hmem : x ∈ componentPart (componentsOfEquiv (.refl _)) ⟨{x}, hx⟩ :=
    ⟨fun j k hjk hjk' ↦ hjk (Subtype.ext ((eq_of_isGenericPoint_mem hx j.2 hgp hjk'.1).symm.trans
      (eq_of_isGenericPoint_mem hx k.2 hgp hjk'.2))), rfl⟩
  have heq : componentPart (componentsOfEquiv (.refl _)) ⟨{x}, hx⟩ = {x} :=
    (componentPart_subset _ _).antisymm (singleton_subset_iff.2 hmem)
  exact heq ▸ isOpen_componentPart_componentsOfEquiv _ _

end Stacks.Topology.Irreducible

end
