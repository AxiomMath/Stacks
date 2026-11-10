module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.Topology.Algebra.Module
public import StacksFrontier.Topology.Algebra.Ring

/-!
# Ideals of definition, admissible and adic topological rings: the refined forms

This file proves that in a pre-adic topological ring every ideal of definition defines the
topology adically.

## Main results

* `TopologicalRing.isAdic_of_isIdealOfDefinition_of_isPreAdic`: in a pre-adic topological ring,
  the topology is the adic topology of any ideal of definition.
-/

@[expose] public section

/-!
# Ideals of definition, admissible and adic topological rings

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07E8.

## Tag 07E8 — Topological rings and modules

This file records topological modules and their continuous homomorphisms, linear topologies,
ideals of definition, and the pre-admissible, admissible, pre-adic, and adic conditions on a
topological ring.

### Main definitions

* `TopModuleCat`: Mathlib's category of topological modules, whose objects are the modules over a
  topological ring whose addition and scalar multiplication are continuous.
* `ContinuousLinearMap` and `StacksTopologicalRingHom`: continuous module and ring homomorphisms.
* `IsIdealOfDefinition`: an open ideal whose powers are cofinal among the neighborhoods
  of zero.
* `IsPreAdmissible` and `IsAdmissible`: existence of an ideal of definition,
  without and with completeness.
* `IsPreAdic` and `IsAdic`: an adic topology defined by an ideal of definition,
  without and with completeness.

### Main results

* `preAdic_and_adic_iff_admissible_and_open_powers`: the source's equivalent
  description in terms of an ideal of definition all of whose positive powers are open.

### Implementation notes

Mathlib's `IsTopologicalRing`, `IsLinearTopology`, and root-level `IsAdic` express respectively
topological rings, linear topologies, and equality with the topology defined by the powers of a
fixed ideal. Completeness is expressed using the canonical right uniformity of the additive
topological group, together with the Hausdorff condition required by the source. For a commutative
ring, `IsLinearTopology R R` gives the source's basis of ideals.

### References

* [EGA I, Chapter 0, Sections 7.1 and 7.2]
* [Stacks Project, Tag 07E8](https://stacks.math.columbia.edu/tag/07E8)

-/

namespace TopologicalRing

/-! ### Stacks Tag 07E8 -/

section

section

@[expose] public section

open Filter
open scoped Topology

universe u v w

end

end

section

open Filter
open scoped Topology

universe u

/-- In a pre-adic topological ring, every ideal of definition defines the topology adically. -/
@[ega "0 7.2.3" "special case"]
public theorem isAdic_of_isIdealOfDefinition_of_isPreAdic {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (h : IsPreAdic R) {I : Ideal R}
    (hI : IsIdealOfDefinition I) : _root_.IsAdic I := by
  obtain ⟨K, -, hKadic⟩ := h
  obtain ⟨m, hm⟩ := (isAdic_iff.mp hKadic).2 (I : Set R) (hI.1.mem_nhds I.zero_mem)
  refine isAdic_iff.mpr ⟨fun n ↦ ?_, hI.2⟩
  refine Ideal.isOpen_of_isOpen_subideal (U := K ^ (m * n)) ?_
    ((isAdic_iff.mp hKadic).1 (m * n))
  rw [pow_mul]
  exact pow_le_pow_left' (show K ^ m ≤ I from fun _ hx ↦ hm hx) n

end

end

end TopologicalRing

end
