module

public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition

/-!
# Admissible rings and weak ideals of definition

Comparison of ideals of definition with weak ideals of definition in a topological ring. These
results sit next to `StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition` but are kept in
a module of their own, so that that module stays as it is on the base.

## Main results

* `TopologicalRing.isWeaklyAdmissible_of_isAdmissible`: An admissible topological ring is weakly
  admissible.
* `TopologicalRing.exists_isIdealOfDefinition_le_of_isWeakIdealOfDefinition`: In a pre-admissible
  topological ring, every weak ideal of definition contains an ideal of definition.
-/

@[expose] public section

namespace TopologicalRing

open Filter

open scoped Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- An admissible topological ring is weakly admissible. Both notions ask for completeness and
separatedness; the only difference is between ideals of definition and weak ideals of
definition, and an ideal of definition is a weak one. -/
public theorem isWeaklyAdmissible_of_isAdmissible [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsAdmissible R) : IsWeaklyAdmissible R :=
  ⟨isWeaklyPreAdmissible_of_isPreAdmissible hR.1, hR.2.2, hR.2.1⟩

/-- **One ideal of definition below a weak ideal of definition.** In a pre-admissible
topological ring the ideals of definition are cofinal below the weak ideals of definition: a
weak ideal of definition is open, so its intersection with any ideal of definition is again an
ideal of definition, and it is contained in it.

This is what makes the index of the colimit of Stacks 0AIE — the ideals of definition of an
admissible ring — cofinal in the index of the formal spectrum of Stacks 0AIF, which is the weak
ideals of definition. -/
public theorem exists_isIdealOfDefinition_le_of_isWeakIdealOfDefinition
    (hR : IsPreAdmissible R) {J : Ideal R} (hJ : IsWeakIdealOfDefinition J) :
    ∃ I : Ideal R, IsIdealOfDefinition I ∧ I ≤ J := by
  obtain ⟨I₀, hI₀⟩ := hR
  exact ⟨I₀ ⊓ J, isIdealOfDefinition_of_le_of_isOpen hI₀
    (by simpa using hI₀.1.inter hJ.1) inf_le_left, inf_le_right⟩

end TopologicalRing

end
