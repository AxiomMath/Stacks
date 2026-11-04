module

public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The topological nilradical of a Noetherian adic ring

Let `A` be a Noetherian commutative ring whose topology is the adic topology of an ideal.
Its ideal `topologicalNilradical A` of topologically nilpotent elements then defines the same
topology: it is the radical of any ideal of definition, and a Noetherian radical ideal has a
power inside the ideal it is the radical of.

## Main results

* `TopologicalRing.isIdealOfDefinition_of_isAdic`: an ideal defining the topology through its
  powers is an ideal of definition.
* `TopologicalRing.isIdealOfDefinition_topologicalNilradical` and
  `TopologicalRing.isAdic_topologicalNilradical`: for a Noetherian adic ring the topological
  nilradical is an ideal of definition, and the topology is its adic topology.

## References

* [Stacks Project, Tag 07E8](https://stacks.math.columbia.edu/tag/07E8)
* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
-/

@[expose] public section

open Filter
open scoped Topology

namespace TopologicalRing

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- An ideal whose powers form a basis of the neighbourhoods of zero is an ideal of
definition. -/
public theorem isIdealOfDefinition_of_isAdic [IsTopologicalRing A] {I : Ideal A}
    (hI : _root_.IsAdic I) : IsIdealOfDefinition I :=
  ⟨by simpa using (isAdic_iff.mp hI).1 1, (isAdic_iff.mp hI).2⟩

/-- The ideal of topologically nilpotent elements of a Noetherian linearly topologized ring with
a weak ideal of definition is an ideal of definition: it is a finitely generated weak ideal of
definition. -/
@[ega "0 7.1.3" "(ii), T is open", ega "0 7.1.6" "special case"]
public theorem isIdealOfDefinition_topologicalNilradical [IsTopologicalRing A]
    [IsLinearTopology A A] [IsNoetherianRing A] (hA : IsWeaklyPreAdmissible A) :
    IsIdealOfDefinition (topologicalNilradical A) :=
  isIdealOfDefinition_of_isWeakIdealOfDefinition
    (isWeakIdealOfDefinition_topologicalNilradical hA) (Ideal.fg_of_isNoetherianRing _)

/-- The topology of a Noetherian adic ring is the adic topology of its ideal of topologically
nilpotent elements: the powers of that ideal are open because they contain the corresponding
powers of the given ideal, and they are cofinal among the neighbourhoods of zero because the
ideal is a finitely generated weak ideal of definition. -/
@[ega "0 7.1.3" "(ii), openness of T", ega "0 7.1.6" "special case"]
public theorem isAdic_topologicalNilradical [IsTopologicalRing A] [IsLinearTopology A A]
    [IsNoetherianRing A] {I : Ideal A} (hI : _root_.IsAdic I) :
    _root_.IsAdic (topologicalNilradical A) := by
  have hdef : IsIdealOfDefinition I := isIdealOfDefinition_of_isAdic hI
  have hnilpotent (x : A) (hx : x ∈ I) : IsTopologicallyNilpotent x :=
    CompletionOver.isTopologicallyNilpotent_of_mem_isIdealOfDefinition hdef hx
  have hle : I ≤ topologicalNilradical A := fun x hx ↦
    IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hnilpotent x hx)
  have hrad := isIdealOfDefinition_topologicalNilradical (A := A) ⟨I, hdef.1, hnilpotent⟩
  refine isAdic_iff.mpr ⟨fun n ↦ Ideal.isOpen_of_isOpen_subideal ?_ ((isAdic_iff.mp hI).1 n),
    hrad.2⟩
  gcongr

end TopologicalRing

end
