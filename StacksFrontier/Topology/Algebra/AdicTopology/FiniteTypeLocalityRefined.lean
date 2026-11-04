module

public import Mathlib.RingTheory.RingHom.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeComposition
public import StacksFrontier.RingTheory.RingHom.QuotientBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverFiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeLocality
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeProduct
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Tautness together with topological finite type is a local property: the refined forms

We show that the property of a continuous ring map of being taut and topologically of finite type
is local, in the sense of `TopologicalRing.PropertyIsLocal'`, on the class of countably indexed
weakly admissible topological rings.

These are the strengthened and newly added declarations of the 2026-10 chapter-87 round that
belong with `StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeLocality`. A declaration of that
module whose statement the round strengthened keeps its original statement there; its
strengthened form lives here under a primed name.

## Main results

* `TopologicalRing.tautAndFiniteType_propertyIsLocal'`: tautness together with topological finite
  type is a local property of morphisms of countably indexed weakly admissible topological rings.
-/

@[expose] public section

namespace TopologicalRing

open TopologicalRing CompletionOver Filter

universe u

section

variable {B : Type u} {A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A]

end

section

variable {A : Type u} {A' : Type u}

end

section

variable {A : Type u} {B : Type u} {A' : Type u}

end

section

variable {A B A' B' : Type u}
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [CommRing A'] [CommRing B']

end

section

/-- Tautness together with topological finite type is a local property of morphisms of
countably indexed weakly admissible topological rings. -/
public theorem tautAndFiniteType_propertyIsLocal' :
    TopologicalRing.PropertyIsLocal'.{u}
      (fun φ => RingHom.IsTaut φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ)
      TopologicalRing.IsCountablyWeaklyAdmissible where
  isomorphismInvariant := TopologicalRing.topologicallyFiniteType_isomorphismInvariant
  localizationPreserves := tautAndFiniteType_localizationPreserves
  faithfullyFlatDescent := tautAndFiniteType_faithfullyFlatDescent
  finiteProduct := tautAndFiniteType_finiteProductPreserves

end

end TopologicalRing

end
