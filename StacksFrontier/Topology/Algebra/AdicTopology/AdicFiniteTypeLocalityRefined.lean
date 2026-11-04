module

public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeComposition
public import StacksFrontier.RingTheory.Rig.RigSmoothStabilityRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeLocality
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMapRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeLocalityRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined
import all StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeLocality

/-!
# Locality of adic morphisms of topologically finite type: the refined forms

The strengthened forms of declarations of
`StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeLocality`. A declaration of that module
whose statement was strengthened keeps its original statement there; its strengthened form lives
here under a primed name.

Adic ring maps that are topologically of finite type form a local property of morphisms of
weakly admissible adic-star rings, and this property is stable under composition.

## Main results

* `TopologicalRing.adicAndFiniteType_propertyIsLocal'`: being adic and topologically of finite
  type is a local property of morphisms of weakly admissible adic-star rings.
* `TopologicalRing.adicAndFiniteType_propertyIsStableUnderComposition'`: this local property is
  stable under composition.
-/

@[expose] public section

namespace TopologicalRing

universe u

open Filter
open scoped Topology

/-- Adic morphisms of topologically finite type form a local property on weakly admissible
adic-star rings. -/
public theorem adicAndFiniteType_propertyIsLocal' :
    TopologicalRing.AdicStarPropertyIsLocal'.{u}
      (fun φ => RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) :=
  adicTopologicallyFiniteType_isLocal'

/-- Adic morphisms of topologically finite type form a local property of morphisms of weakly
admissible adic-star rings which is stable under composition. -/
public theorem adicAndFiniteType_propertyIsStableUnderComposition' :
    TopologicalRing.AdicStarPropertyIsStableUnderComposition'.{u}
      (fun φ => RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) :=
  adicTopologicallyFiniteType_isStableUnderComposition'

end TopologicalRing

end
