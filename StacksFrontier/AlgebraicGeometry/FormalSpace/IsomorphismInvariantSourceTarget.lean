module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartLocalizationDiagram
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Invariance under isomorphism of source and of target, from that of Situation 0CBA

Situation 0CBA opens with "let `P` be a property of morphisms ..., invariant under isomorphism
of source and target in this category". On a class `C` of rings this clause is
`TopologicalRing.IsomorphismInvariant P C`, the `isomorphismInvariant` field of
`TopologicalRing.PropertyIsLocal'`. The chart arguments of this chapter consume it in two
one-sided forms, `AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderSourceIso` and
`AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderTargetIsoOn`; this file derives both
from it, taking the identity on the other end.

## Main results

* `AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderSourceIso_of_isomorphismInvariant`
* `AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderTargetIsoOn_of_isomorphismInvariant`

## References

* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public section

namespace AlgebraicGeometry.FormalSpace

universe u

variable {C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop}
  {P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop}

/-- A property of arrows of a class `C` invariant under isomorphism of source and target in the
category of rings of `C` (the opening clause of Situation 0CBA) is invariant under isomorphism
of targets: take the identity of the source. -/
theorem propertyIsInvariantUnderTargetIsoOn_of_isomorphismInvariant
    (hP : TopologicalRing.IsomorphismInvariant P C) :
    PropertyIsInvariantUnderTargetIsoOn.{u} C P := by
  intro A R R' _ _ _ _ _ _ _ _ _ _ _ _ hA hR hR' ψ e hψ he hes hψP
  exact (hP (RingEquiv.refl A) e continuous_id continuous_id he hes ψ hψ hA hR hA hR').mp hψP

/-- A property of arrows of a class `C` invariant under isomorphism of source and target in the
category of rings of `C` (the opening clause of Situation 0CBA) is invariant under isomorphism
of sources: take the identity of the target. -/
theorem propertyIsInvariantUnderSourceIso_of_isomorphismInvariant
    (hP : TopologicalRing.IsomorphismInvariant P C) :
    PropertyIsInvariantUnderSourceIso.{u} C P := by
  intro A A' R _ _ _ _ _ _ _ _ _ _ _ _ hA hA' hR ψ e hψ he hes hψP
  exact (hP e.symm (RingEquiv.refl R) hes he continuous_id continuous_id ψ hψ hA hR hA' hR).mp
    hψP

end AlgebraicGeometry.FormalSpace

end
