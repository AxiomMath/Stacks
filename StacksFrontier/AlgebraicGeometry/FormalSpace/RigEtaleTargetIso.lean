module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChange
public import StacksFrontier.RingTheory.Rig.RigEtaleArrowIso

/-!
# Rig-étaleness of arrows is invariant under isomorphism of targets

The predicate `AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderTargetIso`, which the
base change transfer of Stacks 0GBG consumes, holds for rig-étaleness of arrows of
`WAdm^Noeth` (Stacks 0GCV): composing a rig-étale arrow with a homeomorphic ring isomorphism of
Noetherian adic targets gives a rig-étale arrow, since such an isomorphism is itself rig-étale
and rig-étaleness is stable under composition (Stacks 0GCX).

## Main results

* `AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderTargetIso_isRigEtaleArrow`.
-/

@[expose] public section

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Rig-étaleness of arrows of `WAdm^Noeth` is invariant under isomorphism of targets.** -/
theorem propertyIsInvariantUnderTargetIso_isRigEtaleArrow :
    PropertyIsInvariantUnderTargetIso.{u}
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ) := by
  intro A R R' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hR _ ψ e he he' hψ
  exact Rig.isRigEtaleArrow_of_isRigEtaleArrow_of_ringEquiv hA hR ψ hψ (RingEquiv.refl A)
    continuous_id continuous_id e he he' _ rfl

end AlgebraicGeometry.FormalSpace

end
