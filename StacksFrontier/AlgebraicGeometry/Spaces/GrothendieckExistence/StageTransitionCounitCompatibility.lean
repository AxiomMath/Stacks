module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.PerfectSectionsTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.SingleCounitCompatibleOfAffine

/-!
# The single-degree counit compatibility along the transitions of Situation 0CX4

For the system `(Fₙ)` of Situation [Stacks, Tag 0CX4], the map `Fₙ₊₁ ⟶ tₙ,* Fₙ` adjoint to
`φₙ : tₙ^* Fₙ₊₁ ≅ Fₙ` has an invertible transpose. So the derived counit along the affine
morphism `tₙ : Xₙ ⟶ Xₙ₊₁`, read at `Fₙ[0]`, is the comparison of the derived pullback with the
degreewise one followed by an isomorphism (Stacks 0FPI in degree `0`). This is
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.StageTransitionCounitCompatible`, the
compatibility used to identify the transpose of the transition map with the base change map of
Stacks 0A1P.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.isIso_homEquiv_symm_transitionAdjoint`:
  the transpose of `Fₙ₊₁ ⟶ tₙ,* Fₙ` is `φₙ`, an isomorphism.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTransitionCounitCompatible`: the
  compatibility at every `n`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u}) (n : ℕ)

/-- The transpose `tₙ^* Fₙ₊₁ ⟶ Fₙ` of the map `Fₙ₊₁ ⟶ tₙ,* Fₙ` adjoint to `φₙ` is `φₙ`, an
isomorphism. -/
theorem isIso_homEquiv_symm_transitionAdjoint :
    IsIso (((modulePullbackAdjunction D.B D.S D.containsLimitBase
      (D.transition n)).homEquiv _ _).symm (D.transitionAdjoint n)) := by
  rw [transitionAdjoint, ← Adjunction.homEquiv_unit, Equiv.symm_apply_apply]
  infer_instance

/-- **The single-degree compatibility of the derived and underived adjunctions along `tₙ`**
(Stacks 0FPI in degree `0`): for every `n`, the map
`Ltₙ^*(Fₙ₊₁[0]) ⟶ Ltₙ^*((tₙ,* Fₙ)[0]) ≅ Ltₙ^*Rtₙ,*(Fₙ[0]) ⟶ Fₙ[0]` built from the adjoint of
`φₙ` and the derived counit is the comparison `Ltₙ^*(Fₙ₊₁[0]) ⟶ (tₙ^*Fₙ₊₁)[0]` followed by an
isomorphism. -/
theorem stageTransitionCounitCompatible : D.StageTransitionCounitCompatible n :=
  singleCounitCompatible (B := D.B) (S := D.S) (hS := D.containsLimitBase) (D.transition n)
    (D.isAffineHom_transition n) (D.F n) (D.isQuasicoherentOnSite_F n) (D.transitionAdjoint n)
    (D.isIso_homEquiv_symm_transitionAdjoint n)

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
