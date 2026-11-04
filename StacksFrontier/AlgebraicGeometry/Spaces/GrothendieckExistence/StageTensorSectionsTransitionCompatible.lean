module

public import StacksFrontier.AlgebraicGeometry.Spaces.TensorSingleSectionsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPushforwardUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EtaleStageSectionsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.LimitTensorSectionsBaseChange

/-!
# Compatibility of `RΓ(X, E ⊗^𝐋 iₙ,* Fₙ) ≅ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` with the transitions

In Situation [Stacks, Tag 0CX4], `ψₙ : RΓ(X, E ⊗^𝐋 (iₙ,* Fₙ)[0]) ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ[0])`
(`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsMap`) is the composite of
`(iₙ,* Fₙ)[0] ≅ Riₙ,*(Fₙ[0])`, the projection formula along `iₙ` and
`RΓ(Spec A, Rf_* Riₙ,* -) ≅ RΓ(Spec Aₙ, Rfₙ,* -)`. This file proves, as an equation of natural
transformations in `E`, that the `ψₙ` carry `RΓ(X, E ⊗^𝐋 -)` of the transition
`iₙ₊₁,* Fₙ₊₁ ⟶ iₙ,* Fₙ` to the transition map along `tₙ : Xₙ ⟶ Xₙ₊₁` of
`AlgebraicGeometry.Space.tensorSingleSectionsTransitionNatTrans`. Its component at `E` is the
transition map `Mₙ₊₁ ⟶ Mₙ` of `Mₙ = RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ[0])`
(`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsTransition`) read in
`D(A)`, which gives the hypothesis `htr` of
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.isPerfect_limitTensorSections_and_isIso_of`.

The statement for variable spaces is
`AlgebraicGeometry.Space.tensorSingleSectionsNatTrans_comp`, along `iₙ = tₙ ≫ iₙ₊₁`; its last
input, the compatibility of the maps `(f_*F)[0] ⟶ Rf_*(F[0])` with composition, is
`AlgebraicGeometry.Space.modulePushforwardSingleToDerived_comp`.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsNatTransOf_transition`:
  the compatibility as an equation of natural transformations in `E`.

## Implementation notes

The statement in the situation is an instance of the statement for variable spaces, with the
base objects, the spaces and `(B, S, hS)` passed as named arguments.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u}) (n : ℕ)

/-- **The `ψₙ` are compatible with the transitions, as natural transformations in `E`**:
`RΓ(X, - ⊗^𝐋 (iₙ₊₁,* Fₙ₊₁ ⟶ iₙ,* Fₙ)[0])` followed by `ψₙ` is `ψₙ₊₁` followed by the transition map
along `tₙ` of `tensorSingleSectionsNatTrans_comp`. -/
theorem stageTensorSectionsNatTransOf_transition :
    Functor.whiskerRight ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.map
        ((DerivedCategory.singleFunctor _ 0).map (D.pushforwardTransition n)))
        (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (limitBaseObject D.system D.B D.containsLimitBase)) ≫
      D.stageTensorSectionsNatTransOf n (D.F n) (D.isQuasicoherentOnSite_F n) =
    D.stageTensorSectionsNatTransOf (n + 1) (D.F (n + 1)) (D.isQuasicoherentOnSite_F (n + 1)) ≫
      tensorSingleSectionsTransitionNatTrans D.B D.S D.containsLimitBase
        (U₁ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))
        (U₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
        (U := limitBaseObject D.system D.B D.containsLimitBase)
        (X := D.X.left) (X₁ := D.stage (n + 1)) (X₀ := D.stage n)
        (D.stageToBase (n + 1)) (D.stageToBase n)
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))
        (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
        (D.closedImmersion (n + 1)) (D.transition n) (D.closedImmersion n)
        (D.transition_closedImmersion n) (D.transition_comp_stageToBase n)
        (D.stageRingHom_eq_comp n) (D.F n) (D.F (n + 1)) (D.transitionAdjoint n) := by
  rw [D.stageTensorSectionsNatTransOf_eq_tensorSingleSectionsNatTrans n,
    D.stageTensorSectionsNatTransOf_eq_tensorSingleSectionsNatTrans (n + 1)]
  exact tensorSingleSectionsNatTrans_comp D.B D.S D.containsLimitBase
    (U := limitBaseObject D.system D.B D.containsLimitBase)
    (U₁ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))
    (U₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
    (X := D.X.left) (X₁ := D.stage (n + 1)) (X₀ := D.stage n) D.X.hom (D.stageToBase (n + 1))
    (D.stageToBase n)
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))
    (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (baseObjectTransition_baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (D.closedImmersion (n + 1)) (D.transition n) (D.closedImmersion n)
    (D.transition_closedImmersion n) (D.closedImmersion_comp_hom (n + 1))
    (D.transition_comp_stageToBase n) (D.closedImmersion_comp_hom n) (D.stageRingHom_eq_comp n)
    (D.isAffineHom_closedImmersion (n + 1)) (D.isAffineHom_closedImmersion n)
    (D.F n) (D.isQuasicoherentOnSite_F n) (D.F (n + 1)) (D.isQuasicoherentOnSite_F (n + 1))
    (D.transitionAdjoint n) (D.pushforwardCompIso n) rfl (D.pushforwardTransition n) rfl
    (modulePushforwardSingleToDerived_comp D.B D.S D.containsLimitBase (X := D.X.left)
      (X₁ := D.stage (n + 1)) (X₀ := D.stage n) (D.transition n) (D.closedImmersion (n + 1))
      (D.closedImmersion n) (D.transition_closedImmersion n) (D.F n))

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
