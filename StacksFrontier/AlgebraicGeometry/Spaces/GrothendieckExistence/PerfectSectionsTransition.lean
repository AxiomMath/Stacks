module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseDerivedSectionsTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorSectionsBaseChangeTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategoryPerfect

/-!
# The transition maps of `RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` in Situation 0CX4

In Situation [Stacks, Tag 0CX4] let `tₙ : Xₙ ⟶ Xₙ₊₁` be the transition closed immersion, over
`Spec Aₙ ⟶ Spec Aₙ₊₁`. For an object `E` of `D(𝒪_X)` write `Mₙ = RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ)` in
`D(Aₙ)`. The **transition map** `Mₙ₊₁ ⟶ Mₙ` of `D(Aₙ₊₁)`, the target read by restriction of
scalars along `Aₙ₊₁ ⟶ Aₙ`, is the composite of

1. `RΓ(Xₙ₊₁, Liₙ₊₁^*E ⊗^𝐋 -)` of the map `Fₙ₊₁ ⟶ tₙ,* Fₙ` adjoint to `φₙ`;
2. the identification `(tₙ,* Fₙ)[0] ≅ Rtₙ,*(Fₙ[0])`, `tₙ` being affine and `Fₙ` quasi-coherent;
3. the projection formula `Liₙ₊₁^*E ⊗^𝐋 Rtₙ,*(Fₙ[0]) ⟶ Rtₙ,*(Ltₙ^*Liₙ₊₁^*E ⊗^𝐋 Fₙ[0])`;
4. the identification `RΓ(Xₙ₊₁, Rtₙ,* -) ≅ RΓ(Xₙ, -)` over the square
   `Xₙ ⟶ Xₙ₊₁`, `Spec Aₙ ⟶ Spec Aₙ₊₁`;
5. `RΓ(Xₙ, - ⊗^𝐋 Fₙ[0])` of `Ltₙ^*Liₙ₊₁^* ≅ Liₙ^*`.

It is the map `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsMap` built
along `tₙ` in place of `iₙ`.

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsTransition`: the
  transition map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- **`Xₙ = Xₙ₊₁ ×_{Spec Aₙ₊₁} Spec Aₙ`**: the square of the transition `Xₙ ⟶ Xₙ₊₁` of the
infinitesimal base changes over the transition `Spec Aₙ ⟶ Spec Aₙ₊₁` of the affine bases is
cartesian, both being base changes of `X`. -/
theorem isPullback_transitionSpace_spaceBaseProjection (F : ℕᵒᵖ ⥤ CommRingCat.{u})
    (B : BigFppfSite.{u}) (hS : B.Contains (GrothendieckExistence.limitBase F))
    (hSn : ∀ n, B.Contains (GrothendieckExistence.baseAt F n))
    (X : Over (schemeSpace (limitBaseObject F B hS))) (n : ℕ) :
    IsPullback (transitionSpace F B hS hSn X n) (spaceBaseProjection F B hS hSn X n)
      (spaceBaseProjection F B hS hSn X (n + 1)) (baseSpaceTransition F B hS hSn n) := by
  refine IsPullback.of_right (h₁₂ := spaceProjection F B hS hSn X (n + 1))
    (h₂₂ := baseSpaceProjection F B hS hSn (n + 1)) (v₁₃ := X.hom) ?_
    (transitionSpace_spaceBaseProjection F B hS hSn X n)
    (isPullback_spaceAt F B hS hSn X (n + 1)).flip
  rw [transitionSpace_spaceProjection, baseSpaceTransition_baseSpaceProjection]
  exact (isPullback_spaceAt F B hS hSn X n).flip

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u}) (n : ℕ)

/-- The square `Xₙ ⟶ Xₙ₊₁`, `Xₙ ⟶ Spec Aₙ`, `Xₙ₊₁ ⟶ Spec Aₙ₊₁`, `Spec Aₙ ⟶ Spec Aₙ₊₁` commutes. -/
theorem transition_comp_stageToBase :
    D.transition n ≫ D.stageToBase (n + 1) = D.stageToBase n ≫
      representedSpaceMap D.B D.S D.containsLimitBase
        (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n) :=
  transitionSpace_spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n

/-- `tₙ : Xₙ ⟶ Xₙ₊₁` is an affine morphism. -/
theorem isAffineHom_transition :
    IsAffineHom D.B D.S D.containsLimitBase (D.transition n).hom :=
  isAffineHom_of_isClosedImmersion _ _ _ _ (D.isClosedImmersion_transition n)

/-- `Ltₙ^* Liₙ₊₁^* ≅ Liₙ^*`, from `iₙ₊₁ ∘ tₙ = iₙ`. -/
def stagePullbackCompIso :
    smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.closedImmersion (n + 1)) ⋙
        smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.transition n) ≅
      smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.closedImmersion n) :=
  smallEtaleDerivedModulePullbackCompIso D.B D.S D.containsLimitBase (D.transition n)
      (D.closedImmersion (n + 1)) ≪≫
    smallEtaleDerivedModulePullbackCongr D.B D.S D.containsLimitBase
      (D.transition_closedImmersion n)

/-- **The counit of `Ltₙ^* ⊣ Rtₙ,*` at `Fₙ` and the comparison `Ltₙ^* ⟶ tₙ^*`**: the map
`Ltₙ^*(Fₙ₊₁[0]) ⟶ Ltₙ^*((tₙ,* Fₙ)[0]) ≅ Ltₙ^*Rtₙ,*(Fₙ[0]) ⟶ Fₙ[0]` built from the adjoint of `φₙ`
and the derived counit is the comparison `Ltₙ^*(Fₙ₊₁[0]) ⟶ (tₙ^*Fₙ₊₁)[0]` followed by an
isomorphism: `AlgebraicGeometry.Space.SingleCounitCompatible` at `tₙ`, `Fₙ` and the map
`Fₙ₊₁ ⟶ tₙ,* Fₙ` adjoint to `φₙ`. This is the single-degree compatibility of the derived
adjunction with the underived one (Stacks 0FPI) used to identify the transpose of the transition
map with the base change map of Stacks 0A1P. -/
abbrev StageTransitionCounitCompatible (n : ℕ) : Prop :=
  SingleCounitCompatible (D.transition n) (D.isAffineHom_transition n) (D.F n)
    (D.isQuasicoherentOnSite_F n) (D.transitionAdjoint n)

variable (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)

/-- The first factor of `stageTensorSectionsTransition`, before `RΓ(Xₙ₊₁, -)`:
`Liₙ₊₁^*E ⊗^𝐋 Fₙ₊₁[0] ⟶ Liₙ₊₁^*E ⊗^𝐋 Rtₙ,*(Fₙ[0]) ⟶ Rtₙ,*(Ltₙ^*Liₙ₊₁^*E ⊗^𝐋 Fₙ[0])`, the map
`Fₙ₊₁ ⟶ tₙ,* Fₙ` adjoint to `φₙ` read through `(tₙ,* Fₙ)[0] ≅ Rtₙ,*(Fₙ[0])`, then the projection
formula along `tₙ`. -/
def stageTensorSectionsTransitionStage :
    ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage (n + 1))).obj
        ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
          (D.closedImmersion (n + 1))).obj E)).obj
      ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage (n + 1)) 0).obj (D.F (n + 1))) ⟶
    (derivedModulePushforward D.B D.S D.containsLimitBase (D.transition n)).obj
      (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).obj
          ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.transition n)).obj
            ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
              (D.closedImmersion (n + 1))).obj E))).obj
        ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage n) 0).obj (D.F n))) :=
  smallEtaleProjectionFormulaComp (D.transition n)
    ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
      (D.closedImmersion (n + 1))).obj E)
    ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage (n + 1)) 0).map
        (D.transitionAdjoint n) ≫
      (derivedModulePushforwardSingleIsoOfIsAffineHom D.B D.S D.containsLimitBase
        (D.transition n) (D.isAffineHom_transition n) (D.F n) (D.isQuasicoherentOnSite_F n)).inv :
      _ ⟶ (derivedModulePushforward D.B D.S D.containsLimitBase (D.transition n)).obj
        ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage n) 0).obj (D.F n)))

/-- The last factor of `stageTensorSectionsTransition`, before restriction of scalars:
`RΓ(Xₙ, - ⊗^𝐋 Fₙ[0])` of `Ltₙ^*Liₙ₊₁^*E ≅ Liₙ^*E`. -/
def stageTensorSectionsTransitionPullback :
    (derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n) ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).obj
      (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).obj
          ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.transition n)).obj
            ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
              (D.closedImmersion (n + 1))).obj E))).obj
        ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage n) 0).obj (D.F n))) ⟶
    D.stageTensorSectionsTarget n E :=
  (derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n) ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
        (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.obj
            ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage n) 0).obj (D.F n))).map
          ((D.stagePullbackCompIso n).hom.app E))

/-- **The transition map `Mₙ₊₁ ⟶ Mₙ`** of `Mₙ = RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ[0])`, in `D(Aₙ₊₁)` with the
target restricted along `Aₙ₊₁ ⟶ Aₙ`: `RΓ(Xₙ₊₁, Liₙ₊₁^*E ⊗^𝐋 -)` of `Fₙ₊₁ ⟶ tₙ,* Fₙ`, the
identification `(tₙ,* Fₙ)[0] ≅ Rtₙ,*(Fₙ[0])`, the projection formula along `tₙ`, the
identification `RΓ(Xₙ₊₁, Rtₙ,* -) ≅ RΓ(Xₙ, -)`, and `Ltₙ^*Liₙ₊₁^* ≅ Liₙ^*`. -/
def stageTensorSectionsTransition :
    D.stageTensorSectionsTarget (n + 1) E ⟶
      (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom D.B D.S
          D.containsLimitBase (baseObjectTransition D.system D.B D.containsLimitBase
            D.containsBaseAt n)).hom).obj (D.stageTensorSectionsTarget n E) :=
  affineBaseDerivedSectionsPushforwardComp D.B D.S D.containsLimitBase
    (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
    (D.stageToBase (n + 1)) (D.stageToBase n) (D.transition n) (D.transition_comp_stageToBase n)
    (D.stageTensorSectionsTransitionStage n E) (D.stageTensorSectionsTransitionPullback n E)

/-- **The transpose of the transition map `Mₙ₊₁ ⟶ Mₙ`** under derived extension and restriction
of scalars along `Aₙ₊₁ ⟶ Aₙ`: the base change map of `RΓ` over the square `Xₙ ⟶ Xₙ₊₁`,
`Spec Aₙ ⟶ Spec Aₙ₊₁` at `Liₙ₊₁^*E ⊗^𝐋 Fₙ₊₁[0]`, followed by `RΓ(Xₙ, -)` of the transpose of
`stageTensorSectionsTransitionStage` under `Ltₙ^* ⊣ Rtₙ,*` and by
`stageTensorSectionsTransitionPullback`. -/
theorem homEquiv_symm_stageTensorSectionsTransition :
    ((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
        (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
          (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)).hom).homEquiv
        ((derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase (n + 1)) ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))).obj
        (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage (n + 1))).obj
          ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
            (D.closedImmersion (n + 1))).obj E)).obj
        ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage (n + 1)) 0).obj (D.F (n + 1)))))
        (D.stageTensorSectionsTarget n E)).symm (D.stageTensorSectionsTransition n E) =
      affineBaseDerivedSectionsBaseChangeMap D.B D.S D.containsLimitBase
          (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
          (D.stageToBase (n + 1)) (D.stageToBase n) (D.transition n)
          (D.transition_comp_stageToBase n) _ ≫
        (derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n) ⋙
            representedAffineDerivedSections D.B D.S D.containsLimitBase
              (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
          (((smallEtaleDerivedModuleAdjunction D.B D.S D.containsLimitBase
              (D.transition n)).homEquiv _ _).symm (D.stageTensorSectionsTransitionStage n E)) ≫
          D.stageTensorSectionsTransitionPullback n E :=
  homEquiv_symm_affineBaseDerivedSectionsPushforwardComp D.B D.S D.containsLimitBase _ _ _ _ _ _ _

/-- **The transpose of the transition map `Mₙ₊₁ ⟶ Mₙ` is invertible**, i.e.
`Mₙ₊₁ ⊗^𝐋_{Aₙ₊₁} Aₙ ≅ Mₙ`, for a perfect `E`, given the single-degree compatibility of the derived
and underived adjunctions along `tₙ` (`StageTransitionCounitCompatible`): it is the base change
map of Stacks 0A1P for the cartesian square `Xₙ ⟶ Xₙ₊₁` over `Spec Aₙ ⟶ Spec Aₙ₊₁` at
`Liₙ₊₁^*E ⊗^𝐋 Fₙ₊₁[0]`, `Fₙ₊₁` being of finite presentation, flat over `Aₙ₊₁` with support proper
over `Aₙ₊₁`, followed by `Ltₙ^*Liₙ₊₁^*E ⊗^𝐋 φₙ` and `Ltₙ^*Liₙ₊₁^* ≅ Liₙ^*`. -/
theorem isIso_homEquiv_symm_stageTensorSectionsTransition
    (hE : spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E)
    (h : D.StageTransitionCounitCompatible n) :
    IsIso (((RingTheory.TorIndependence.totalDerivedExtensionScalarsAdjunction
        (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
          (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)).hom).homEquiv
        ((derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase (n + 1)) ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))).obj
        (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage (n + 1))).obj
          ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
            (D.closedImmersion (n + 1))).obj E)).obj
        ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage (n + 1)) 0).obj (D.F (n + 1)))))
        (D.stageTensorSectionsTarget n E)).symm (D.stageTensorSectionsTransition n E)) := by
  rw [homEquiv_symm_stageTensorSectionsTransition]
  have sq : IsPullback (D.transition n) (D.stageToBase n) (D.stageToBase (n + 1))
      (representedSpaceMap D.B D.S D.containsLimitBase
        (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)) :=
    isPullback_transitionSpace_spaceBaseProjection D.system D.B D.containsLimitBase
      D.containsBaseAt D.X n
  have key := isIso_affineBaseDerivedSectionsBaseChangeMap_comp_projectionFormula
    (B := D.B) (S := D.S) (hS := D.containsLimitBase)
    (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
    (D.stageToBase (n + 1)) (D.stageToBase n) (D.transition n) sq
    (isFinitePresentation_spaceBaseProjection D.system D.B D.containsLimitBase D.containsBaseAt
      D.X D.finitePresentation (n + 1))
    ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
      (D.closedImmersion (n + 1))).obj E)
    (isPerfect_smallEtaleDerivedModulePullback (D.closedImmersion (n + 1)) E hE) (D.F (n + 1))
    (SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' (D.F (n + 1))
      (D.finitelyPresented (n + 1)))
    (D.flat (n + 1)) (D.properSupport (n + 1)) (D.isAffineHom_transition n) (D.F n)
    (D.isQuasicoherentOnSite_F n) (D.transitionAdjoint n) (D.qcohDerived_single_F (n + 1)) h
  have hP : IsIso (D.stageTensorSectionsTransitionPullback n E) :=
    isIso_map_map_flip_smallEtaleDerivedTensor (B := D.B) (S := D.S) (hS := D.containsLimitBase)
      (D.stageToBase n)
      ((spaceDerivedSingle D.B D.S D.containsLimitBase (D.stage n) 0).obj (D.F n))
      ((D.stagePullbackCompIso n).app E)
  exact (congrArg IsIso (Category.assoc _ _ _)).mp (IsIso.comp_isIso' key hP)

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
