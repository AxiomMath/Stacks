module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp

/-!
# `ψ` in the module variable, and along the transitions of Situation 0CX4

In Situation [Stacks, Tag 0CX4] the identification
`ψ_H : RΓ(X, E ⊗^𝐋 (iₙ,* H)[0]) ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 H[0])`
(`FlatSheafExistenceSituation.stageTensorSectionsNatTransOf`) is defined for every quasi-coherent
`𝒪_{Xₙ}`-module `H`. This file proves that it is natural in `H`, one step at a time.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsNatTransOf_naturality`:
  naturality of `ψ_H` in `H`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageRingHom_eq_comp`: `A ⟶ Aₙ` factors
  through `Aₙ₊₁`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

/-- The interchange law for a horizontal pair of natural transformations: whiskering
`β : A ⟶ A'` on the right by `F` and then `α : F ⟶ G` on the left by `A'` is whiskering `α` by `A`
and then `β` by `G`. -/
private theorem whiskerRight_comp_whiskerLeft_eq {K D' C : Type*} [Category K] [Category D']
    [Category C] {A A' : K ⥤ D'} {F G : D' ⥤ C} (β : A ⟶ A') (α : F ⟶ G) :
    Functor.whiskerRight β F ≫ Functor.whiskerLeft A' α =
      Functor.whiskerLeft A α ≫ Functor.whiskerRight β G := by
  ext X
  exact α.naturality (β.app X)

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u}) (n : ℕ)
  {H H' : Modules.{u, u} D.B D.S D.containsLimitBase (D.stage n).1 (D.stage n).2}
  (hH : H.IsQuasicoherentOnSite) (hH' : H'.IsQuasicoherentOnSite) (w : H ⟶ H')

omit hH hH' in
/-- **The ring maps of the affine bases compose**: `A ⟶ Aₙ` is `A ⟶ Aₙ₊₁` followed by
`Aₙ₊₁ ⟶ Aₙ`, on the rings of global functions of `Spec A`, `Spec Aₙ₊₁` and `Spec Aₙ`. This is the
compatibility `derivedRestrictScalarsComp` takes to identify restriction along `A ⟶ Aₙ` with
restriction along `A ⟶ Aₙ₊₁ ⟶ Aₙ`. -/
theorem stageRingHom_eq_comp :
    (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom =
      (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
          (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)).hom.comp
        (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
          (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt
            (n + 1))).hom := by
  rw [← representedAffineRingHom_comp, baseObjectTransition_baseObjectProjection]

/-- The projection formula `smallEtaleProjectionFormulaSndNatTrans` along `iₙ`, as a natural
transformation in the module `H` (through `H ↦ H[0]`). -/
def stageProjectionFormulaModuleNatTrans :
    DerivedCategory.singleFunctor _ 0 ⋙
        (derivedModulePushforward D.B D.S D.containsLimitBase (D.closedImmersion n)) ⋙
          (smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip ⟶
      DerivedCategory.singleFunctor _ 0 ⋙
        (smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip ⋙
          (Functor.whiskeringLeft _ _ _).obj
            (smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.closedImmersion n)) ⋙
          (Functor.whiskeringRight _ _ _).obj
            (derivedModulePushforward D.B D.S D.containsLimitBase (D.closedImmersion n)) where
  app M := smallEtaleProjectionFormulaSndNatTrans (D.closedImmersion n)
    ((DerivedCategory.singleFunctor _ 0).obj M)
  naturality M M' v := by
    refine NatTrans.ext (funext fun E => ?_)
    have h := Stacks.ProjectionFormula.adjunctionTensorMapSnd_natural
      (smallEtaleDerivedModuleAdjunction D.B D.S D.containsLimitBase (D.closedImmersion n))
      (Functor.uncurry.obj (smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left))
      (Functor.uncurry.obj (smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)))
      (smallEtaleDerivedPullbackTensorIso (D.closedImmersion n)).hom (𝟙 E)
      ((DerivedCategory.singleFunctor _ 0).map v)
    simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h
    exact h

include hH hH' in
/-- Step 1 of the naturality of `ψ_H` in `H`. -/
theorem stageTensorSectionsSingleNatTrans_naturality :
    Functor.whiskerRight ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf D.B D.S
          D.containsLimitBase D.X.left)) 0).map
          ((modulePushforward D.B D.S D.containsLimitBase (D.closedImmersion n)).map w)))
        (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (limitBaseObject D.system D.B D.containsLimitBase)) ≫
      D.stageTensorSectionsSingleNatTrans n H' hH' =
    D.stageTensorSectionsSingleNatTrans n H hH ≫
      Functor.whiskerRight ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.map
          ((derivedModulePushforward D.B D.S D.containsLimitBase (D.closedImmersion n)).map
            ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (ringedToposStructureRingSheaf D.B D.S D.containsLimitBase (D.stage n))) 0).map w)))
          (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
            representedAffineDerivedSections D.B D.S D.containsLimitBase
              (limitBaseObject D.system D.B D.containsLimitBase)) :=
  (Functor.whiskerRight (Functor.whiskerRight (modulePushforwardSingleToDerived D.B D.S
      D.containsLimitBase (D.closedImmersion n))
      (smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip)
    ((Functor.whiskeringRight _ _ _).obj _)).naturality w

/-- Step 2 of the naturality of `ψ_H` in `H`. -/
theorem stageTensorSectionsProjectionNatTrans_naturality :
    Functor.whiskerRight ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.map
        ((derivedModulePushforward D.B D.S D.containsLimitBase (D.closedImmersion n)).map
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            (ringedToposStructureRingSheaf D.B D.S D.containsLimitBase (D.stage n))) 0).map w)))
        (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (limitBaseObject D.system D.B D.containsLimitBase)) ≫
      D.stageTensorSectionsProjectionNatTrans n H' =
    D.stageTensorSectionsProjectionNatTrans n H ≫
      Functor.whiskerRight (Functor.whiskerLeft
          (smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.closedImmersion n))
          (Functor.whiskerRight
            ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.map
              ((DerivedCategory.singleFunctor (SheafOfModules.{u}
                (ringedToposStructureRingSheaf D.B D.S D.containsLimitBase (D.stage n))) 0).map w))
            (derivedModulePushforward D.B D.S D.containsLimitBase (D.closedImmersion n))))
        (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (limitBaseObject D.system D.B D.containsLimitBase)) :=
  (Functor.whiskerRight (D.stageProjectionFormulaModuleNatTrans n)
    ((Functor.whiskeringRight _ _ _).obj _)).naturality w

/-- Step 3 of the naturality of `ψ_H` in `H`. -/
theorem stageTensorSectionsPushforwardNatTrans_naturality :
    Functor.whiskerRight (Functor.whiskerLeft
        (smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.closedImmersion n))
        (Functor.whiskerRight
          ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.map
            ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (ringedToposStructureRingSheaf D.B D.S D.containsLimitBase (D.stage n))) 0).map w))
          (derivedModulePushforward D.B D.S D.containsLimitBase (D.closedImmersion n))))
        (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (limitBaseObject D.system D.B D.containsLimitBase)) ≫
      D.stageTensorSectionsPushforwardNatTrans n H' =
    D.stageTensorSectionsPushforwardNatTrans n H ≫
      Functor.whiskerLeft
        (smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.closedImmersion n))
        (Functor.whiskerRight
          ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.map
            ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (ringedToposStructureRingSheaf D.B D.S D.containsLimitBase (D.stage n))) 0).map w))
          ((derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n) ⋙
            representedAffineDerivedSections D.B D.S D.containsLimitBase
              (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)) ⋙
          StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom D.B D.S
              D.containsLimitBase (baseObjectProjection D.system D.B D.containsLimitBase
                D.containsBaseAt n)).hom)) :=
  whiskerRight_comp_whiskerLeft_eq
    (Functor.whiskerLeft (smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
      (D.closedImmersion n))
      ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf D.B D.S
          D.containsLimitBase (D.stage n))) 0).map w)))
    (affineBaseDerivedSectionsPushforwardIso D.B D.S D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) D.X.hom
      (D.stageToBase n) (D.closedImmersion n) (D.closedImmersion_comp_hom n)).hom

include hH hH' in
/-- **`ψ_H` is natural in the quasi-coherent module `H`.** For `w : H ⟶ H'`, `ψ_{H'}` after
`RΓ(X, - ⊗^𝐋 (iₙ,* w)[0])` is `ψ_H` followed by `RΓ(Xₙ, Liₙ^*(-) ⊗^𝐋 w[0])`. -/
theorem stageTensorSectionsNatTransOf_naturality :
    Functor.whiskerRight ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.map
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf D.B D.S
          D.containsLimitBase D.X.left)) 0).map
          ((modulePushforward D.B D.S D.containsLimitBase (D.closedImmersion n)).map w)))
        (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (limitBaseObject D.system D.B D.containsLimitBase)) ≫
      D.stageTensorSectionsNatTransOf n H' hH' =
    D.stageTensorSectionsNatTransOf n H hH ≫
      Functor.whiskerLeft
        (smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.closedImmersion n))
        (Functor.whiskerRight
          ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.map
            ((DerivedCategory.singleFunctor (SheafOfModules.{u}
              (ringedToposStructureRingSheaf D.B D.S D.containsLimitBase (D.stage n))) 0).map w))
          ((derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n) ⋙
            representedAffineDerivedSections D.B D.S D.containsLimitBase
              (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)) ⋙
          StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom D.B D.S
              D.containsLimitBase (baseObjectProjection D.system D.B D.containsLimitBase
                D.containsBaseAt n)).hom)) := by
  have e1 := congrArg (· ≫ D.stageTensorSectionsProjectionNatTrans n H' ≫
      D.stageTensorSectionsPushforwardNatTrans n H')
    (D.stageTensorSectionsSingleNatTrans_naturality n hH hH' w)
  have e2 := congrArg (fun x => D.stageTensorSectionsSingleNatTrans n H hH ≫ x ≫
      D.stageTensorSectionsPushforwardNatTrans n H')
    (D.stageTensorSectionsProjectionNatTrans_naturality n w)
  have e3 := congrArg (fun x => D.stageTensorSectionsSingleNatTrans n H hH ≫
      D.stageTensorSectionsProjectionNatTrans n H ≫ x)
    (D.stageTensorSectionsPushforwardNatTrans_naturality n w)
  exact (Category.assoc _ _ _).symm.trans (e1.trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (e2.trans
      ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (e3.trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm))))))

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
