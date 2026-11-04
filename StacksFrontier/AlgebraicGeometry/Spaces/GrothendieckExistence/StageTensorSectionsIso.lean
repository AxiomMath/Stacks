module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.DerivedLimitBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.BaseObjectAtAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaSnd
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedModulePushforwardSingle
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalDerivedHomBaseChange
public import StacksFrontier.Homology.DerivedCategory.StandardModuleCatModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceEtaleSectionsComparison

/-!
# `RΓ(X, E ⊗^𝐋 iₙ,* Fₙ) = RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` for the infinitesimal stages

In Situation [Stacks, Tag 0CX4] let `iₙ : Xₙ ⟶ X` be the closed immersion of the `n`th
infinitesimal stage, over `Spec Aₙ ⟶ Spec A`. For an object `E` of `D(𝒪_X)` there is a canonical
map

`RΓ(X, E ⊗^𝐋 (iₙ,* Fₙ)[0]) ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ[0])`

of `D(A)`, the target read in `D(A)` by restriction of scalars along `A ⟶ Aₙ`. It is the composite
of

1. the identification `(iₙ,* Fₙ)[0] ≅ Riₙ,*(Fₙ[0])`, `iₙ` being affine and `Fₙ` quasi-coherent;
2. the projection formula `E ⊗^𝐋 Riₙ,*(Fₙ[0]) ⟶ Riₙ,*(Liₙ^*E ⊗^𝐋 Fₙ[0])` with the counit in the
   second factor ([Stacks, Tag 08IN]);
3. the identification `RΓ(X, Riₙ,* -) ≅ RΓ(Xₙ, -)` over the square
   `Xₙ ⟶ X`, `Spec Aₙ ⟶ Spec A`.

It is natural in `E`, and an isomorphism as soon as `E` has quasi-coherent cohomology.

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsMap`: the map.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsMap_eq`: the map is the
  composite of the three steps above.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsMap_naturality`:
  naturality in `E`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.isIso_stageTensorSectionsMap`: the map is an
  isomorphism for `E` with quasi-coherent cohomology.

## References

* [Stacks Project, Tag 0CX4](https://stacks.math.columbia.edu/tag/0CX4)
* [Stacks Project, Tag 08IN](https://stacks.math.columbia.edu/tag/08IN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u}) (n : ℕ)

/-- The square `Xₙ ⟶ X`, `Xₙ ⟶ Spec Aₙ`, `X ⟶ Spec A`, `Spec Aₙ ⟶ Spec A` commutes. -/
theorem closedImmersion_comp_hom :
    D.closedImmersion n ≫ D.X.hom = D.stageToBase n ≫
      representedSpaceMap D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) :=
  ((isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).w).symm

/-- `Fₙ[0]` has quasi-coherent cohomology. -/
theorem qcohDerived_single_F :
    QcohDerived D.B D.S D.containsLimitBase (D.stage n)
      ((DerivedCategory.singleFunctor _ 0).obj (D.F n)) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
      (D.isQuasicoherentOnSite_F n)
  · refine SheafOfModules.IsQuasicoherentOnSite.of_isZero ?_
    rcases lt_or_gt_of_ne hi with h | h
    exacts [DerivedCategory.isZero_of_isGE _ 0 i h, DerivedCategory.isZero_of_isLE _ 0 i h]

variable (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)

/-- `RΓ(X, E ⊗^𝐋 (iₙ,* Fₙ)[0])`, the source of `stageTensorSectionsMap`. -/
abbrev stageTensorSectionsSource :
    StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
      (limitBaseObject D.system D.B D.containsLimitBase), ⊤) :=
  (representedAffineDerivedSections D.B D.S D.containsLimitBase
      (limitBaseObject D.system D.B D.containsLimitBase)).obj
    ((derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom).obj
      (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).obj E).obj
        (D.derivedSystem.obj (op n))))

/-- `Liₙ^*E ⊗^𝐋 Fₙ[0]` on `Xₙ`. -/
abbrev stageTensorObj :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf D.B D.S
      D.containsLimitBase (D.stage n))) :=
  ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).obj
      ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
        (D.closedImmersion n)).obj E)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (D.F n))

/-- `RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ[0])` in `D(Aₙ)`, the sections over `Spec Aₙ`. -/
abbrev stageTensorSectionsTarget :
    StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
      (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n), ⊤) :=
  (representedAffineDerivedSections D.B D.S D.containsLimitBase
      (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).obj
    ((derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n)).obj
      (D.stageTensorObj n E))

omit E in
/-- Step 1 of `ψ_H`: `RΓ(X, - ⊗^𝐋 -)` of the identification `(iₙ,* H)[0] ≅ Riₙ,*(H[0])`
(`derivedModulePushforwardSingleIsoOfIsAffineHom`, inverse). -/
def stageTensorSectionsSingleNatTrans
    (H : Modules.{u, u} D.B D.S D.containsLimitBase (D.stage n).1 (D.stage n).2)
    (hH : H.IsQuasicoherentOnSite) :=
  Functor.whiskerRight ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.map
      (derivedModulePushforwardSingleIsoOfIsAffineHom D.B D.S D.containsLimitBase
          (D.closedImmersion n) (D.isAffineHom_closedImmersion n) H hH).inv)
    (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase))

omit E in
/-- Step 2 of `ψ_H`: `RΓ(X, -)` of the projection formula `smallEtaleProjectionFormulaSndNatTrans`
at `H[0]`. -/
def stageTensorSectionsProjectionNatTrans
    (H : Modules.{u, u} D.B D.S D.containsLimitBase (D.stage n).1 (D.stage n).2) :=
  Functor.whiskerRight (smallEtaleProjectionFormulaSndNatTrans (D.closedImmersion n)
      ((DerivedCategory.singleFunctor _ 0).obj H))
    (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase))

omit E in
/-- Step 3 of `ψ_H`: `affineBaseDerivedSectionsPushforwardIso` at `Liₙ^*(-) ⊗^𝐋 H[0]`. -/
def stageTensorSectionsPushforwardNatTrans
    (H : Modules.{u, u} D.B D.S D.containsLimitBase (D.stage n).1 (D.stage n).2) :=
  Functor.whiskerLeft (smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
      (D.closedImmersion n) ⋙
    (smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.obj
      ((DerivedCategory.singleFunctor _ 0).obj H))
    (affineBaseDerivedSectionsPushforwardIso D.B D.S D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) D.X.hom
      (D.stageToBase n) (D.closedImmersion n) (D.closedImmersion_comp_hom n)).hom

omit E in
/-- For a quasi-coherent `𝒪_{Xₙ}`-module `H`, the natural transformation in `E`
`RΓ(X, E ⊗^𝐋 (iₙ,* H)[0]) ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 H[0])` composed of the identification
`(iₙ,* H)[0] ≅ Riₙ,*(H[0])`, the projection formula `smallEtaleProjectionFormulaSndNatTrans`, and
`affineBaseDerivedSectionsPushforwardIso`. -/
def stageTensorSectionsNatTransOf
    (H : Modules.{u, u} D.B D.S D.containsLimitBase (D.stage n).1 (D.stage n).2)
    (hH : H.IsQuasicoherentOnSite) :
    (smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((modulePushforward D.B D.S D.containsLimitBase (D.closedImmersion n)).obj H)) ⋙
      derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase) ⟶
    smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.closedImmersion n) ⋙
      (smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.obj
        ((DerivedCategory.singleFunctor _ 0).obj H) ⋙
      (derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n) ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)) ⋙
      StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom D.B D.S
          D.containsLimitBase (baseObjectProjection D.system D.B D.containsLimitBase
            D.containsBaseAt n)).hom :=
  D.stageTensorSectionsSingleNatTrans n H hH ≫ D.stageTensorSectionsProjectionNatTrans n H ≫
    D.stageTensorSectionsPushforwardNatTrans n H

omit E in
/-- The natural transformation in `E` `RΓ(X, E ⊗^𝐋 (iₙ,* Fₙ)[0]) ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ[0])`,
`stageTensorSectionsNatTransOf` at `H = Fₙ`. -/
def stageTensorSectionsNatTrans :
    (smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.obj
        (D.derivedSystem.obj (op n)) ⋙
      derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase) ⟶
    smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.closedImmersion n) ⋙
      (smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.obj
        ((DerivedCategory.singleFunctor _ 0).obj (D.F n)) ⋙
      (derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n) ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)) ⋙
      StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom D.B D.S
          D.containsLimitBase (baseObjectProjection D.system D.B D.containsLimitBase
            D.containsBaseAt n)).hom :=
  D.stageTensorSectionsNatTransOf n (D.F n) (D.isQuasicoherentOnSite_F n)

omit E in
/-- `stageTensorSectionsNatTrans` is `stageTensorSectionsNatTransOf` at `H = Fₙ`. -/
theorem stageTensorSectionsNatTrans_eq_natTransOf :
    D.stageTensorSectionsNatTrans n =
      D.stageTensorSectionsNatTransOf n (D.F n) (D.isQuasicoherentOnSite_F n) :=
  rfl

/-- The map `ψ_E : RΓ(X, E ⊗^𝐋 (iₙ,* Fₙ)[0]) ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ[0])` of `D(A)`, the target
restricted along `A ⟶ Aₙ`: the component at `E` of `stageTensorSectionsNatTrans`. -/
def stageTensorSectionsMap :
    D.stageTensorSectionsSource n E ⟶
      (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom D.B D.S
          D.containsLimitBase (baseObjectProjection D.system D.B D.containsLimitBase
            D.containsBaseAt n)).hom).obj (D.stageTensorSectionsTarget n E) :=
  (D.stageTensorSectionsNatTrans n).app E

/-- `stageTensorSectionsMap` is natural in `E`. -/
theorem stageTensorSectionsMap_naturality
    {E E' : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left} (w : E ⟶ E') :
    (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase)).map
        (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.obj
          (D.derivedSystem.obj (op n))).map w) ≫
      D.stageTensorSectionsMap n E' =
    D.stageTensorSectionsMap n E ≫
      (derivedModulePushforward D.B D.S D.containsLimitBase (D.stageToBase n) ⋙
          representedAffineDerivedSections D.B D.S D.containsLimitBase
            (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n) ⋙
          StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom D.B D.S
            D.containsLimitBase (baseObjectProjection D.system D.B D.containsLimitBase
              D.containsBaseAt n)).hom).map
        (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.obj
          ((DerivedCategory.singleFunctor _ 0).obj (D.F n))).map
          ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
            (D.closedImmersion n)).map w)) :=
  (D.stageTensorSectionsNatTrans n).naturality w

omit E in
/-- `stageTensorSectionsNatTrans` is the whiskered composite of the inverse of
`derivedModulePushforwardSingleIsoOfIsAffineHom`, the projection formula
`smallEtaleProjectionFormulaSndNatTrans` and `affineBaseDerivedSectionsPushforwardIso`. -/
theorem stageTensorSectionsNatTrans_eq :
    D.stageTensorSectionsNatTrans n =
  Functor.whiskerRight ((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.map
      (derivedModulePushforwardSingleIsoOfIsAffineHom D.B D.S D.containsLimitBase
          (D.closedImmersion n) (D.isAffineHom_closedImmersion n) (D.F n)
          (D.isQuasicoherentOnSite_F n)).inv)
      (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase)) ≫
    Functor.whiskerRight (smallEtaleProjectionFormulaSndNatTrans (D.closedImmersion n)
        ((DerivedCategory.singleFunctor _ 0).obj (D.F n)))
      (derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
        representedAffineDerivedSections D.B D.S D.containsLimitBase
          (limitBaseObject D.system D.B D.containsLimitBase)) ≫
    Functor.whiskerLeft (smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase
        (D.closedImmersion n) ⋙
      (smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.obj
        ((DerivedCategory.singleFunctor _ 0).obj (D.F n)))
      (affineBaseDerivedSectionsPushforwardIso D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) D.X.hom
        (D.stageToBase n) (D.closedImmersion n) (D.closedImmersion_comp_hom n)).hom :=
  rfl

/-- `stageTensorSectionsMap` is the component at `E` of `stageTensorSectionsNatTrans`. -/
theorem stageTensorSectionsMap_eq :
    D.stageTensorSectionsMap n E = (D.stageTensorSectionsNatTrans n).app E :=
  rfl

/-- `stageTensorSectionsMap` is an isomorphism when `E` has quasi-coherent cohomology. -/
theorem isIso_stageTensorSectionsMap (hE : QcohDerived D.B D.S D.containsLimitBase D.X.left E) :
    IsIso (D.stageTensorSectionsMap n E) := by
  have hσ := isIso_smallEtaleProjectionFormulaMapSnd D.B D.S D.containsLimitBase
    (D.closedImmersion n)
    (isQuasiCompact_of_isAffineHom_hom (D.closedImmersion n) (D.isAffineHom_closedImmersion n))
    (isQuasiSeparated_of_isAffineHom_hom (D.closedImmersion n) (D.isAffineHom_closedImmersion n))
    E hE _ (D.qcohDerived_single_F n)
  have h1 := ((derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
      representedAffineDerivedSections D.B D.S D.containsLimitBase
        (limitBaseObject D.system D.B D.containsLimitBase)).mapIso
    (((smallEtaleDerivedTensor D.B D.S D.containsLimitBase D.X.left).flip.mapIso
      (derivedModulePushforwardSingleIsoOfIsAffineHom D.B D.S D.containsLimitBase
        (D.closedImmersion n) (D.isAffineHom_closedImmersion n) (D.F n)
        (D.isQuasicoherentOnSite_F n)).symm).app E)).isIso_hom
  have h2 : IsIso ((derivedModulePushforward D.B D.S D.containsLimitBase D.X.hom ⋙
      representedAffineDerivedSections D.B D.S D.containsLimitBase
        (limitBaseObject D.system D.B D.containsLimitBase)).map
      ((smallEtaleProjectionFormulaSndNatTrans (D.closedImmersion n)
        ((DerivedCategory.singleFunctor _ 0).obj (D.F n))).app E)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ hσ
  have h3 := ((affineBaseDerivedSectionsPushforwardIso D.B D.S D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) D.X.hom
      (D.stageToBase n) (D.closedImmersion n) (D.closedImmersion_comp_hom n)).app
      ((smallEtaleDerivedModulePullback D.B D.S D.containsLimitBase (D.closedImmersion n) ⋙
          (smallEtaleDerivedTensor D.B D.S D.containsLimitBase (D.stage n)).flip.obj
            ((DerivedCategory.singleFunctor _ 0).obj (D.F n))).obj E)).isIso_hom
  rw [stageTensorSectionsMap_eq, stageTensorSectionsNatTrans_eq]
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 h3)

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
