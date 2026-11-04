module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetTopPiece

/-!
# The inclusion of the top piece of a relative duality situation

For a relative duality situation `D` with `f : X ⟶ S` of relative dimension `n`, the complex
`Ω^n[-n]` shifted by `2n` is identified in the derived category with `Ω^n[n]`
(`AlgebraicGeometry.RelativeDualitySituation.topComplexShiftHom`). This file computes `Rf_*` of
this identification followed by the inclusion `Rf_*Ω^n[n] ⟶ Rf_*(Ω^•[2n])` of the top piece: it is
the factorization isomorphism `Rf_* ≅ Rπ_* ∘ Rι_*` followed by `Rπ_*` of the inverse comparison
`Rι_*(Q(Ω^n[-n][2n])) ⟶ Q(ι_*(Ω^n[-n][2n]))` and of the inclusion of `ι_*Ω^n[-n]` into the
de Rham complex, shifted by `2n`.

## Main definitions

* `AlgebraicGeometry.RelativeDualitySituation.topComplexShiftHom`: the identification
  `Q(Ω^n[-n][2n]) ⟶ Q(Ω^n)[n]`, an isomorphism.

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.map_topComplexShiftHom_comp_topInclusion`: `Rf_*` of
  `topComplexShiftHom` followed by the inclusion of the top piece is the factorization isomorphism
  followed by `Rπ_*` of the inverse comparison and of the inclusion of `ι_*Ω^n[-n]` into the
  de Rham complex, shifted by `2n`.
* `AlgebraicGeometry.RelativeDualitySituation.duality_map_topComplexShiftHom_comp_topInclusion`:
  the same, for the derived direct image `Stacks.Duality.derivedPushforward`.

## References

* [Stacks, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.DeRhamDirectImage (inverseImageBase toInverseImageBase inverseImageBaseProjection)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardCompIso
  derivedPushforwardCommShift derivedPushforwardSingleIso)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open Stacks.DerivedTensor.RingedSite (DerivedModules)

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-- The inclusion of `ι_*Ω^n[-n]` into the de Rham complex is the commutation of `ι_*` with the
single complex followed by the inclusion of the top forms. -/
theorem topComplexToDeRham_eq_comp (D : RelativeDualitySituation.{u}) :
    eqToHom (congrArg (pushforwardComplex (toInverseImageBase D.f)).obj
        (rfl : D.topComplexX = (HomologicalComplex.single (ModulesOn D.X.toRingedSpace)
            (ComplexShape.up ℤ)
          (D.n : ℤ)).obj (Scheme.Hom.relativeDifferentialForms D.f D.n))) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (StacksDraft.KFlat.modulePushforward (toInverseImageBase D.f)) (ComplexShape.up ℤ) (D.n :
            ℤ)).hom.app
          (Scheme.Hom.relativeDifferentialForms D.f D.n) ≫ D.topFormsToDeRham = D.topComplexToDeRham
              := by
  rw [eqToHom_refl]
  exact Category.id_comp _

/-- The identification `Q(Ω^n[-n][2n]) ⟶ Q(Ω^n[0])[n]` of the shifted top complex, an
isomorphism (`AlgebraicGeometry.RelativeDualitySituation.isIso_topComplexShiftHom`). -/
def topComplexShiftHom (D : RelativeDualitySituation.{u}) :
    DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧) ⟶ (D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧ :=
  (eqToHom (congrArg (fun Tc => DerivedCategory.Q.obj (Tc⟦2 * (D.n : ℤ)⟧)) (rfl : D.topComplexX =
      (HomologicalComplex.single (ModulesOn D.X.toRingedSpace) (ComplexShape.up ℤ) (D.n : ℤ)).obj
      (Scheme.Hom.relativeDifferentialForms D.f D.n))) ≫
    (DerivedCategory.singleShiftTwoMulIso (ModulesOn D.X.toRingedSpace)
      (Scheme.Hom.relativeDifferentialForms D.f D.n) (D.n : ℤ)).hom)

/-- The identification of the shifted top complex is an isomorphism. -/
instance isIso_topComplexShiftHom (D : RelativeDualitySituation.{u}) : IsIso D.topComplexShiftHom :=
  IsIso.comp_isIso' inferInstance (Iso.isIso_hom (DerivedCategory.singleShiftTwoMulIso
    (ModulesOn D.X.toRingedSpace) (Scheme.Hom.relativeDifferentialForms D.f D.n) (D.n : ℤ)))

/-- `Rf_*` of `topComplexShiftHom` followed by the inclusion of the top piece, unfolded. -/
theorem map_topComplexShiftHom_comp_topInclusion_eq_shift (D : RelativeDualitySituation.{u}) :
    letI := derivedPushforwardCommShift D.f.toLRSHom.toShHom
    letI := derivedPushforwardCommShift (inverseImageBaseProjection D.f)
    @CategoryTheory.Functor.map _ _ _ _ (derivedPushforward D.f.toLRSHom.toShHom)
        (DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧) : DerivedCategory (SheafOfModules
        (structureSheafRing D.X.toSheafedSpace))) _ D.topComplexShiftHom ≫ D.topInclusion =
      (derivedPushforward D.f.toLRSHom.toShHom).map (eqToHom (congrArg (fun Tc =>
          DerivedCategory.Q.obj (Tc⟦2 * (D.n : ℤ)⟧)) (rfl : D.topComplexX =
          (HomologicalComplex.single (ModulesOn D.X.toRingedSpace) (ComplexShape.up ℤ) (D.n :
          ℤ)).obj (Scheme.Hom.relativeDifferentialForms D.f D.n))) ≫
          (DerivedCategory.singleShiftTwoMulIso
          (ModulesOn D.X.toRingedSpace) (Scheme.Hom.relativeDifferentialForms D.f D.n) (D.n :
          ℤ)).hom) ≫ (((((derivedPushforward D.f.toLRSHom.toShHom).commShiftIso (D.n : ℤ)).app
          (DerivedCategory.Q.obj ((HomologicalComplex.single D.X.Modules (ComplexShape.up ℤ) 0).obj
          (Scheme.Hom.relativeDifferentialForms D.f D.n)) : DerivedCategory D.X.Modules)).hom) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules (structureSheafRing D.S.toSheafedSpace)))
          (D.n : ℤ)).map
        ((eqToIso (congrArg (fun φ => (derivedPushforward φ).obj (DerivedCategory.Q.obj
            ((HomologicalComplex.single D.X.Modules (ComplexShape.up ℤ) 0).obj
            (Scheme.Hom.relativeDifferentialForms D.f D.n)) : DerivedCategory D.X.Modules))
          (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f).symm)).hom ≫
          ((derivedPushforwardCompIso (toInverseImageBase D.f) (inverseImageBaseProjection
              D.f)).symm.app (DerivedCategory.Q.obj ((HomologicalComplex.single D.X.Modules
              (ComplexShape.up ℤ) 0).obj (Scheme.Hom.relativeDifferentialForms D.f D.n)) :
              DerivedCategory D.X.Modules)).hom ≫
          (derivedPushforward (inverseImageBaseProjection D.f)).map
          ((derivedPushforward (toInverseImageBase D.f)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (Scheme.Hom.relativeDifferentialForms D.f
              D.n)).symm ≪≫
          ((derivedPushforwardSingleIso (toInverseImageBase D.f)).app
              (Scheme.Hom.relativeDifferentialForms D.f D.n)).symm).hom) ≫
        (((((derivedPushforward (inverseImageBaseProjection D.f)).commShiftIso (D.n : ℤ)).app
            ((DerivedCategory.singleFunctor (SheafOfModules (structureSheafRing (inverseImageBase
            D.f))) 0).obj ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase
            D.f)).obj (Scheme.Hom.relativeDifferentialForms D.f D.n)))).symm).hom) ≫
        (derivedPushforward (inverseImageBaseProjection D.f)).map
        ((((DerivedCategory.singleFunctors _).shiftIso (D.n : ℤ) (-(D.n : ℤ)) 0 (by omega)).app
            ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase D.f)).obj
            (Scheme.Hom.relativeDifferentialForms D.f D.n)) ≪≫
          (((DerivedCategory.singleFunctors _).shiftIso (2 * (D.n : ℤ)) (-(D.n : ℤ)) (D.n : ℤ) (by
              omega)).app ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase
              D.f)).obj (Scheme.Hom.relativeDifferentialForms D.f D.n))).symm ≪≫
          (shiftFunctor _ (2 * (D.n : ℤ))).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ _ (D.n : ℤ)).app
                ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase D.f)).obj
                (Scheme.Hom.relativeDifferentialForms D.f D.n)))).hom)) ≫
      (derivedPushforward (inverseImageBaseProjection D.f)).map ((shiftFunctor (DerivedModules
          (inverseImageBase D.f).sheaf) (2 * (D.n : ℤ))).map (DerivedCategory.Q.map
          D.topFormsToDeRham)) := rfl

/-- The unfolded inclusion of the top piece of `map_topComplexShiftHom_comp_topInclusion_eq_shift`
through the factorization isomorphism. -/
theorem map_singleShiftTwoMulIso_comp_shift_eq_factorIso (D : RelativeDualitySituation.{u}) :
    letI := derivedPushforwardCommShift D.f.toLRSHom.toShHom
    letI := derivedPushforwardCommShift (inverseImageBaseProjection D.f)
    (derivedPushforward D.f.toLRSHom.toShHom).map (eqToHom (congrArg (fun Tc =>
        DerivedCategory.Q.obj (Tc⟦2 * (D.n : ℤ)⟧)) (rfl : D.topComplexX = (HomologicalComplex.single
        (ModulesOn D.X.toRingedSpace) (ComplexShape.up ℤ) (D.n : ℤ)).obj
        (Scheme.Hom.relativeDifferentialForms D.f D.n))) ≫ (DerivedCategory.singleShiftTwoMulIso
        (ModulesOn D.X.toRingedSpace) (Scheme.Hom.relativeDifferentialForms D.f D.n) (D.n : ℤ)).hom)
        ≫
      (((((derivedPushforward D.f.toLRSHom.toShHom).commShiftIso (D.n : ℤ)).app
          (DerivedCategory.Q.obj ((HomologicalComplex.single D.X.Modules (ComplexShape.up ℤ) 0).obj
          (Scheme.Hom.relativeDifferentialForms D.f D.n)) : DerivedCategory D.X.Modules)).hom) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules (structureSheafRing D.S.toSheafedSpace)))
          (D.n : ℤ)).map
        ((eqToIso (congrArg (fun φ => (derivedPushforward φ).obj (DerivedCategory.Q.obj
            ((HomologicalComplex.single D.X.Modules (ComplexShape.up ℤ) 0).obj
            (Scheme.Hom.relativeDifferentialForms D.f D.n)) : DerivedCategory D.X.Modules))
          (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f).symm)).hom ≫
          ((derivedPushforwardCompIso (toInverseImageBase D.f) (inverseImageBaseProjection
              D.f)).symm.app (DerivedCategory.Q.obj ((HomologicalComplex.single D.X.Modules
              (ComplexShape.up ℤ) 0).obj (Scheme.Hom.relativeDifferentialForms D.f D.n)) :
              DerivedCategory D.X.Modules)).hom ≫
          (derivedPushforward (inverseImageBaseProjection D.f)).map
          ((derivedPushforward (toInverseImageBase D.f)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (Scheme.Hom.relativeDifferentialForms D.f
              D.n)).symm ≪≫
          ((derivedPushforwardSingleIso (toInverseImageBase D.f)).app
              (Scheme.Hom.relativeDifferentialForms D.f D.n)).symm).hom) ≫
        (((((derivedPushforward (inverseImageBaseProjection D.f)).commShiftIso (D.n : ℤ)).app
            ((DerivedCategory.singleFunctor (SheafOfModules (structureSheafRing (inverseImageBase
            D.f))) 0).obj ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase
            D.f)).obj (Scheme.Hom.relativeDifferentialForms D.f D.n)))).symm).hom) ≫
        (derivedPushforward (inverseImageBaseProjection D.f)).map
        ((((DerivedCategory.singleFunctors _).shiftIso (D.n : ℤ) (-(D.n : ℤ)) 0 (by omega)).app
            ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase D.f)).obj
            (Scheme.Hom.relativeDifferentialForms D.f D.n)) ≪≫
          (((DerivedCategory.singleFunctors _).shiftIso (2 * (D.n : ℤ)) (-(D.n : ℤ)) (D.n : ℤ) (by
              omega)).app ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase
              D.f)).obj (Scheme.Hom.relativeDifferentialForms D.f D.n))).symm ≪≫
          (shiftFunctor _ (2 * (D.n : ℤ))).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ _ (D.n : ℤ)).app
                ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase D.f)).obj
                (Scheme.Hom.relativeDifferentialForms D.f D.n)))).hom)) ≫
      (derivedPushforward (inverseImageBaseProjection D.f)).map ((shiftFunctor (DerivedModules
          (inverseImageBase D.f).sheaf) (2 * (D.n : ℤ))).map (DerivedCategory.Q.map
          D.topFormsToDeRham)) =
    (Scheme.Hom.inverseImageBaseFactorIso D.f D.f.toLRSHom.toShHom
        (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f)).hom.app (DerivedCategory.Q.obj
        (D.topComplexX⟦2 * (D.n : ℤ)⟧)) ≫
      (derivedPushforward (inverseImageBaseProjection D.f)).map ((@inv _ _ _ _
          (pushforwardComparisonQ (toInverseImageBase D.f) (D.topComplexX⟦2 * (D.n : ℤ)⟧))
          (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase D.f _)) ≫
              (DerivedCategory.Q.map D.topComplexToDeRhamShift) ≫ ((DerivedCategory.Q.commShiftIso
              (2 * (D.n : ℤ))).hom.app (D.deRhamCx.extend ComplexShape.embeddingUpNat))) :=
  (Scheme.Hom.map_singleShiftTwoMulIso_comp_topPiece D.f D.f.toLRSHom.toShHom
    (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f) (Scheme.Hom.relativeDifferentialForms D.f
        D.n) D.n
    D.topComplexX (rfl : D.topComplexX = (HomologicalComplex.single (ModulesOn D.X.toRingedSpace)
        (ComplexShape.up ℤ) (D.n : ℤ)).obj (Scheme.Hom.relativeDifferentialForms D.f D.n))
        D.topFormsToDeRham D.topComplexToDeRham (D.topComplexToDeRham_eq_comp)
    D.topComplexToDeRhamShift rfl)

/-- `Rf_*` of `topComplexShiftHom` followed by the inclusion of the top piece, through the
factorization isomorphism, with the commutations of the direct images with the shift in
context. -/
theorem map_topComplexShiftHom_comp_topInclusion_eq_factorIso (D : RelativeDualitySituation.{u}) :
    letI := derivedPushforwardCommShift D.f.toLRSHom.toShHom
    letI := derivedPushforwardCommShift (inverseImageBaseProjection D.f)
    @CategoryTheory.Functor.map _ _ _ _ (derivedPushforward D.f.toLRSHom.toShHom)
        (DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧) : DerivedCategory (SheafOfModules
        (structureSheafRing D.X.toSheafedSpace))) _ D.topComplexShiftHom ≫ D.topInclusion =
         (Scheme.Hom.inverseImageBaseFactorIso D.f D.f.toLRSHom.toShHom
             (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f)).hom.app (DerivedCategory.Q.obj
             (D.topComplexX⟦2 * (D.n : ℤ)⟧)) ≫
      (derivedPushforward (inverseImageBaseProjection D.f)).map ((@inv _ _ _ _
          (pushforwardComparisonQ (toInverseImageBase D.f) (D.topComplexX⟦2 * (D.n : ℤ)⟧))
          (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase D.f _)) ≫
              (DerivedCategory.Q.map D.topComplexToDeRhamShift) ≫ ((DerivedCategory.Q.commShiftIso
              (2 * (D.n : ℤ))).hom.app (D.deRhamCx.extend ComplexShape.embeddingUpNat))) :=
  (map_topComplexShiftHom_comp_topInclusion_eq_shift D).trans
    (map_singleShiftTwoMulIso_comp_shift_eq_factorIso D)

/-- `Rf_*` of `topComplexShiftHom` followed by the inclusion of the top piece is the factorization
isomorphism followed by `Rπ_*` of the inverse comparison and of the inclusion of `ι_*Ω^n[-n]`
into the de Rham complex, shifted by `2n`. -/
theorem map_topComplexShiftHom_comp_topInclusion (D : RelativeDualitySituation.{u}) :
    @CategoryTheory.Functor.map _ _ _ _ (derivedPushforward D.f.toLRSHom.toShHom)
        (DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧) : DerivedCategory (SheafOfModules
        (structureSheafRing D.X.toSheafedSpace))) _ D.topComplexShiftHom ≫ D.topInclusion =
      (Scheme.Hom.inverseImageBaseFactorIso D.f D.f.toLRSHom.toShHom
          (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f)).hom.app
          (DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧)) ≫
        (derivedPushforward (inverseImageBaseProjection D.f)).map
          (@inv _ _ _ _ (pushforwardComparisonQ (toInverseImageBase D.f) (D.topComplexX⟦(2 * D.n :
              ℤ)⟧))
              (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase D.f _) ≫
            DerivedCategory.Q.map D.topComplexToDeRhamShift ≫
            (DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.app
              (D.deRhamCx.extend ComplexShape.embeddingUpNat)) :=
  map_topComplexShiftHom_comp_topInclusion_eq_factorIso D

/-- `map_topComplexShiftHom_comp_topInclusion` for the derived direct image of
`Stacks.Duality.derivedPushforward`. -/
theorem duality_map_topComplexShiftHom_comp_topInclusion (D : RelativeDualitySituation.{u}) :
    @CategoryStruct.comp _ _ _ ((Stacks.Duality.derivedPushforward D.f).obj
        ((D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧ : DerivedCategory D.X.Modules)) _
      ((Stacks.Duality.derivedPushforward D.f).map D.topComplexShiftHom) D.topInclusion =
      (Scheme.Hom.inverseImageBaseFactorIso D.f D.f.toLRSHom.toShHom
          (Stacks.DeRhamDirectImage.toInverseImageBase_comp D.f)).hom.app
          (DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧)) ≫
        (derivedPushforward (inverseImageBaseProjection D.f)).map
          (@inv _ _ _ _ (pushforwardComparisonQ (toInverseImageBase D.f) (D.topComplexX⟦(2 * D.n :
              ℤ)⟧))
              (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase D.f _) ≫
            DerivedCategory.Q.map D.topComplexToDeRhamShift ≫
            (DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.app
              (D.deRhamCx.extend ComplexShape.embeddingUpNat)) :=
  map_topComplexShiftHom_comp_topInclusion D

end AlgebraicGeometry.RelativeDualitySituation
