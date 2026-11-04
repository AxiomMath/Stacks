module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetFactorIso
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetChase

/-!
# The inclusion of the top piece through the factorization `f = π ∘ ι`

Let `f : X ⟶ S` be a morphism of schemes, factored on ringed spaces as `ι : X ⟶ (X, f⁻¹𝒪_S)`
followed by `π`, and let `M` be a sheaf of modules on `X`. The inclusion of the top piece of the
de Rham complex is assembled from `Rf_*` of the identification `Q(M[-n][2n]) ≅ Q(M[0])[n]`, the
commutation of `Rf_*` with the shift and the comparison `Rf_* ≅ Rπ_* ∘ Rι_*`. This file shows that
this composite, followed by `Rπ_*` of a morphism `t` out of `ι_*M[-n]`, is the factorization
isomorphism followed by `Rπ_*` of the inverse comparison `Rι_*(Q(M[-n][2n])) ⟶ Q(ι_*(M[-n][2n]))`
and of `Q(t[2n])`.

## Main definitions

* `DerivedCategory.singleShiftTwoMulIso`: the isomorphism `Q(M[-n][2n]) ≅ Q(M[0])[n]`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.map_singleShiftTwoMulIso_comp_topPiece`

## Implementation notes

The single complex `T = M[-n]`, the morphisms `tc0 : ι_*T ⟶ K` and `tcs : ι_*(T[2n]) ⟶ K[2n]` are
parameters with the equations defining them, so that the statement applies verbatim to the
complexes of a relative duality situation, which are equal to these by definition only.

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

namespace DerivedCategory

variable (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The isomorphism `Q(M[-n][2n]) ≅ Q(M[0])[n]` of a shifted single complex in the derived
category. -/
def singleShiftTwoMulIso (M : C) (n : ℤ) :
    Q.obj (((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj M)⟦2 * n⟧) ≅
      (Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M))⟦n⟧ :=
  Q.mapIso (((CochainComplex.singleFunctors C).shiftIso (2 * n) (-n) n (by omega)).app M ≪≫
      (((CochainComplex.singleFunctors C).shiftIso n (-n) 0 (by omega)).app M).symm) ≪≫
    (Q.commShiftIso n).app _

end DerivedCategory

namespace AlgebraicGeometry.Scheme.Hom

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The inclusion of the top piece through the factorization `f = π ∘ ι`: `Rg_*` of
`Q(M[-n][2n]) ≅ Q(M[0])[n]`, the commutations with the shift and `Rg_* ≅ Rπ_* ∘ Rι_*`, followed by
`Rπ_*` of `Q(t[2n])`, is the factorization isomorphism followed by `Rπ_*` of the inverse of the
comparison `Q(ι_*(T[2n])) ⟶ Rι_*(Q(T[2n]))` and of `Q(tcs)`. -/
theorem map_singleShiftTwoMulIso_comp_topPiece (g : X.toSheafedSpace ⟶ S.toSheafedSpace)
    (hg : toInverseImageBase f ≫ inverseImageBaseProjection f = g) (M : X.Modules) (n : ℤ)
    (T : CochainComplex (ModulesOn X.toRingedSpace) ℤ)
    (hT : T = (HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ) n).obj M)
    {K : CochainComplex (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf
      ((TopCat.Sheaf.pullback CommRingCat f.base).obj S.sheaf))) ℕ}
    (t : (HomologicalComplex.single (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf
      ((TopCat.Sheaf.pullback CommRingCat f.base).obj S.sheaf))) (ComplexShape.up ℤ) n).obj
      ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj M) ⟶ K.extend
          ComplexShape.embeddingUpNat)
    (tc0 : (pushforwardComplex (toInverseImageBase f)).obj T ⟶ K.extend ComplexShape.embeddingUpNat)
    (htc0 : eqToHom (congrArg (pushforwardComplex (toInverseImageBase f)).obj hT) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (StacksDraft.KFlat.modulePushforward (toInverseImageBase f)) (ComplexShape.up ℤ) n).hom.app
            M ≫
        t = tc0)
    (tcs : (pushforwardComplex (toInverseImageBase f)).obj (T⟦2 * n⟧) ⟶
      (K.extend ComplexShape.embeddingUpNat)⟦2 * n⟧)
    (htcs : tcs = ((pushforwardComplex (toInverseImageBase f)).commShiftIso (2 * n)).hom.app T ≫
      tc0⟦2 * n⟧') :
    letI := derivedPushforwardCommShift g
    letI := derivedPushforwardCommShift (inverseImageBaseProjection f)
    (derivedPushforward g).map (eqToHom (congrArg (fun Tc => DerivedCategory.Q.obj (Tc⟦2 * n⟧)) hT)
        ≫ (DerivedCategory.singleShiftTwoMulIso (ModulesOn X.toRingedSpace) M n).hom) ≫
      (((((derivedPushforward g).commShiftIso n).app (DerivedCategory.Q.obj
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) : DerivedCategory
          X.Modules)).hom) ≫ (shiftFunctor (DerivedCategory (SheafOfModules (structureSheafRing
          S.toSheafedSpace))) n).map
        ((eqToIso (congrArg (fun φ => (derivedPushforward φ).obj (DerivedCategory.Q.obj
            ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) : DerivedCategory
            X.Modules))
          hg.symm)).hom ≫
          ((derivedPushforwardCompIso (toInverseImageBase f) (inverseImageBaseProjection
              f)).symm.app (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules
              (ComplexShape.up ℤ) 0).obj M) : DerivedCategory X.Modules)).hom ≫
          (derivedPushforward (inverseImageBaseProjection f)).map
          ((derivedPushforward (toInverseImageBase f)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm ≪≫
          ((derivedPushforwardSingleIso (toInverseImageBase f)).app M).symm).hom) ≫
        (((((derivedPushforward (inverseImageBaseProjection f)).commShiftIso n).app
            ((DerivedCategory.singleFunctor (SheafOfModules (structureSheafRing (inverseImageBase
            f))) 0).obj ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj
            M))).symm).hom) ≫
        (derivedPushforward (inverseImageBaseProjection f)).map
        ((((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by omega)).app
            ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj M) ≪≫
          (((DerivedCategory.singleFunctors _).shiftIso (2 * n) (-n) n (by omega)).app
              ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj M)).symm
              ≪≫
          (shiftFunctor _ (2 * n)).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ _ n).app
                ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj
                M))).hom)) ≫
      (derivedPushforward (inverseImageBaseProjection f)).map ((shiftFunctor (DerivedModules
          (inverseImageBase f).sheaf) (2 * n)).map (DerivedCategory.Q.map t)) =
    (inverseImageBaseFactorIso f g hg).hom.app (DerivedCategory.Q.obj (T⟦2 * n⟧)) ≫
      (derivedPushforward (inverseImageBaseProjection f)).map ((@inv _ _ _ _ (pushforwardComparisonQ
          (toInverseImageBase f) (T⟦2 * n⟧))
          (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase f _)) ≫
              (DerivedCategory.Q.map tcs) ≫ ((DerivedCategory.Q.commShiftIso (2 * n)).hom.app
              (K.extend ComplexShape.embeddingUpNat))) := by
  subst htcs
  subst htc0
  subst hT
  simp only [eqToHom_refl, Category.id_comp]
  subst hg
  simp only [inverseImageBaseFactorIso, eqToIso_refl, Iso.trans_refl, Iso.symm_hom, Iso.refl_hom,
      Category.id_comp]
  let := derivedPushforwardCommShift (toInverseImageBase f ≫ inverseImageBaseProjection f)
  let := derivedPushforwardCommShift (inverseImageBaseProjection f)
  let := derivedPushforwardCommShift (toInverseImageBase f)
  have := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.commShift_derivedPushforwardCompIso_hom
    (toInverseImageBase f) (inverseImageBaseProjection f)
  have G1 : ((((derivedPushforward (toInverseImageBase f)) ⋙ (derivedPushforward
      (inverseImageBaseProjection f))).commShiftIso n).hom.app (DerivedCategory.Q.obj
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) : DerivedCategory
      X.Modules)) ≫ (shiftFunctor (DerivedCategory (SheafOfModules (structureSheafRing
      S.toSheafedSpace))) n).map ((derivedPushforwardCompIso (toInverseImageBase f)
      (inverseImageBaseProjection f)).hom.app (DerivedCategory.Q.obj ((HomologicalComplex.single
      X.Modules (ComplexShape.up ℤ) 0).obj M) : DerivedCategory X.Modules)) =
      (derivedPushforwardCompIso (toInverseImageBase f) (inverseImageBaseProjection f)).hom.app
      ((DerivedCategory.Q.obj ((HomologicalComplex.single (ModulesOn X.toRingedSpace)
      (ComplexShape.up ℤ) 0).obj M))⟦n⟧) ≫ ((((derivedPushforward (toInverseImageBase f ≫
      inverseImageBaseProjection f)).commShiftIso n).app (DerivedCategory.Q.obj
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) : DerivedCategory
      X.Modules)).hom) :=
    NatTrans.shift_app_comm (derivedPushforwardCompIso (toInverseImageBase f)
        (inverseImageBaseProjection f)).hom n _
  have Gc : ((((derivedPushforward (toInverseImageBase f)) ⋙ (derivedPushforward
      (inverseImageBaseProjection f))).commShiftIso n).hom.app (DerivedCategory.Q.obj
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) : DerivedCategory
      X.Modules)) = (derivedPushforward (inverseImageBaseProjection f)).map (((derivedPushforward
      (toInverseImageBase f)).commShiftIso n).hom.app (DerivedCategory.Q.obj
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) : DerivedCategory
      X.Modules)) ≫ (fun K => ((derivedPushforward (inverseImageBaseProjection f)).commShiftIso
      n).hom.app K) ((derivedPushforward (toInverseImageBase f)).obj (DerivedCategory.Q.obj
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) : DerivedCategory
      X.Modules)) :=
    Functor.commShiftIso_comp_hom_app _ _ _ _
  have G4 : (derivedPushforward (inverseImageBaseProjection f)).map ((shiftFunctor (DerivedCategory
      (ModulesOn (inverseImageBase f))) n).map ((derivedPushforward (toInverseImageBase f)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm ≪≫
          ((derivedPushforwardSingleIso (toInverseImageBase f)).app M).symm).hom) ≫ (fun K =>
              ((derivedPushforward (inverseImageBaseProjection f)).commShiftIso n).hom.app K)
              ((DerivedCategory.singleFunctor (SheafOfModules (structureSheafRing (inverseImageBase
              f))) 0).obj ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase
              f)).obj M)) = (fun K => ((derivedPushforward (inverseImageBaseProjection
              f)).commShiftIso n).hom.app K) ((derivedPushforward (toInverseImageBase f)).obj
              (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
              0).obj M) : DerivedCategory X.Modules)) ≫ (shiftFunctor (DerivedCategory
              (SheafOfModules (structureSheafRing S.toSheafedSpace))) n).map ((derivedPushforward
              (inverseImageBaseProjection f)).map ((derivedPushforward (toInverseImageBase
              f)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm ≪≫
          ((derivedPushforwardSingleIso (toInverseImageBase f)).app M).symm).hom) :=
    Functor.commShiftIso_hom_naturality _ _ _
  have G4' : (fun K => ((derivedPushforward (inverseImageBaseProjection f)).commShiftIso n).hom.app
      K) ((DerivedCategory.singleFunctor (SheafOfModules (structureSheafRing (inverseImageBase f)))
      0).obj ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj M)) ≫
      (((((derivedPushforward (inverseImageBaseProjection f)).commShiftIso n).app
      ((DerivedCategory.singleFunctor (SheafOfModules (structureSheafRing (inverseImageBase f)))
      0).obj ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj
      M))).symm).hom) = 𝟙 _ :=
    (((derivedPushforward (inverseImageBaseProjection f)).commShiftIso n).hom_inv_id_app _)
  have G5 : (pushforwardComparisonQ (toInverseImageBase f) (((HomologicalComplex.single (ModulesOn
      X.toRingedSpace) (ComplexShape.up ℤ) n).obj M)⟦2 * n⟧)) ≫ (derivedPushforward
      (toInverseImageBase f)).map (DerivedCategory.singleShiftTwoMulIso (ModulesOn X.toRingedSpace)
      M n).hom ≫ (((derivedPushforward (toInverseImageBase f)).commShiftIso n).hom.app
      (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) :
      DerivedCategory X.Modules)) ≫ (shiftFunctor (DerivedCategory (ModulesOn (inverseImageBase f)))
      n).map ((derivedPushforward (toInverseImageBase f)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm ≪≫
          ((derivedPushforwardSingleIso (toInverseImageBase f)).app M).symm).hom ≫
              ((((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by omega)).app
              ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj M) ≪≫
          (((DerivedCategory.singleFunctors _).shiftIso (2 * n) (-n) n (by omega)).app
              ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj M)).symm
              ≪≫
          (shiftFunctor _ (2 * n)).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ _ n).app
                ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj
                M))).hom) = (DerivedCategory.Q.map (((pushforwardComplex (toInverseImageBase
                f)).commShiftIso (2 * n)).hom.app
          ((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ) n).obj M)) ≫
        (DerivedCategory.Q.commShiftIso (2 * n)).hom.app ((pushforwardComplex (toInverseImageBase
            f)).obj ((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ)
            n).obj M)) ≫
        (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (StacksDraft.KFlat.modulePushforward (toInverseImageBase f)) (ComplexShape.up ℤ)
              n).hom.app
            M))⟦2 * n⟧') :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardComparisonQ_singleShift
      (toInverseImageBase f) M n
  have hc : (@inv _ _ _ _ (pushforwardComparisonQ (toInverseImageBase f)
      (((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ) n).obj M)⟦2 *
      n⟧))
          (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase f _)) ≫
              (pushforwardComparisonQ (toInverseImageBase f) (((HomologicalComplex.single (ModulesOn
              X.toRingedSpace) (ComplexShape.up ℤ) n).obj M)⟦2 * n⟧)) = 𝟙 _ :=
    @IsIso.inv_hom_id _ _ _ _ _
        (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase f _)
  have G6 : (DerivedCategory.Q.map (((pushforwardComplex (toInverseImageBase f)).commShiftIso (2 *
      n)).hom.app
            ((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ) n).obj M) ≫
          ((HomologicalComplex.singleMapHomologicalComplex
            (StacksDraft.KFlat.modulePushforward (toInverseImageBase f)) (ComplexShape.up ℤ)
                n).hom.app M ≫
            t)⟦2 * n⟧')) ≫ ((DerivedCategory.Q.commShiftIso (2 * n)).hom.app (K.extend
                ComplexShape.embeddingUpNat)) = (DerivedCategory.Q.map (((pushforwardComplex
                (toInverseImageBase f)).commShiftIso (2 * n)).hom.app
          ((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ) n).obj M)) ≫
        (DerivedCategory.Q.commShiftIso (2 * n)).hom.app ((pushforwardComplex (toInverseImageBase
            f)).obj ((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ)
            n).obj M)) ≫
        (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (StacksDraft.KFlat.modulePushforward (toInverseImageBase f)) (ComplexShape.up ℤ)
              n).hom.app
            M))⟦2 * n⟧') ≫ ((shiftFunctor (DerivedModules (inverseImageBase f).sheaf) (2 * n)).map
                (DerivedCategory.Q.map t)) :=
    Stacks.GradedTargetChase.shift_map_comp_chase DerivedCategory.Q (shiftFunctor _ (2 * n))
        (shiftFunctor _ (2 * n)) _ _ t _ _
      (Functor.commShiftIso_hom_naturality DerivedCategory.Q _ (2 * n))
  exact Stacks.GradedTargetChase.topPiece_chase (DX' := DerivedCategory (ModulesOn (inverseImageBase
      f)))
    (derivedPushforward (toInverseImageBase f)) (derivedPushforward (inverseImageBaseProjection f))
        (derivedPushforward (toInverseImageBase f ≫ inverseImageBaseProjection f))
        (derivedPushforwardCompIso (toInverseImageBase f) (inverseImageBaseProjection f))
        (shiftFunctor (DerivedCategory (ModulesOn (inverseImageBase f))) n) (shiftFunctor
        (DerivedCategory (SheafOfModules (structureSheafRing S.toSheafedSpace))) n) (F0 :=
        (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) :
        DerivedCategory X.Modules))
    (DerivedCategory.singleShiftTwoMulIso (ModulesOn X.toRingedSpace) M n).hom
        ((((derivedPushforward (toInverseImageBase f ≫ inverseImageBaseProjection f)).commShiftIso
        n).app
        (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) :
        DerivedCategory X.Modules)).hom) ((((derivedPushforward (toInverseImageBase f)) ⋙
        (derivedPushforward (inverseImageBaseProjection f))).commShiftIso n).hom.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) :
        DerivedCategory X.Modules)) (((derivedPushforward (toInverseImageBase f)).commShiftIso
        n).hom.app (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ)
        0).obj M) : DerivedCategory X.Modules)) (fun K => ((derivedPushforward
        (inverseImageBaseProjection f)).commShiftIso n).hom.app K) (((((derivedPushforward
        (inverseImageBaseProjection f)).commShiftIso n).app ((DerivedCategory.singleFunctor
        (SheafOfModules (structureSheafRing (inverseImageBase f))) 0).obj
        ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj M))).symm).hom)
        (((derivedPushforwardCompIso (toInverseImageBase f) (inverseImageBaseProjection f)).symm.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) :
        DerivedCategory X.Modules)).hom) ((derivedPushforward (toInverseImageBase f)).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm ≪≫
          ((derivedPushforwardSingleIso (toInverseImageBase f)).app M).symm).hom
              ((((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by omega)).app
              ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj M) ≪≫
          (((DerivedCategory.singleFunctors _).shiftIso (2 * n) (-n) n (by omega)).app
              ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj M)).symm
              ≪≫
          (shiftFunctor _ (2 * n)).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ _ n).app
                ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase f)).obj
                M))).hom) ((shiftFunctor (DerivedModules (inverseImageBase f).sheaf) (2 * n)).map
                (DerivedCategory.Q.map t)) (pushforwardComparisonQ (toInverseImageBase f)
                (((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ) n).obj
                M)⟦2 * n⟧)) (@inv _ _ _ _ (pushforwardComparisonQ (toInverseImageBase f)
                (((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ) n).obj
                M)⟦2 * n⟧))
          (Stacks.Cohomology.BoxKunneth.isIso_pushforwardComparisonQ_toInverseImageBase f _))
              (DerivedCategory.Q.map (((pushforwardComplex (toInverseImageBase f)).commShiftIso (2 *
              n)).hom.app
          ((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ) n).obj M)) ≫
        (DerivedCategory.Q.commShiftIso (2 * n)).hom.app ((pushforwardComplex (toInverseImageBase
            f)).obj ((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ)
            n).obj M)) ≫
        (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (StacksDraft.KFlat.modulePushforward (toInverseImageBase f)) (ComplexShape.up ℤ)
              n).hom.app
            M))⟦2 * n⟧') (DerivedCategory.Q.map (((pushforwardComplex (toInverseImageBase
                f)).commShiftIso (2 * n)).hom.app
            ((HomologicalComplex.single (ModulesOn X.toRingedSpace) (ComplexShape.up ℤ) n).obj M) ≫
          ((HomologicalComplex.singleMapHomologicalComplex
            (StacksDraft.KFlat.modulePushforward (toInverseImageBase f)) (ComplexShape.up ℤ)
                n).hom.app M ≫
            t)⟦2 * n⟧')) ((DerivedCategory.Q.commShiftIso (2 * n)).hom.app (K.extend
                ComplexShape.embeddingUpNat))
    _ rfl rfl G1 Gc G4 G4' G5 hc G6

end AlgebraicGeometry.Scheme.Hom
