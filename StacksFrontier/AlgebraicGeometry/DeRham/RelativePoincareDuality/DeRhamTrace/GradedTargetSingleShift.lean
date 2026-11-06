module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTopPiece
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetChase

/-!
# The comparison of direct images on a shifted single complex

For a morphism of ringed spaces `f : X ⟶ Y` whose module direct image preserves finite colimits,
and a sheaf of modules `M` on `X`, the comparison `Q(f_*K) ⟶ Rf_*(QK)` of the degreewise and the
derived direct image at `K = M[-n][2n]` is, after the identifications `M[-n][2n] ≅ M[0][n]` and
`Rf_*(M[0]) ≅ (f_*M)[0]`, the canonical isomorphism `Q(f_*(M[-n][2n])) ≅ Q((f_*M)[-n])[2n]`.

## Main results

* `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardComparisonQ_singleShift`

## References

* [Stacks, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ
  pushforwardComparisonQ_naturality)
open RingedSpaceModuleAdjunction (modulePushforward)

universe u

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
  [PreservesFiniteColimits (modulePushforward f)]

/-- The comparison `Q(f_*K) ⟶ Rf_*(QK)` at the shifted single complex `K = M[-n][2n]`, followed by
the identifications of `M[-n][2n]` with `M[0][n]` and of `Rf_*(M[0])` with `(f_*M)[0]`, is the
commutation of the degreewise direct image with the shift and with single complexes. -/
theorem pushforwardComparisonQ_singleShift (M : SheafOfModules.{u} (structureSheafRing X)) (n : ℤ) :
    letI := derivedPushforwardCommShift f
    pushforwardComparisonQ f (((HomologicalComplex.single (ModulesOn X) (ComplexShape.up ℤ) n).obj
        M)⟦2 * n⟧) ≫
      (derivedPushforward f).map (DerivedCategory.Q.map
          (((CochainComplex.singleFunctors (ModulesOn X)).shiftIso (2 * n) (-n) n (by
              omega)).hom.app M ≫
            ((CochainComplex.singleFunctors (ModulesOn X)).shiftIso n (-n) 0 (by omega)).inv.app M)
                ≫
          (DerivedCategory.Q.commShiftIso n).hom.app
            ((HomologicalComplex.single (ModulesOn X) (ComplexShape.up ℤ) 0).obj M)) ≫
      ((derivedPushforward f).commShiftIso n).hom.app
        (DerivedCategory.Q.obj ((HomologicalComplex.single (ModulesOn X) (ComplexShape.up ℤ) 0).obj
            M)) ≫
      ((derivedPushforward f).map ((DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app M) ≫
        (derivedPushforwardSingleIso f).inv.app M)⟦n⟧' ≫
      ((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by omega)).hom.app
        ((modulePushforward f).obj M) ≫
      ((DerivedCategory.singleFunctors _).shiftIso (2 * n) (-n) n (by omega)).inv.app
        ((modulePushforward f).obj M) ≫
      ((DerivedCategory.singleFunctorIsoCompQ _ n).hom.app ((modulePushforward f).obj M))⟦2 * n⟧' =
    DerivedCategory.Q.map (((pushforwardComplex f).commShiftIso (2 * n)).hom.app
        ((HomologicalComplex.single (ModulesOn X) (ComplexShape.up ℤ) n).obj M)) ≫
      (DerivedCategory.Q.commShiftIso (2 * n)).hom.app
        ((pushforwardComplex f).obj ((HomologicalComplex.single (ModulesOn X) (ComplexShape.up ℤ)
            n).obj M)) ≫
      (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
        (StacksDraft.KFlat.modulePushforward f) (ComplexShape.up ℤ) n).hom.app M))⟦2 * n⟧' := by
  let := derivedPushforwardCommShift f
  have F1 := pushforwardComparisonQ_naturality f
    (((CochainComplex.singleFunctors (ModulesOn X)).shiftIso (2 * n) (-n) n (by omega)).hom.app M ≫
      ((CochainComplex.singleFunctors (ModulesOn X)).shiftIso n (-n) 0 (by omega)).inv.app M)
  have F2 := pushforwardComparisonQ_commShift f
    ((HomologicalComplex.single (ModulesOn X) (ComplexShape.up ℤ) 0).obj M) n
  have F3 := derivedPushforwardSingleIso_hom_app_eq f M
  have F7 := CochainComplex.mapHomologicalComplex_singleShift
    (StacksDraft.KFlat.modulePushforward f) M n
  have F5 : ((DerivedCategory.singleFunctors (SheafOfModules.{u} (structureSheafRing Y))).shiftIso
      n (-n) 0 (by omega)).hom.app ((modulePushforward f).obj M) =
      (DerivedCategory.Q.commShiftIso n).inv.app
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj ((modulePushforward f).obj M)) ≫
      DerivedCategory.Q.map (((CochainComplex.singleFunctors _).shiftIso n (-n) 0 (by
          omega)).hom.app
        ((modulePushforward f).obj M)) := by
    simp [DerivedCategory.singleFunctors]
  have F6 : ((DerivedCategory.singleFunctors (SheafOfModules.{u} (structureSheafRing Y))).shiftIso
      (2 * n) (-n) n (by omega)).inv.app ((modulePushforward f).obj M) =
      DerivedCategory.Q.map (((CochainComplex.singleFunctors _).shiftIso (2 * n) (-n) n
        (by omega)).inv.app ((modulePushforward f).obj M)) ≫
      (DerivedCategory.Q.commShiftIso (2 * n)).hom.app
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj ((modulePushforward f).obj M)) :=
            by
    simp [DerivedCategory.singleFunctors]
  exact Stacks.GradedTargetChase.singleShift_chase (pushforwardComplex f) DerivedCategory.Q
      DerivedCategory.Q
    (derivedPushforward f) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 F2 F3
    ((derivedPushforwardSingleIso f).hom_inv_id_app M)
    ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward f) (ComplexShape.up ℤ)
      0).hom_inv_id_app M)
    ((derivedPushforward f).map_id _) rfl
    (Functor.commShiftIso_hom_naturality DerivedCategory.Q
      ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward f) (ComplexShape.up ℤ)
        0).hom.app M) n)
    F5 ((DerivedCategory.Q.commShiftIso n).hom_inv_id_app _) F6 F7
    (Functor.commShiftIso_hom_naturality DerivedCategory.Q
      ((HomologicalComplex.singleMapHomologicalComplex (StacksDraft.KFlat.modulePushforward f)
        (ComplexShape.up ℤ) n).hom.app M) (2 * n))

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
