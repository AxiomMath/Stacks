module

public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionReduction

/-!
# The unwhiskered base change comparison, computed

`Dualizing.restrictionBaseChangeIsoGeneral` is the comparison isomorphism of Stacks 0661 before it
is whiskered by `RHom_R(A, -)`. Its inverse is the derived component of
`RingTheory.TorIndependence.derivedBaseChangeComparison`, and the counit equations of that
comparison hold for it.

## Main results

* `Dualizing.restrictionBaseChangeIsoGeneral_inv_eq`: the inverse of the unwhiskered comparison
  is the derived component of `RingTheory.TorIndependence.derivedBaseChangeComparison`.
* `Dualizing.restrictionBaseChangeIsoGeneral_inv_app_q_obj_comp_counit`: the counit
  compatibility, at the class of an arbitrary cochain complex of `A`-modules.
* `Dualizing.restrictionBaseChangeIsoGeneral_inv_app_q_obj`: the inverse at the class of `K`,
  wherever the counit of derived extension of scalars along `A → A ⊗_R R'` is invertible at `K`;
  this holds at every K-flat complex by
  `CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat`.

## Implementation notes

`Dualizing.restrictionBaseChangeIsoGeneral_inv_eq` holds by `rfl`: the isomorphism is
`(CategoryTheory.asIso _).symm`, whose `inv` field is the morphism itself. The two
`IsLeftDerivedFunctor` arguments are instance binders.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp v

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [isLeftDerivedA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]

/-- The inverse of `Dualizing.restrictionBaseChangeIsoGeneral` is the derived component of
`RingTheory.TorIndependence.derivedBaseChangeComparison`. -/
theorem restrictionBaseChangeIsoGeneral_inv_eq :
    (restrictionBaseChangeIsoGeneral.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).inv =
      (RingTheory.TorIndependence.derivedBaseChangeComparison
        (algebraMap R A) (algebraMap R R')
        (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
        ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
          (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
        baseChangeR baseChangeA comparisonR comparisonA).2.1 :=
  rfl

/-- For every cochain complex `K` of `A`-modules, composing the inverse of
`Dualizing.restrictionBaseChangeIsoGeneral` at the class of `K` with the counit of derived
extension of scalars along `A → A ⊗_R R'`, restricted along `R' → A ⊗_R R'`, is the counit along
`R → R'` at the restriction of `K` followed by the underived comparison. -/
theorem restrictionBaseChangeIsoGeneral_inv_app_q_obj_comp_counit
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ) :
    (restrictionBaseChangeIsoGeneral.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
          baseChangeA comparisonA isLeftDerivedA).inv.app (DerivedCategory.Q.obj K) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R' (TensorProduct R A R'))).mapDerivedCategory.map
          (comparisonA.app K) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R' (TensorProduct R A R'))).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
            (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) =
      baseChangeR.map
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategoryFactors.hom.app K) ≫
        comparisonR.app
          (((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (RingTheory.TorIndependence.derivedBaseChangeComparison
              (algebraMap R A) (algebraMap R R')
              (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
              ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
                (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
              baseChangeR baseChangeA comparisonR comparisonA).1
            (ComplexShape.up ℤ)).app K) := by
  have : (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uR, uRp}
      (algebraMap R R')).isLeftAdjoint
  have : (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
      (algebraMap A (TensorProduct R A R'))).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uA, max uA uRp}
      (algebraMap A (TensorProduct R A R'))).isLeftAdjoint
  rw [restrictionBaseChangeIsoGeneral_inv_eq.{uR, uA, uRp, v} hTor baseChangeR comparisonR
    baseChangeA comparisonA]
  exact RingTheory.TorIndependence.derivedBaseChangeComparison_snd_app_comp_counit.{uR, uA, uRp,
    max uA uRp, v} (algebraMap R A) (algebraMap R R')
    (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
    ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
      (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
    baseChangeR baseChangeA comparisonR comparisonA K

/-- If the counit of derived extension of scalars along `A → A ⊗_R R'` is invertible at `K`, the
inverse of `Dualizing.restrictionBaseChangeIsoGeneral` at the class of `K` is the counit along
`R → R'` at the restriction of `K`, followed by the underived comparison and the inverse of the
restricted counit. -/
theorem restrictionBaseChangeIsoGeneral_inv_app_q_obj
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ) [IsIso (comparisonA.app K)] :
    (restrictionBaseChangeIsoGeneral.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).inv.app (DerivedCategory.Q.obj K) =
      (baseChangeR.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapDerivedCategoryFactors.hom.app K) ≫
          comparisonR.app
            (((ModuleCat.restrictScalars.{max v uR uA uRp}
              (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (RingTheory.TorIndependence.derivedBaseChangeComparison
                (algebraMap R A) (algebraMap R R')
                (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
                ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
                  (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
                baseChangeR baseChangeA comparisonR comparisonA).1
              (ComplexShape.up ℤ)).app K)) ≫
        CategoryTheory.inv
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R' (TensorProduct R A R'))).mapDerivedCategory.map
              (comparisonA.app K) ≫
            (ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R' (TensorProduct R A R'))).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
                (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K)) := by
  rw [IsIso.eq_comp_inv]
  exact restrictionBaseChangeIsoGeneral_inv_app_q_obj_comp_counit hTor baseChangeR comparisonR
    baseChangeA comparisonA K

end Dualizing

end
