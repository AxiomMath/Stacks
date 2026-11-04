module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonMate
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.RestrictionIsoComputation

/-!
# The unit side of the comparison of Stacks 0661

The derived base-change comparison of [stacks 065Z] is the Beck--Chevalley mate of the
identification of the two derived restrictions along a commutative square of rings
(`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonMate`). This file records the
equation that identification satisfies against the units of [stacks 0GMT] for
`Dualizing.restrictionBaseChangeIsoGeneral`, the unwhiskered comparison of [stacks 0661], whose
inverse is the derived comparison of [stacks 065Z] by
`Dualizing.restrictionBaseChangeIsoGeneral_inv_eq`. [stacks 0E2A] reads the comparison of
[stacks 0661] in this packaging.

## Main results

* `Dualizing.unit_comp_restrictionBaseChangeIsoGeneral_inv`: the unit of [stacks 0GMT] along
  `R → R'` followed by the restricted inverse comparison of [stacks 0661] is the restricted unit
  of [stacks 0GMT] along `A → A ⊗_R R'`, through the identification
  `RingTheory.TorIndependence.restrictSquareDerivedIso` of the two derived restrictions to `D(R)`.
  Neither Tor independence nor K-flatness is used.

## Implementation notes

The `Dualizing` specialization lives in its own file because the additivity instance of
degreewise extension of scalars used by
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonMate` (the `private`
`extendScalarsAdditive` of `StacksFrontier.Homology.Tor.IndependenceBaseChange`, which
`RingTheory.TorIndependence.derivedBaseChangeComparison`'s own signature uses) cannot be the
active one in a file that also imports the `Dualizing` chain.

No `@[stacks]` attribute is placed here: [stacks 0661] is already formalized as
`RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent`, and this is a
computation about a particular packaging of it.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

namespace Dualizing

open RingTheory.TorIndependence

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp v

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

/-- **The unit side of the comparison of [stacks 0661].** At an object `W` of `D(A)` the unit of
[stacks 0GMT] along `R → R'` at `W|_R`, followed by the restriction of the inverse of
`Dualizing.restrictionBaseChangeIsoGeneral`, is the restriction along `R → A` of the unit of
[stacks 0GMT] along `A → A ⊗_R R'` at `W`, followed by the identification
`RingTheory.TorIndependence.restrictSquareDerivedIso` of the two derived restrictions to `D(R)`.
-/
theorem unit_comp_restrictionBaseChangeIsoGeneral_inv
    (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) :
    (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
          comparisonR).unit.app
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory.obj W) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R R')).mapDerivedCategory.map
          ((restrictionBaseChangeIsoGeneral.{uR, uA, uRp, v} hTor baseChangeR comparisonR
            isLeftDerivedR baseChangeA comparisonA isLeftDerivedA).inv.app W) =
      (ModuleCat.restrictScalars.{max v uR uA uRp} (algebraMap R A)).mapDerivedCategory.map
          ((derivedExtensionScalarsAdjunction.{uA, max uA uRp, max v uR}
            (algebraMap A (TensorProduct R A R')) baseChangeA comparisonA).unit.app W) ≫
        (restrictSquareDerivedIso.{uR, uA, uRp, max uA uRp, v} (algebraMap R A) (algebraMap R R')
            (algebraMap A (TensorProduct R A R')) (algebraMap R' (TensorProduct R A R'))
            ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
              (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))).hom.app
          (baseChangeA.obj W) := by
  have : (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp} (algebraMap R R')).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uR, uRp}
      (algebraMap R R')).isLeftAdjoint
  have : (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
      (algebraMap A (TensorProduct R A R'))).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp, uA, max uA uRp}
      (algebraMap A (TensorProduct R A R'))).isLeftAdjoint
  rw [restrictionBaseChangeIsoGeneral_inv_eq.{uR, uA, uRp, v} hTor baseChangeR comparisonR
    baseChangeA comparisonA]
  exact unit_comp_derivedBaseChangeComparison.{uR, uA, uRp, max uA uRp, v} (algebraMap R A)
    (algebraMap R R') (algebraMap A (TensorProduct R A R'))
    (algebraMap R' (TensorProduct R A R'))
    ((IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
      (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R')))
    baseChangeR baseChangeA comparisonR comparisonA W

end Dualizing

end
