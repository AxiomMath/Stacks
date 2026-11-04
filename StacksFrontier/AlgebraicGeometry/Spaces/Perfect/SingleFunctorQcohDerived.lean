module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardLeftTExact
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral

/-!
# A quasi-coherent module in degree zero lies in `D_QCoh`

A quasi-coherent `𝒪_X`-module `ℳ` on an algebraic space `X`, placed in degree zero, is an object
of `D_QCoh(𝒪_X)`: its only nonzero cohomology sheaf is `ℳ` itself.

## Main results

* `AlgebraicGeometry.Space.qcohDerived_singleFunctor_obj_of_isQuasicoherentOnSite`: a
  quasi-coherent module placed in degree zero lies in `D_QCoh`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
-- `QcohDerived` is stated at the standard model of the derived category.
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A quasi-coherent module placed in degree zero lies in `D_QCoh`.** -/
theorem qcohDerived_singleFunctor_obj_of_isQuasicoherentOnSite (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) [M.IsQuasicoherentOnSite] :
    QcohDerived B S hS X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
      (inferInstance : M.IsQuasicoherentOnSite)
  · rcases lt_or_gt_of_ne hi with hi | hi
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
        (DerivedCategory.isZero_of_isGE _ 0 i hi)
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
        (DerivedCategory.isZero_of_isLE _ 0 i hi)

end AlgebraicGeometry.Space

end
