module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceGlobalHom
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpen

/-!
# Homology sheaves of a module placed in degree zero

Auxiliary results for the untensored base change of `Rf_*ℱ` along a cartesian square, the
base-change half of [Stacks, Tag 0B91] (2), which is
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.baseChangeDerivedPushforward`: a
quasi-coherent module placed in degree zero has quasi-coherent homology sheaves, quasi-coherence
of the homology sheaves transports along isomorphisms, and the ordinary pullback of a module
placed in degree zero is the pullback of the module placed in degree zero.

## Main results

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.isQuasicoherent_homology_singleFunctor`
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.isQuasicoherent_homology_of_iso`
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.pullbackComplexSingleIso`

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open AlgebraicGeometry.ProperFlatBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- **A quasi-coherent module placed in degree zero has quasi-coherent homology sheaves.** -/
theorem isQuasicoherent_homology_singleFunctor {X : Scheme.{u}} (M : X.Modules)
    (hM : M.IsQuasicoherent) (n : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)).IsQuasicoherent := by
  by_cases hn : n = 0
  · subst hn
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app M).symm hM
  · exact Stacks.Duality.isQuasicoherent_of_isZero _
      (Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj M hn)

/-- Quasi-coherence of the homology sheaves transports along an isomorphism in the derived
category. -/
theorem isQuasicoherent_homology_of_iso {X : Scheme.{u}} {A B : DerivedCategory X.Modules}
    (e : A ≅ B) (h : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj B).IsQuasicoherent)
    (n : ℤ) : ((DerivedCategory.homologyFunctor X.Modules n).obj A).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor X.Modules n).mapIso e).symm (h n)

/-- The ordinary pullback of a module placed in degree zero is the pullback of the module placed
in degree zero. -/
def pullbackComplexSingleIso {X X' : Scheme.{u}} (g' : X' ⟶ X) (M : X.Modules) :
    DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj (singleDegreeComplex M)) ≅
      (DerivedCategory.singleFunctor X'.Modules 0).obj ((Scheme.Modules.pullback g').obj M) :=
  DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (StacksDraft.KFlat.modulePullback g'.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X'.Modules 0).app _).symm

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end
