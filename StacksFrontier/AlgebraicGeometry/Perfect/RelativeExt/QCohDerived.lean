module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PerfectStage
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeMayerVietoris.Qcoh
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# `D_QCoh` at the standard model

The objects of `D(𝒪_S)`, for a scheme `S`, whose cohomology sheaves are quasi-coherent form a
class of objects stable under shifts and binary biproducts and containing the quasi-coherent
modules placed in degree zero. This file records these facts at the standard model of the
derived category.

## Main definitions

* `Stacks.Cohomology.RelativeExt.DStd`: `D(𝒪_S)` at the standard model.
* `Stacks.Cohomology.RelativeExt.qcohDerived`: `D_QCoh(𝒪_S)`.

## Main results

* `Stacks.Cohomology.RelativeExt.qcohDerived_shift`: `D_QCoh(𝒪_S)` is stable under shifts.
* `Stacks.Cohomology.RelativeExt.qcohDerived_biprod`: `D_QCoh(𝒪_S)` is stable under binary
  biproducts.
* `Stacks.Cohomology.RelativeExt.qcohDerived_single`: a quasi-coherent module in degree zero lies
  in `D_QCoh(𝒪_S)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard

/-- Presheaves of abelian groups on the opens of a topological space admit sheafification. -/
theorem hasSheafifyOpensSpace (T : TopCat.{u}) :
    HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _

/-- Weak equivalences of presheaves of abelian groups on the opens of a topological space are the
locally bijective morphisms. -/
theorem wEqualsLocallyBijectiveOpensSpace (T : TopCat.{u}) :
    (Opens.grothendieckTopology T).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _

/-- The derived category of `𝒪_S`-modules at the standard model. -/
abbrev DStd (S : Scheme.{u}) : Type (u + 1) :=
  DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))

/-- **`D_QCoh(𝒪_S)`**: the objects of `D(𝒪_S)` with quasi-coherent cohomology sheaves. -/
def qcohDerived (S : Scheme.{u}) : ObjectProperty (DStd S) :=
  fun N => Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing S.toRingedSpace) N

/-- `D_QCoh(𝒪_S)` is stable under shifts. -/
theorem qcohDerived_shift (S : Scheme.{u}) (N : DStd S) (n : ℤ) (hN : qcohDerived S N) :
    qcohDerived S (N⟦n⟧) := fun i =>
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor _ 0).shiftIso n i (n + i) rfl).app N).symm (hN (n + i))

/-- `D_QCoh(𝒪_S)` is stable under binary biproducts. -/
theorem qcohDerived_biprod (S : Scheme.{u}) (N N' : DStd S) (hN : qcohDerived S N)
    (hN' : qcohDerived S N') : qcohDerived S (N ⊞ N') := fun i =>
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) i)
  (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapBiprod N N').symm
    (Stacks.AlgebraicGeometry.RelativeMayerVietoris.isQuasicoherent_biprod _ _ (hN i) (hN' i))

/-- A quasi-coherent `𝒪_S`-module placed in degree zero lies in `D_QCoh(𝒪_S)`. -/
theorem qcohDerived_single (S : Scheme.{u})
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (hF : F.IsQuasicoherent) :
    qcohDerived S ((DerivedCategory.singleFunctor _ 0).obj F) := by
  intro i
  change ((DerivedCategory.homologyFunctor _ i).obj
    ((DerivedCategory.singleFunctor _ 0).obj F)).IsQuasicoherent
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_isZero
      (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor _ 0).obj F) 0 i hi)
  · exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_isZero
      (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor _ 0).obj F) 0 i hi)

end Stacks.Cohomology.RelativeExt

end
