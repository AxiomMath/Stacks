module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The derived pullback of the structure sheaf, at the locally small model

For a morphism `f : X ⟶ Y` of ringed spaces, the derived pullback `Lf^*`
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, and
`Stacks.Duality.derivedPullback` for schemes) sends the structure sheaf `𝒪_Y` placed in degree
zero to `𝒪_X` placed in degree zero, and more generally sends a flat module `F` placed in degree
`n` to `f^*F` placed in degree `n`. The endomorphisms of the
structure sheaf of an affine scheme commute with each other, in the category of modules and in
the derived category.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIsoLocallySmall`,
  `Stacks.Duality.derivedPullbackStructureSheafIso`: `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`, for ringed spaces
  and for schemes.
* `Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackSingleIsoOfIsFlatLocallySmall`,
  `Stacks.Duality.derivedPullbackSingleIsoOfIsFlat`: `Lf^*(F[-n]) ≅ (f^*F)[-n]` for a flat `F`.

## Main results

* `Stacks.Duality.unit_endomorphisms_commute`: the endomorphisms of `𝒪_{Spec R}` commute.
* `Stacks.Duality.derived_unit_endomorphisms_commute`: the endomorphisms of `𝒪_{Spec R}[0]` in
  the derived category commute.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.DerivedPullbackUnit

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The isomorphism `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` for a morphism `f` of ringed spaces, at the locally
small model of the derived categories. -/
def derivedPullbackUnitIsoLocallySmall :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj
          (SheafOfModules.unit (structureSheafRing Y))) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
        (SheafOfModules.unit (structureSheafRing X)) := by
  haveI : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj
        (SheafOfModules.unit (structureSheafRing Y)))) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.sheaf _ (isFlat_unit Y) 0)
  exact (derivedPullback f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) 0).app
        (SheafOfModules.unit (structureSheafRing Y))) ≪≫
    asIso ((derivedPullbackComparison f).app _) ≪≫
    DerivedCategory.Qh.mapIso (((modulePullback f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app _) ≪≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback f) (ComplexShape.up ℤ) 0).app _) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X)) 0).app
      ((modulePullback f).obj (SheafOfModules.unit (structureSheafRing Y)))).symm ≪≫
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).mapIso
      (modulePullbackObjUnitIso f)

/-- The isomorphism `Lf^*(F[-n]) ≅ (f^*F)[-n]` for a flat module `F` and a morphism `f` of ringed
spaces, at the locally small model of the derived categories. -/
def derivedPullbackSingleIsoOfIsFlatLocallySmall (F : SheafOfModules.{u} (structureSheafRing Y))
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F) (n : ℤ) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) n).obj F) ≅
      (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) n).obj
        ((modulePullback f).obj F) := by
  haveI : IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) n).obj F)) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f _
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Y.sheaf F hF n)
  exact (derivedPullback f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) n).app
        F) ≪≫
    asIso ((derivedPullbackComparison f).app _) ≪≫
    DerivedCategory.Qh.mapIso (((modulePullback f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app _) ≪≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).app _ ≪≫
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (modulePullback f) (ComplexShape.up ℤ) n).app _) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (SheafOfModules.{u} (structureSheafRing X)) n).app
      ((modulePullback f).obj F)).symm

end Stacks.Cohomology.DerivedPullbackUnit

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The isomorphism `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` for a morphism `f` of schemes, at the locally small
model of the derived categories. -/
def derivedPullbackStructureSheafIso :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor Y.Modules 0).obj
        (SheafOfModules.unit Y.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) :=
  Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIsoLocallySmall f.toLRSHom.toShHom

/-- The isomorphism `Lf^*(F[-n]) ≅ (f^*F)[-n]` for a flat module `F` and a morphism `f` of
schemes, at the locally small model of the derived categories. -/
def derivedPullbackSingleIsoOfIsFlat (F : Y.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F) (n : ℤ) :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor Y.Modules n).obj F) ≅
      (DerivedCategory.singleFunctor X.Modules n).obj ((Scheme.Modules.pullback f).obj F) :=
  Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackSingleIsoOfIsFlatLocallySmall
    f.toLRSHom.toShHom F hF n

end Stacks.Duality

namespace Stacks.Duality

variable (R : CommRingCat.{u})

/-- Any two endomorphisms of the structure sheaf of `Spec R` commute. -/
theorem unit_endomorphisms_commute (g h : SheafOfModules.unit (Spec R).ringCatSheaf ⟶
    SheafOfModules.unit (Spec R).ringCatSheaf) : g ≫ h = h ≫ g := by
  obtain ⟨g', rfl⟩ := (tilde.fullyFaithfulFunctor (R := R)).map_surjective
    (X := ModuleCat.of R R) (Y := ModuleCat.of R R) g
  obtain ⟨h', rfl⟩ := (tilde.fullyFaithfulFunctor (R := R)).map_surjective
    (X := ModuleCat.of R R) (Y := ModuleCat.of R R) h
  have hcomm : g' ≫ h' = h' ≫ g' := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have key (φ : ModuleCat.of R R ⟶ ModuleCat.of R R) (y : R) : φ.hom y = y * φ.hom 1 := by
      simpa using φ.hom.map_smul y (1 : R)
    change h'.hom (g'.hom x) = g'.hom (h'.hom x)
    rw [key h' (g'.hom x), key g' x, key g' (h'.hom x), key h' x]
    ring
  exact ((tilde.functor R).map_comp g' h').symm.trans
    ((congrArg (tilde.functor R).map hcomm).trans ((tilde.functor R).map_comp h' g'))

/-- Any two endomorphisms of `𝒪_{Spec R}[0]` in the derived category commute. -/
theorem derived_unit_endomorphisms_commute
    (g h : (DerivedCategory.singleFunctor (Spec R).Modules 0).obj
        (SheafOfModules.unit (Spec R).ringCatSheaf) ⟶
      (DerivedCategory.singleFunctor (Spec R).Modules 0).obj
        (SheafOfModules.unit (Spec R).ringCatSheaf)) :
    g ≫ h = h ≫ g := by
  obtain ⟨g', rfl⟩ := (DerivedCategory.singleFunctor (Spec R).Modules 0).map_surjective g
  obtain ⟨h', rfl⟩ := (DerivedCategory.singleFunctor (Spec R).Modules 0).map_surjective h
  exact ((DerivedCategory.singleFunctor (Spec R).Modules 0).map_comp g' h').symm.trans
    ((congrArg (DerivedCategory.singleFunctor (Spec R).Modules 0).map
      (unit_endomorphisms_commute R g' h')).trans
      ((DerivedCategory.singleFunctor (Spec R).Modules 0).map_comp h' g'))

end Stacks.Duality

end
