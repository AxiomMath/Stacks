module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullbackSupplement

/-!
# The unit comparison of the derived pullback at any model of the derived category

`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/UnitComparison.lean` constructs the unit
comparison `ν : Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` at the file-local model
`CategoryTheory.HasDerivedCategory.standard`. This file restates it with the two models of the
derived categories free binders, so that it is available at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, where `D_QCoh(𝒪_X)` has the direct sums
compactness is tested against.

## Main definitions

* `derivedPullbackUnitIsoAtModel`: the unit comparison at any pair of models.

## Main results

* `derivedPullbackSingleUnitIsoAtModel_inv_comp_derivedPullbackUnitIsoAtModel_hom`:
  read through `Lf^*(𝒪_Y[0]) ≅ (f^*𝒪_Y)[0]`, it is the degree-zero comparison `f^*𝒪_Y ≅ 𝒪_X`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.SpaceInverseSystems (ringedSiteOfSpace)

universe w₁ w₂ u

namespace Stacks.Cohomology.DerivedPullbackUnit

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{w₁} (_root_.SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (_root_.SheafOfModules.{u} (structureSheafRing Y))]

/-- The identification `Lf^*(𝒪_Y[0]) ≅ (f^*𝒪_Y)[0]`: the complex `𝒪_Y[0]` is K-flat because
`𝒪_Y` is flat, so the derived pullback is computed by the degreewise one.

The two models of the derived categories are free binders rather than the file's pinned
`CategoryTheory.HasDerivedCategory.standard`, as they are in
`Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIsoAtModel` which this is an
instance of. -/
abbrev derivedPullbackSingleUnitIsoAtModel :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y)) 0).obj
          (_root_.SheafOfModules.unit (structureSheafRing Y))) ≅
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj
        ((modulePullback f).obj (_root_.SheafOfModules.unit (structureSheafRing Y))) :=
  Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIsoAtModel f
    (_root_.SheafOfModules.unit (structureSheafRing Y)) (isFlat_unit Y)

/-- **The unit comparison `ν : Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`** of the derived pullback along a
morphism of ringed spaces: the identification of `Lf^*(𝒪_Y[0])` with the degreewise pullback
`(f^*𝒪_Y)[0]`, followed by the degree-zero image of the ordinary comparison
`f^*𝒪_Y ≅ 𝒪_X`.

The two models of the derived categories are free binders, so that the comparison is available
at the locally small model of `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` where
`D_QCoh(𝒪_X)` has the direct sums compactness is tested against; see
`Stacks.Duality.derivedPullbackUnitIsoScheme`. -/
def derivedPullbackUnitIsoAtModel :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y)) 0).obj
          (_root_.SheafOfModules.unit (structureSheafRing Y))) ≅
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj
        (_root_.SheafOfModules.unit (structureSheafRing X)) :=
  derivedPullbackSingleUnitIsoAtModel f ≪≫
    (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).mapIso
      (modulePullbackObjUnitIso f)

/-- The factorisation of `ν` through the degreewise pullback, in the forward direction. -/
theorem derivedPullbackUnitIsoAtModel_hom :
    (derivedPullbackUnitIsoAtModel f).hom =
      (derivedPullbackSingleUnitIsoAtModel f).hom ≫
        (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).map
          (modulePullbackObjUnitIso f).hom :=
  rfl

/-- **`ν` on representatives is the degree-zero comparison `f^*𝒪_Y ≅ 𝒪_X`.** Read through the
identification of `Lf^*(𝒪_Y[0])` with `(f^*𝒪_Y)[0]`, the unit comparison of the derived
pullback is the image under `(-)[0]` of the ordinary unit comparison of [Stacks, Tag 01CD];
in particular it adds no data to it. -/
theorem derivedPullbackSingleUnitIsoAtModel_inv_comp_derivedPullbackUnitIsoAtModel_hom :
    (derivedPullbackSingleUnitIsoAtModel f).inv ≫ (derivedPullbackUnitIsoAtModel f).hom =
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).map
        (modulePullbackObjUnitIso f).hom := by
  rw [derivedPullbackUnitIsoAtModel_hom, Iso.inv_hom_id_assoc]

end Stacks.Cohomology.DerivedPullbackUnit

end
