module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional

/-!
# The top cohomology of the derived pullback of a single module, at any model

For a morphism of ringed spaces `f : X ⟶ Y` and an `𝒪_Y`-module `M` placed in degree `d`, the
degree-`d` cohomology of `Lf^*(M[-d])` is the ordinary pullback `f^*M`. The file
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/DerivedPullbackTopDegree.lean` proves this at
`CategoryTheory.HasDerivedCategory.standard`; the argument does not depend on the model of the two
derived categories, and this file records it for arbitrary models, which is what the derived
categories of schemes in the duality library (the locally small model) need.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleIsoAnyModel`:
  `H^d(Lf^*(M[-d])) ≅ f^*M`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe w₁ w₂ u

open DerivedCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]

/-- **`H^d(Lf^*(M[-d])) ≅ f^* M`**, at any model of the two derived categories: the canonical
comparison `Lf^*(M[-d]) ⟶ (f^*M)[-d]` of `derivedToOrdinaryPullbackSingle`, on degree-`d`
cohomology, followed by `H^d((f^*M)[-d]) = f^*M`. -/
def homologyDerivedPullbackSingleIsoAnyModel
    (M : SheafOfModules.{u} (structureSheafRing Y)) (d : ℤ) :
    (homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M)) ≅
      (modulePullback f).obj M := by
  let c := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
      ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing Y)) d).hom.app M) ≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategorySingleFunctor (modulePullback f) d).hom.app M) ≫
    (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) d).inv.app
      ((modulePullback f).obj M)
  -- the comparison `Lf^*(Q P) ⟶ Q(f^* P)` is invertible on degree-`d` cohomology for every
  -- complex `P` with zero terms above `d`: a K-flat resolution `F ⟶ P` with zero terms above `d`
  -- reduces it to `H^d(f^* s)`, and `f^*` preserves the cokernel of the last differential
  have key : ∀ (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ),
      P.IsStrictlyLE d →
      IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ)).obj P))) := by
    intro P hP
    obtain ⟨F, s, hF, hFLE, hs⟩ := exists_kFlat_isStrictlyLE_resolution P d hP
    have hcompF :=
      Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f F hF
    have hmap : IsIso (HomologicalComplex.homologyMap
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) d) := by
      have := RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback f
      exact isIso_homologyMap_map_of_isStrictlyLE (modulePullback f) s d hFLE hP
        ((quasiIsoAt_iff_isIso_homologyMap s d).1 (hs.quasiIsoAt d))
    have hψ : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f).map
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ)).map s))) :=
      isIso_homologyFunctor_map_Qh_map_quotient_map_of_isIso_homologyMap
        (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) d hmap
    have hQs : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).map s)) :=
      isIso_Qh_map_quotient_map (C := SheafOfModules.{u} (structureSheafRing Y)) s hs
    have hLs : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
        ((DerivedCategory.Qh ⋙ Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f).map
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ)).map s))) :=
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⋙
        homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).mapIso
          (@asIso _ _ _ _ _ hQs)).isIso_hom
    have nat := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      f).naturality
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).map s)
    have hRHS : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
              (ComplexShape.up ℤ)).obj F) ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f).map
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
              (ComplexShape.up ℤ)).map s))) := by
      rw [Functor.map_comp]
      exact (@asIso _ _ _ _ _
          (((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).mapIso
            (@asIso _ _ _ _ _ hcompF)).isIso_hom) ≪≫ @asIso _ _ _ _ _ hψ).isIso_hom
    rw [← nat, Functor.map_comp] at hRHS
    exact IsIso.of_isIso_comp_left
      ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
        ((DerivedCategory.Qh ⋙ Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f).map
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ)).map s))) _
  have hcomp : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M))) :=
    key ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj M)
      inferInstance
  have hc : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map c) := by
    simp only [c, Functor.map_comp]
    infer_instance
  exact @asIso _ _ _ _ _ hc ≪≫ homologySingleIso ((modulePullback f).obj M) d

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
