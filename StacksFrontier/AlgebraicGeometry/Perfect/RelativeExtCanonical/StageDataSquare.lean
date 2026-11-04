module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.BaseChangeUnits
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.PerfectStageBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.QCohDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaGeneralBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCohCoproducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.RetractOfAPerfectObject
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# The perfect stages base change along a cartesian square of schemes

For a cartesian square `U' → U` over `S' → S` of schemes with `U → S` quasi-compact and
quasi-separated, and `𝒢^•` a bounded complex of quasi-coherent modules flat over `S`, every perfect
`P` on `U` with `K(P) = Rg_*(P^∨ ⊗^L 𝒢)` perfect satisfies the hypotheses
`Stacks.Cohomology.RelativeExtCanonical.StageData` of the base change of the perfect stage, for
the base-change map of [Stacks, Tag 0A1D] and the class `D_QCoh(𝒪_{S'})`.

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.stageData_of_isPullback`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] hasSheafifyOpensSpace wEqualsLocallyBijectiveOpensSpace

variable {U S S' U' : Scheme.{u}} {g : U ⟶ S} {gS : S' ⟶ S} {g' : U' ⟶ S'} {h : U' ⟶ U}
  (hsq : IsPullback h g' g gS) [QuasiCompact g] [QuasiSeparated g]
  {G : CochainComplex (SheafOfModules.{u} (structureSheafRing U.toRingedSpace)) ℤ}
  (hG : IsBoundedFlatOver g.toLRSHom.toShHom G) (hGq : ∀ i : ℤ, (G.X i).IsQuasicoherent)

/-- The derived dual of a perfect object of `D(𝒪_X)` has quasi-coherent cohomology sheaves. -/
private theorem isDQCoh_derivedDual_of_isPerfectStd (X : Scheme.{u})
    (E : StdDerivedModules X.sheaf) (hE : IsPerfectStd E) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing X.toRingedSpace)
      (Stacks.SheafOfModules.derivedDual X.sheaf E) :=
  fun i ↦ PerfectApproximation.isQuasicoherent_homology_of_isPerfect X _
    (@Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite X.toRingedSpace
      (HasDerivedCategory.standard _) _
      (Stacks.SheafOfModules.isPerfect_derivedDual X.sheaf _ hE)) i

include hsq hG hGq in
/-- **The perfect stages base change**: the hypotheses `StageData` hold at every perfect `P` with
`K(P)` perfect, for the base-change map of [Stacks, Tag 0A1D]. -/
theorem stageData_of_isPullback (P : StdDerivedModules U.sheaf) (hP : IsPerfectStd P)
    (hK : IsPerfectStd (stageK g.toLRSHom.toShHom (G := G) P)) :
    StageData g.toLRSHom.toShHom gS.toLRSHom.toShHom g'.toLRSHom.toShHom h.toLRSHom.toShHom
      (squareBaseChangeMap hsq G) (qcohDerived S') P := by
  have : QuasiCompact g' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance
  have : QuasiSeparated g' :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) hsq inferInstance
  have hP' := isPerfectStd_stdPullback h P hP
  have hgK := isPerfectStd_stdPullback gS _ hK
  have hbc := isIso_squareBaseChangeMap hsq hG hGq P hP
  have hK' := isPerfectStd_stageK_of_baseChange g.toLRSHom.toShHom gS.toLRSHom.toShHom
    g'.toLRSHom.toShHom h.toLRSHom.toShHom (squareBaseChangeMap hsq G) P hP hP' hgK
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing U'.toRingedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S'.toRingedSpace))
  let := HasDerivedCategory.standard (SheafOfModules.{u} U'.ringCatSheaf)
  let := HasDerivedCategory.standard (SheafOfModules.{u} S'.ringCatSheaf)
  have hK₀ : ∀ j : ℤ, (((pullbackComplex h.toLRSHom.toShHom).obj G).X j).IsQuasicoherent :=
    fun j ↦
      have := hGq j
      AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent h.toLRSHom.toShHom (G.X j)
  have hQG : Stacks.DerivedQCoh.IsDQCoh (R := structureSheafRing U'.toRingedSpace)
      (DerivedCategory.Q.obj ((pullbackComplex h.toLRSHom.toShHom).obj G)) := fun n ↦
    (SheafOfModules.isQuasicoherent U'.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (structureSheafRing U'.toRingedSpace)) n).app _).symm
      ((SheafOfModules.isQuasicoherent U'.ringCatSheaf).prop_of_isColimit_cokernelCofork
        (HomologicalComplex.homologyIsCokernel _ ((ComplexShape.up ℤ).prev n) n rfl) (hK₀ _)
        ((SheafOfModules.isQuasicoherent U'.ringCatSheaf).prop_of_isLimit_kernelFork
          (HomologicalComplex.cyclesIsKernel _ n ((ComplexShape.up ℤ).next n) rfl) (hK₀ n)
            (hK₀ _)))
  have hD := isDQCoh_derivedDual_of_isPerfectStd U' _ hP'
  have hL : qcohDerived S'
      (stageL g'.toLRSHom.toShHom (G := (pullbackComplex h.toLRSHom.toShHom).obj G)
        ((stdPullback h.toLRSHom.toShHom).obj P)) :=
    isDQCoh_derivedDual_of_isPerfectStd S' _ hK'
  refine ⟨hP, hP', hK, hgK, hK', hbc, fun N hN ↦ ?_, hL⟩
  exact Stacks.Cohomology.ProjectionFormulaGeneralBase.isIso_projectionFormulaMap_of_isQuasicoherent
    g' _ (Stacks.Cohomology.ProjectionFormulaQCohCoproducts.isDQCoh_derivedTensor_obj U' _ _ hD hQG)
    N hN

end Stacks.Cohomology.RelativeExtCanonical

end
