module

public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOfSchemes
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.FamilyCriterion.EtaleGenusDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartScheme
public import StacksFrontier.AlgebraicGeometry.ProperQcoh.Basic

/-!
# The genus of a family of curves given by a morphism of schemes

Let `g : T ⟶ U` be a flat proper morphism of finite presentation of schemes of the big fppf site,
with fibres of dimension at most one, and `F` the family of curves it defines
(`AlgebraicGeometry.curveFamilyOfFiberDimensionLE`). The first higher direct image of `F`, on
the small étale site of the algebraic space represented by `U`, is the module associated with the
Zariski higher direct image `R¹g_*𝒪_T` (Stacks 071N, étale clause); so `F` has genus `r` as soon
as `R¹g_*𝒪_T` is finite locally free of rank `r` on the small Zariski site of `U`.

## Main results

* `AlgebraicGeometry.CurveFamily.hasGenus_curveFamilyOfFiberDimensionLE`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **A family of curves given by a morphism of schemes has genus `r` when `R¹g_*𝒪_T` is locally
free of rank `r`** on the small Zariski site of the base. -/
theorem hasGenus_curveFamilyOfFiberDimensionLE {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hfib : ∀ x, topologicalKrullDimAt
      (((BigFppfOver.toScheme B integerBase hZ).map g).fiber
        (((BigFppfOver.toScheme B integerBase hZ).map g) x))
      (((BigFppfOver.toScheme B integerBase hZ).map g).asFiber x) ≤ 1) (r : ℕ)
    (h : RingedSite.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B integerBase hZ).obj U).zariskiRingedSite
      (((Scheme.Modules.pushforward ((BigFppfOver.toScheme B integerBase hZ).map g)).rightDerived
        1).obj (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj T).ringCatSheaf))
      r) :
    HasGenus B hZ (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib) r := by
  refine RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
    (Space.rightDerivedModulePushforwardSchemeSpaceMapStructureSheafModuleIso B integerBase hZ
      g 1).symm ?_
  have := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit
    ((BigFppfOver.toScheme B integerBase hZ).obj T)
  have := Stacks.AlgebraicGeometry.Tag0EX4ProperQcoh.isQuasicoherent_rightDerived_of_isProper
    ((BigFppfOver.toScheme B integerBase hZ).map g)
    (SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj T).ringCatSheaf) 1
  exact (Space.isFiniteLocallyFreeOfRank_representedSmallEtaleModule_iff B integerBase hZ U _ r).2
    ((SmallEtale.isFiniteLocallyFreeOfRank_associatedModule_iff (associatedBigEtaleSite B) _
      U.left.property _ r).2 h)

end AlgebraicGeometry.CurveFamily

end
