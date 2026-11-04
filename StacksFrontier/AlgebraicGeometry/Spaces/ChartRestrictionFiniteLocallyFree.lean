module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeViaEssSurj
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# The restriction of a finite locally free module to an étale chart is finite locally free

Let `X` be an algebraic space over a scheme `S` and `ℰ` a quasi-coherent `𝒪_X`-module on its
small étale site which is finite locally free in the sense of Stacks 03DL (2): over a covering of
every object of the site it is a finite direct sum of copies of the structure sheaf.  This file
proves that the restriction `ℰ|_V` of `ℰ` to the scheme of an étale chart `V` of `X` is a finite
locally free `𝒪_V`-module in the Zariski sense.

The restriction to the slice of the small étale site at `V` is finite locally free, and so is its
reading on the small étale site of the chart (Stacks 03DM, at the localization of Stacks 04M0);
that reading is, through the comparison of Stacks 03DX (2), the restriction of `ℰ` to the small
étale site of the scheme `V`, and the Zariski restriction of a finite locally free module on the
small étale site of a scheme is finite locally free (the descent half of Stacks 05VG, through
Stacks 05B2).

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFree_restrictToChartScheme`: the chart restriction
  of a quasi-coherent finite locally free module is finite locally free.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart restriction of a quasi-coherent finite locally free `𝒪_X`-module is a finite
locally free module on the scheme of the chart.** -/
theorem isFiniteLocallyFree_restrictToChartScheme (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite M) (A : SmallEtale B S hS X.1) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (restrictToChartScheme B S hS X.1 X.2 M A) := by
  have h₁ : SheafOfModules.IsFiniteLocallyFreeOnSite (M.over A) := hfree.over A
  have h₂ := (isFiniteLocallyFreeOnSite_chartSmallEtaleRestriction_iff B S hS X M A).2 h₁
  have h₃ := SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X M hM A).symm h₂
  have h₄ := (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS _ _).1 h₃
  exact @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso _ _ _
    (restrictToChartSchemeIsoRestrictModule B S hS X M hM A).symm
    (AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_restrictModule_of_isFiniteLocallyFreeOnSite
      (associatedBigEtaleSite B) (chartScheme A) (chartFppfObject B S hS X A).left.property
      (chartSchemeEtaleModule B S hS X M hM A) h₄)

end AlgebraicGeometry.Space

end
