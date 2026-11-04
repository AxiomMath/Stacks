module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme

/-!
# The rank of a module on an algebraic space, read at an étale scheme chart

Let `X` be an algebraic space and `M` a quasi-coherent `𝒪_X`-module. If the Zariski chart module of
Stacks 03DX (2) at an étale scheme chart `A` of `X` is finite locally free of rank `r` in the sense
of the rank clause of Stacks 0409, then so is the restriction of `M` to the slice of the small
étale site of `X` at `A`.

## Main results

* `isFiniteLocallyFreeOfRank_chartSmallEtaleRestriction_iff` and
  `isFiniteLocallyFreeOfRank_representedSmallEtaleModule_iff`: the rank clause of Stacks 0409 is
  invariant under the comparison equivalences of Stacks 04M0 at a chart and of Stacks 03DX (2) at a
  representable algebraic space (Stacks 03DM).
* `isFiniteLocallyFreeOfRank_over_of_isFiniteLocallyFreeOfRank_chartSchemeModule`: if the Zariski
  chart module has rank `r`, the restriction of the module to the slice at the chart has rank `r`.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The rank clause of Stacks 0409 is invariant under the comparison of Stacks 04M0.**  The
restriction of an `𝒪_X`-module to an étale scheme chart, read on the small étale site of the
chart, has rank `r` exactly when the restriction to the slice of the small étale site of `X`
has. -/
@[stacks 03DM "the rank clause of 0409, at the localization of 04M0 at a chart"]
theorem isFiniteLocallyFreeOfRank_chartSmallEtaleRestriction_iff (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (U : SmallEtale B S hS X.1) (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite B S hS (chartSpace B S hS X U).1 (chartSpace B S hS X U).2)
        (chartSmallEtaleRestriction B S hS X M U) r ↔
      RingedSite.IsFiniteLocallyFreeOfRank ((smallEtaleRingedSite B S hS X.1 X.2).over U)
        (M.over U) r := by
  have h₁ : (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).J :=
    isContinuous_chartLocalization_chartSpace B S hS X U
  have h₃ : (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).inverse.IsDenseSubsite
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).J
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1) :=
    isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U
  have h₂ : (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).inverse.IsContinuous
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).J
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1) :=
    @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _ h₃
  exact @RingedSite.isFiniteLocallyFreeOfRank_reindex_iff
    ((smallEtaleRingedSite B S hS X.1 X.2).over U) _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U) h₁ h₂ h₃ (M.over U) r

/-- **The rank clause of Stacks 0409 is invariant under the comparison equivalence of
Stacks 03DX (2) at a representable algebraic space.** -/
@[stacks 03DM "the rank clause of 0409, at the represented-space comparison of 03DX (2)"]
theorem isFiniteLocallyFreeOfRank_representedSmallEtaleModule_iff (U : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) (r : ℕ) :
    RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        (representedSmallEtaleModule B S hS U M) r ↔
      RingedSite.IsFiniteLocallyFreeOfRank
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) M r :=
  RingedSite.isFiniteLocallyFreeOfRank_reindex_iff
    (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U) M r

/-- **If the Zariski chart module of Stacks 03DX (2) has rank `r`, the restriction of the module
to the slice at the chart has rank `r` on the site.** -/
theorem isFiniteLocallyFreeOfRank_over_of_isFiniteLocallyFreeOfRank_chartSchemeModule
    (X : AlgebraicSpaces B S hS) (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1) (r : ℕ)
    (h : RingedSite.IsFiniteLocallyFreeOfRank (chartScheme A).zariskiRingedSite
      (chartSchemeModule B S hS X M hM A) r) :
    RingedSite.IsFiniteLocallyFreeOfRank ((smallEtaleRingedSite B S hS X.1 X.2).over A)
      (M.over A) r := by
  rw [← isFiniteLocallyFreeOfRank_chartSmallEtaleRestriction_iff]
  refine RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
    (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X M hM A) ?_
  refine (isFiniteLocallyFreeOfRank_representedSmallEtaleModule_iff B S hS _ _ r).2 ?_
  exact RingedSite.IsFiniteLocallyFreeOfRank.of_iso _ _
    (associatedModuleChartSchemeModuleIso B S hS X M hM A)
    (_root_.AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOfRank_associatedModule
      (associatedBigEtaleSite B) (chartScheme A)
      ((SmallEtale.toOver B S hS X.1).obj A).left.property _ r h)

end AlgebraicGeometry.Space

end
