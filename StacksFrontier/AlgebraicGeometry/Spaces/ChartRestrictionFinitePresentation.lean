module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationSiteEquivalence

/-!
# Finite presentation on an étale chart, through the comparison of Stacks 04M0

`AlgebraicGeometry.Space.chartSmallEtaleRestriction` reads the restriction `M|_U` of an
`𝒪_X`-module to an étale scheme chart `U` of an algebraic space `X` as a module on the small étale
site of the chart, through the comparison equivalence of Stacks 04M0. Finite presentation
(Modules on Sites, Definition 03DL (7)) is invariant under that comparison.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_chartSmallEtaleRestriction_iff`: **finite
  presentation is invariant under the comparison of Stacks 04M0.**

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- **Finite presentation is invariant under the comparison of Stacks 04M0.** The restriction of
an `𝒪_X`-module to an étale scheme chart, read on the small étale site of the chart, is of finite
presentation exactly when the restriction to the slice of the small étale site of `X` is. -/
theorem isFinitePresentation_chartSmallEtaleRestriction_iff
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (U : SmallEtale B S hS X.1) :
    (chartSmallEtaleRestriction B S hS X M U).IsFinitePresentation ↔
      (M.over U).IsFinitePresentation := by
  let (V : Over U) : HasSheafify (((SmallEtale.topology B S hS X.1).over U).over V)
      AddCommGrpCat.{u} := AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let (V : SmallEtale B S hS (chartSpace B S hS X U).1) :
      HasSheafify ((SmallEtale.topology B S hS (chartSpace B S hS X U).1).over V)
        AddCommGrpCat.{u} := AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  exact (@Stacks.SheafOfModules.isFinitePresentation_reindex_iff _ _ _ _
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    inferInstance
    ((structureRingSheaf B S hS X).over U)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U)
    (isDenseSubsite_chartLocalization_chartSpace B S hS X U)
    (M.over U)).symm

end AlgebraicGeometry.Space

end
