module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpaceGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison

/-!
# Quasi-coherence on a slice from the pullback to the chart space, at a free module universe

Let `W` be an étale scheme chart of an algebraic space `X` and `M` a sheaf of `𝒪_X`-modules on the
small étale site of `X`, with sections in an arbitrary universe `m`. If the pullback of `M` along
the structure morphism of `W` (`AlgebraicGeometry.Space.etaleModulePullback`) is quasi-coherent,
then so is the restriction `M|_W` of `M` to the slice `X_étale/W`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_over_of_etaleModulePullback_chartToSpace`:
  quasi-coherence of `M|_W` from quasi-coherence of the pullback of `M` to the chart space of `W`.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- If the pullback of `M` to the chart space of `W` is quasi-coherent, then so is `M|_W`, for a
module with sections in an arbitrary universe. -/
theorem isQuasicoherentOnSite_over_of_etaleModulePullback_chartToSpace
    (M : SheafOfModules.{m} (structureRingSheaf B S hS X)) (W : SmallEtale B S hS X.1)
    (h : ((etaleModulePullback.{u, m} B S hS (chartToSpace B S hS X W)
      (isEtale_chartToSpace B S hS X W)).obj M).IsQuasicoherentOnSite) :
    (M.over W).IsQuasicoherentOnSite := by
  exact @Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex' _ _ _ _
    ((SmallEtale.topology B S hS X.1).over W)
    (SmallEtale.topology B S hS (chartSpace B S hS X W).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 W)
    (isContinuous_chartLocalization_chartSpace B S hS X W) ((structureRingSheaf B S hS X).over W)
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X W) (M.over W)
    (SheafOfModules.IsQuasicoherentOnSite.of_iso ((SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext x; rfl))) h)

end AlgebraicGeometry.Space
