module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartPointLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheaves
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# Finite local freeness from étale restrictions to a covering family of charts

Let `Y` be an algebraic space and `(Vᵢ ⟶ Y)` a family of étale scheme charts covering `Y`. An
`𝒪_Y`-module is finite locally free (Stacks 03DL, part (2)) as soon as each of its restrictions
along the structure morphisms `Vᵢ ⟶ Y` is. This is the clause of Stacks 03DN for finite local
freeness, read along the charts `Vᵢ ⟶ Y` rather than on the slices of the small étale site of `Y`.

## Main results

* `isFiniteLocallyFreeOnSite_of_coversTop_etaleModulePullback`: a module whose restrictions along a
  covering family of étale charts are finite locally free is finite locally free.
* `isFiniteLocallyFreeOfRank_of_coversTop_etaleModulePullback`: the same for the rank condition of
  Stacks 0409.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Surjective étale charts of the charts `Vᵢ` of a covering family push forward to a covering
family of `Y`. -/
private theorem exists_coversTop_postcomp_surjective_charts {Y : AlgebraicSpaces B S hS}
    {ι : Type (u + 1)} {V : ι → SmallEtale B S hS Y.1}
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V) :
    ∃ T : ∀ i, SmallEtale B S hS (chartSpace B S hS Y (V i)).1,
      (SmallEtale.topology B S hS Y.1).CoversTop fun i =>
        (smallEtaleRingedSitePostcomp B S hS (chartToSpace B S hS Y (V i))
          (isEtale_chartToSpace B S hS Y (V i))).obj (T i) := by
  choose T hT using fun i => exists_surjective_smallEtale_chart B S hS (chartSpace B S hS Y (V i)).1
    (chartSpace B S hS Y (V i)).2
  refine ⟨T, SmallEtale.coversTop_of_forall_mem_range B S hS fun x => ?_⟩
  obtain ⟨i, y, rfl⟩ := SmallEtale.exists_mem_range_of_coversTop B S hS Y.2 hV x
  obtain ⟨z, rfl⟩ := hT i y
  exact ⟨i, z, pointsMap_comp_apply B S hS (T i).1.hom (V i).1.hom z⟩

/-- **Finite local freeness is local along a covering family of étale charts.** If the
restriction of an `𝒪_Y`-module along the structure morphism of each member of a family of étale
scheme charts covering `Y` is finite locally free, the module is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_of_coversTop_etaleModulePullback {Y : AlgebraicSpaces B S hS}
    {ι : Type (u + 1)} {V : ι → SmallEtale B S hS Y.1}
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (h : ∀ i, SheafOfModules.IsFiniteLocallyFreeOnSite
      ((etaleModulePullback B S hS (chartToSpace B S hS Y (V i))
        (isEtale_chartToSpace B S hS Y (V i))).obj M)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite M := by
  obtain ⟨T, hU⟩ := exists_coversTop_postcomp_surjective_charts hV
  let U : ι → (smallEtaleRingedSite B S hS Y.1 Y.2).C := fun i =>
    (smallEtaleRingedSitePostcomp B S hS (chartToSpace B S hS Y (V i))
      (isEtale_chartToSpace B S hS Y (V i))).obj (T i)
  refine (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite
    (smallEtaleRingedSite B S hS Y.1 Y.2) M).2 ⟨ι, U, ?_, fun i => ?_⟩
  · exact hU
  · exact (isFiniteLocallyFreeOnSite_over_etaleModulePullback_iff B S hS
      (chartToSpace B S hS Y (V i)) (isEtale_chartToSpace B S hS Y (V i)) M (T i)).1
      ((h i).over (T i))

/-- **The rank is local along a covering family of étale charts.** If the restriction of an
`𝒪_Y`-module along the structure morphism of each member of a family of étale scheme charts
covering `Y` is finite locally free of rank `r` (Stacks 0409), the module is. -/
theorem isFiniteLocallyFreeOfRank_of_coversTop_etaleModulePullback {Y : AlgebraicSpaces B S hS}
    {ι : Type (u + 1)} {V : ι → SmallEtale B S hS Y.1}
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (r : ℕ)
    (h : ∀ i, RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite B S hS (chartSpace B S hS Y (V i)).1 (chartSpace B S hS Y (V i)).2)
      ((etaleModulePullback B S hS (chartToSpace B S hS Y (V i))
        (isEtale_chartToSpace B S hS Y (V i))).obj M) r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) M r := by
  obtain ⟨T, hU⟩ := exists_coversTop_postcomp_surjective_charts hV
  let U : ι → (smallEtaleRingedSite B S hS Y.1 Y.2).C := fun i =>
    (smallEtaleRingedSitePostcomp B S hS (chartToSpace B S hS Y (V i))
      (isEtale_chartToSpace B S hS Y (V i))).obj (T i)
  refine (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover _ M r).2 ⟨ι, U, ?_, fun i => ?_⟩
  · exact hU
  · exact (isFiniteLocallyFreeOfRank_over_etaleModulePullback_iff B S hS
      (chartToSpace B S hS Y (V i)) (isEtale_chartToSpace B S hS Y (V i)) M (T i) r).1
      (RingedSite.IsFiniteLocallyFreeOfRank.over _ _ (h i) (T i))

end AlgebraicGeometry.Space

end
