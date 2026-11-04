module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreePushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent

/-!
# Finite local freeness of a module on an algebraic space, read at an étale scheme chart

Finite local freeness on a site is invariant under the two comparisons of ringed sites that
relate a module on the small étale site of an algebraic space `X` with a Zariski module on the
scheme of an étale chart: the localization of Stacks 04M0 at the chart, and the comparison of
Stacks 03DX (2) between the small étale site of the chart space and that of the chart scheme.

Composed with Stacks 05VG for the clause 03DL (2) at `τ = étale`
(`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule`) this transports
finite local freeness of the Zariski chart module of Stacks 03DX (2) to finite local freeness of
the chart restriction of the module on `X`.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_chartSmallEtaleRestriction_iff` and
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff`: the two
  reindexings, Stacks 03DM for the clause 03DL (2).
* `AlgebraicGeometry.Space.isFiniteFree_representedSmallEtaleModule_iff`: the second of those
  reindexings for *outright* finite freeness, Stacks 03DE (2), which is what the base-change
  clause of Stacks 0CZT consumes at the image point.
* `Space.isFiniteLocallyFreeOnSite_over_of_isFiniteLocallyFree_chartSchemeModule`:
  if the Zariski chart module is finite locally free, the restriction of the module to the slice
  at the chart is finite locally free on the site.

## Implementation notes

The two reindexings are `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff` at the two
equivalences, stated exactly as the quasi-coherence versions
`AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSmallEtaleRestriction_iff` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleModule_iff` are, with the
same instance arguments supplied positionally; what makes them available is that the transported
structure sheaves are the structure sheaves of the targets on the nose
(`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence` and
`AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`, both `rfl`).

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Finite local freeness is invariant under the comparison of Stacks 04M0.**  The restriction
of an `𝒪_X`-module to an étale scheme chart, read on the small étale site of the chart, is finite
locally free exactly when the restriction to the slice of the small étale site of `X` is. -/
@[stacks 03DM "finite locally free, at the localization of 04M0 at a chart"]
theorem isFiniteLocallyFreeOnSite_chartSmallEtaleRestriction_iff (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (U : SmallEtale B S hS X.1) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (chartSmallEtaleRestriction B S hS X M U) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite (M.over U) :=
  @Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff _ _ _ _
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    ((structureRingSheaf B S hS X).over U)
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U)
    (M.over U)

/-- **Finite local freeness is invariant under the comparison equivalence of Stacks 03DX (2) at a
representable algebraic space.** -/
@[stacks 03DM "finite locally free, at the comparison of a representable space with its scheme"]
theorem isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff (U : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (representedSmallEtaleModule B S hS U M) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite M :=
  Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff
    (representedSmallEtaleEquivalence B S hS U) (representedSchemeStructureSheaf B S hS U) M

/-- **Finite freeness is invariant under the comparison equivalence of Stacks 03DX (2) at a
representable algebraic space.**  This is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff` for outright
finite freeness in place of finite local freeness; it is the same reindexing. -/
@[stacks 03DM "finite free, at the comparison of a representable space with its scheme"]
theorem isFiniteFree_representedSmallEtaleModule_iff (U : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    SheafOfModules.IsFiniteFree (representedStructureRingSheaf B S hS U)
        (representedSmallEtaleModule B S hS U M) ↔
      SheafOfModules.IsFiniteFree (representedSchemeStructureSheaf B S hS U) M :=
  Stacks.SheafOfModules.isFiniteFree_reindex_iff
    (representedSmallEtaleEquivalence B S hS U) (representedSchemeStructureSheaf B S hS U) M

/-- The counit of the comparison of Stacks 03DX (2) at an étale chart: the chart restriction of a
quasi-coherent `𝒪_X`-module, read on the small étale site of the chart *space*, is the reading on
the chart space of its restriction to the small étale site of the chart *scheme*. -/
noncomputable def representedSmallEtaleChartSchemeEtaleModuleIso (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (hM : M.IsQuasicoherentOnSite)
    (A : SmallEtale B S hS X.1) :=
  (ObjectProperty.ι _).mapIso
    ((representedQuasicoherentEquivalence B S hS
      ((SmallEtale.toOver B S hS X.1).obj A)).counitIso.app
        (chartSmallEtaleQcoh B S hS X M hM A))

/-- **If the Zariski chart module of Stacks 03DX (2) is finite locally free, the restriction of
the module to the slice at the chart is finite locally free on the site.**

The chain is Stacks 05VG for the clause 03DL (2) at `τ = étale`
(`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule`), then the counit of
03DX (2) at the chart scheme (`AlgebraicGeometry.Space.associatedModuleChartSchemeModuleIso`),
then the two reindexings above. -/
theorem isFiniteLocallyFreeOnSite_over_of_isFiniteLocallyFree_chartSchemeModule
    (X : AlgebraicSpaces B S hS) (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (A : SmallEtale B S hS X.1)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (chartSchemeModule B S hS X M hM A)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (M.over A) := by
  rw [← isFiniteLocallyFreeOnSite_chartSmallEtaleRestriction_iff]
  refine SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X M hM A) ?_
  refine (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS _ _).2 ?_
  exact SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
    (associatedModuleChartSchemeModuleIso B S hS X M hM A)
    (_root_.AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule
      (associatedBigEtaleSite B) (chartScheme A)
      ((SmallEtale.toOver B S hS X.1).obj A).left.property _ h)

end AlgebraicGeometry.Space

end
