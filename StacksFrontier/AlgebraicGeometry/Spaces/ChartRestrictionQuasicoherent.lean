module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# Quasi-coherence on an étale chart, through the structure sheaves of Stacks 04M0

Stacks 04M0 identifies the small étale site of an étale scheme chart `U` of an algebraic space
`X` with the localization `X_étale/U` of the small étale site of `X`.  This file matches the two
structure sheaves across that equivalence: the direct image of `𝒪_X|_U` along the comparison
functor *is* the structure sheaf of the small étale site of the chart, on the nose.  With the
two ringed sites so identified, Stacks 03DM for clause (6) of Stacks 03DL applies, and
quasi-coherence of an `𝒪_X`-module is equivalent to quasi-coherence of its restriction to the
chart read on the small étale site of the chart.

## Main definitions

* `AlgebraicGeometry.Space.chartStructureRingSheaf` is the structure sheaf of the small étale
  ringed site of an étale chart of an algebraic space, with commutativity forgotten; the
  structure sheaf of the space itself is `AlgebraicGeometry.Space.structureRingSheaf`.
* `AlgebraicGeometry.Space.chartSmallEtaleRestriction` is the restriction of an `𝒪_X`-module to
  an étale chart, read as a module on the small étale site of the chart.

## Main results

* `AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`: **the two structure sheaves
  of Stacks 04M0 agree**, by `rfl`.
* `AlgebraicGeometry.Space.isDenseSubsite_chartLocalizationEquivalence_inverse`: the inverse of
  the comparison equivalence of Stacks 04M0 is a dense subsite inclusion, which is the hypothesis
  under which quasi-coherence is invariant.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSmallEtaleRestriction_iff` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSmallEtaleRestriction`: a module on the
  small étale site of an algebraic space is quasi-coherent exactly when its restriction to an
  étale chart is quasi-coherent on the small étale site of that chart.

## Implementation notes

The structure sheaf of the small étale site of an algebraic space sends a chart to the global
functions on its underlying scheme, and the comparison functor of Stacks 04M0 followed by the
slice projection leaves the underlying object of the big fppf site unchanged
(`AlgebraicGeometry.Space.SmallEtale.chartLocalization_comp_forget_comp_toOver`); the match of
the two structure sheaves is therefore an equality, not merely an isomorphism.  That is what
makes the transport possible at all: `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`
compares a module over the transported sheaf of rings with a module over the sheaf of rings of
the target site, and the invariance of quasi-coherence under restriction of scalars along an
isomorphism of sheaves of rings is not available.

`AlgebraicGeometry.Space.structureRingSheaf` is the structure sheaf typed at
`AlgebraicGeometry.Space.SmallEtale.topology` rather than at the projection
`(AlgebraicGeometry.Space.smallEtaleRingedSite ‹_›).J`, to which it is definitionally equal, and
`AlgebraicGeometry.Space.chartStructureRingSheaf` is typed the same way.
The two readings carry different `CategoryTheory.Category` instance terms on the same category,
and with the ringed-site reading instance search does not find `Category (Over U)` at the
restriction to a slice — the same obstruction that
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` restates its instances for.
An `AlgebraicGeometry.Space.Modules` is accepted everywhere below, the two sheaves of rings
being the same.

The hypothesis of `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` is a dense-subsite
property of the *inverse* of the equivalence, whereas Stacks 04M0 supplies it for the comparison
functor itself (`AlgebraicGeometry.Space.isDenseSubsite_chartLocalization_chartSpace`).  Passing
from one to the other is `CategoryTheory.Equivalence.isDenseSubsite_inverse_of_isCocontinuous`,
whose two cocontinuity hypotheses are, for the functor, the one a dense subsite inclusion
already has, and for the inverse, cover preservation of the functor read through the adjunction
`CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving`.

Both sites have objects in `Type (u + 1)` and morphisms in `Type u`, which is what
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` asks for, its transport of a global
presentation being stated for two sites in the same pair of universes.

No declaration here carries a `stacks` tag: this is an input to Stacks 060Q and 0CTW, not an
assertion of either, and the clause of Stacks 04M0 used is already covered in the tree.

## What this does not give

It does *not* give quasi-coherence of `AlgebraicGeometry.Space.restrictToChartScheme`, which is a
module on the *Zariski* site of the chart's scheme.  Transporting quasi-coherence from the small
étale site of the chart to its Zariski site is the passage from a finer topology to a coarser
one: a global presentation is a colimit computed in sheaves of modules, and sheafification for
the finer topology is the only one of the two comparisons which is a left adjoint, so only the
coarse-to-fine direction is formal (`Stacks.SheafOfModules.isQuasicoherentOnSite_of_le`).  The
direction needed here is Descent, Proposition Stacks 03DX; it also involves a drop of the
presentation index types from `Type (u + 1)` to `Type u`, the small étale site of the chart
having objects one universe above the Zariski site of its scheme.

That transport is carried out elsewhere, by the route the *scheme* case of Stacks 03DX supplies
rather than by any comparison of topologies:
`AlgebraicGeometry.Space.restrictToChartSchemeIsoChartSchemeModule`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionCoherent.lean`) identifies
`AlgebraicGeometry.Space.restrictToChartScheme` with
`AlgebraicGeometry.Space.chartSchemeModule`, which is quasi-coherent, so
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart` holds with no hypothesis beyond
quasi-coherence of the module itself.

## References

* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The comparison functor of Stacks 04M0 is cocontinuous: a dense subsite inclusion is. -/
instance isCocontinuous_chartLocalizationEquivalence_functor (U : SmallEtale B S hS X.1) :
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.IsCocontinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      ((SmallEtale.topology B S hS X.1).over U) :=
  @Functor.IsDenseSubsite.instIsCocontinuous _ _ _ _ _ _ _
    (isDenseSubsite_chartLocalization_chartSpace B S hS X U)

/-- The inverse of the comparison equivalence of Stacks 04M0 is cocontinuous: through the
adjunction it provides, this is cover preservation of the comparison functor. -/
instance isCocontinuous_chartLocalizationEquivalence_inverse (U : SmallEtale B S hS X.1) :
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).inverse.IsCocontinuous
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1) :=
  (Adjunction.isCocontinuous_iff_coverPreserving
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
      (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).symm.toAdjunction).2
    (@Functor.IsDenseSubsite.coverPreserving _ _ _ _ _ _ _
      (isDenseSubsite_chartLocalization_chartSpace B S hS X U))

/-- The inverse of the comparison equivalence of Stacks 04M0 is a dense subsite inclusion of the
localization of the small étale site of `X` at a chart into the small étale site of the chart. -/
instance isDenseSubsite_chartLocalizationEquivalence_inverse (U : SmallEtale B S hS X.1) :
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).inverse.IsDenseSubsite
      ((SmallEtale.topology B S hS X.1).over U)
      (SmallEtale.topology B S hS (chartSpace B S hS X U).1) :=
  @Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1) _ _
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isCocontinuous_chartLocalizationEquivalence_functor B S hS X U)
    (isCocontinuous_chartLocalizationEquivalence_inverse B S hS X U)

/-- The structure sheaf of the small étale site of an étale scheme chart of `X`, with
commutativity forgotten. -/
noncomputable abbrev chartStructureRingSheaf (U : SmallEtale B S hS X.1) :
    Sheaf (SmallEtale.topology B S hS (chartSpace B S hS X U).1) RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
    (chartSpace B S hS X U).1 (chartSpace B S hS X U).2).O)

/-- **The two structure sheaves of Stacks 04M0 agree.**  The direct image along the comparison
functor of the restriction of `𝒪_X` to an étale scheme chart is the structure sheaf of the small
étale site of that chart: the comparison followed by the slice projection leaves the underlying
object of the big fppf site unchanged, and the structure sheaf is the global functions on it. -/
theorem reindexRing_chartLocalizationEquivalence (U : SmallEtale B S hS X.1) :
    @Stacks.SheafOfModules.reindexRing _ _ _ _ _
        (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
        (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
        (isContinuous_chartLocalization_chartSpace B S hS X U)
        ((structureRingSheaf B S hS X).over U) =
      chartStructureRingSheaf B S hS X U := rfl

/-- The restriction of an `𝒪_X`-module to an étale scheme chart `U`, read as a module on the
small étale site of `U` through the comparison equivalence of Stacks 04M0.

This is the identification which Stacks 03M0 invokes as the abuse of notation of its
Equation 03LW; it is available because the two structure sheaves agree, by
`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`. -/
noncomputable def chartSmallEtaleRestriction
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (U : SmallEtale B S hS X.1) :
    SheafOfModules.{u} (chartStructureRingSheaf B S hS X U) :=
  (@SheafOfModules.pushforward _ _ _ _
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor
    (chartStructureRingSheaf B S hS X U)
    ((structureRingSheaf B S hS X).over U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    (𝟙 _)).obj (M.over U)

/-- **Quasi-coherence is invariant under the comparison of Stacks 04M0.**  The restriction of an
`𝒪_X`-module to an étale scheme chart, read on the small étale site of the chart, is
quasi-coherent exactly when the restriction to the slice of the small étale site of `X` is.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` — Stacks 03DM for clause (6)
of Stacks 03DL — at the equivalence of ringed sites of Stacks 04M0. -/
theorem isQuasicoherentOnSite_chartSmallEtaleRestriction_iff
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (U : SmallEtale B S hS X.1) :
    (chartSmallEtaleRestriction B S hS X M U).IsQuasicoherentOnSite ↔
      (M.over U).IsQuasicoherentOnSite :=
  @Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff _ _ _ _
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    ((structureRingSheaf B S hS X).over U)
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U)
    (M.over U)

/-- **A quasi-coherent `𝒪_X`-module restricts to a quasi-coherent module on the small étale site
of every étale scheme chart of `X`.**

Quasi-coherence is stable under restriction to a slice of the site, and the slice at a chart is
the small étale site of the chart as a *ringed* site, by
`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`. -/
theorem isQuasicoherentOnSite_chartSmallEtaleRestriction
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (U : SmallEtale B S hS X.1) :
    (chartSmallEtaleRestriction B S hS X M U).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_chartSmallEtaleRestriction_iff B S hS X M U).2
    (Stacks.SheafOfModules.isQuasicoherent_over M hM U)

end AlgebraicGeometry.Space

end
