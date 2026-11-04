module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections

/-!
# Finite type of the ideal sheaf of a closed subspace gives finite generation on charts

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `Z ⊆ X` be a closed
subspace with defining ideal sheaf `𝓘 = 𝓘_Z ⊆ 𝒪_X` of Stacks 03MB.  This file proves that if `𝓘`
is of finite type as a module on the small étale site of `X`, then the sheaf of ideals it induces
on any étale scheme chart is of finite type in the sense of
`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`: the ideal over every affine open of the
chart's scheme is finitely generated.

Read at a chart, this is the implication `⟹` of the comparison which
`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart`
carries as the hypothesis `hchart`, and which the source of Stacks 084Q takes from Properties of
Spaces, Section 66.30.

## Main results

* `AlgebraicGeometry.Space.fg_ideal_idealSheafDataOfChart_of_isFiniteTypeOnSite`: **finite type of
  `𝓘` on the small étale site gives finite generation of the chart ideal over every affine open of
  every chart.**
* `AlgebraicGeometry.Space.isFiniteType_idealSheafDataOfChart_of_isFiniteTypeOnSite`: the same
  conclusion packaged as `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`.
* `AlgebraicGeometry.Space.fg_ideal_ker_rep_snd_of_isFiniteTypeOnSite`: the same, with the chart
  ideal spelled as the kernel of pullback of regular functions along the base change
  `Z ×_X A ⟶ A` — the spelling in which Stacks 084Q and the Quot/Hilbert dictionary state it.

## Implementation notes

**Why no hypothesis beyond finite type is needed.**  Quasi-coherence of `𝓘` is the other input of
`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`, and for a *defining* ideal
sheaf it is unconditional: `AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`.  So
is the cartesian-on-affine-charts condition that `AlgebraicGeometry.Space.idealSheafDataOfChart`
needs, by `AlgebraicGeometry.Space.definingIdealSheaf_isCartesianOnAffineCharts`.  Nothing here is
assumed about `Z` or about the chart.

**The one step.**  Over the affine chart `AlgebraicGeometry.Space.openChart` that an affine open
`V` of the chart's scheme cuts out, the sections of `𝓘` form a finite module over the functions on
that chart, by Stacks 03DL(5) in the form
`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`; a finite module is a
finitely generated submodule, and the chart ideal over `V` is that ideal of sections transported
along the ring isomorphism `AlgebraicGeometry.Space.openChartTopRingHom`, under which finite
generation is preserved.  There is no sheafification and no site comparison in the argument.

**What this does *not* give, and what the converse actually needs.**  The reverse implication —
finite generation on the affine opens of one *surjective* chart gives finite type of `𝓘` on the
small étale site — is not here, and it is not the same kind of statement: it has to produce
generating sections that span `𝓘` locally at *every* object of the small étale site, not merely
over the affine charts that come from opens of the given chart.

Two routes to it exist.

* Through the chart comparison of Stacks 04M0.  **The structure-sheaf matching is
  available**, as `AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionQuasicoherent.lean` — an equality, by
  `rfl` — together with
  `AlgebraicGeometry.Space.SmallEtale.ringSheaf_eq_chartLocalization_pushforward` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartEquivalenceClosure.lean`; module transport
  along it is `AlgebraicGeometry.Space.chartSmallEtaleRestriction`, and quasi-coherence, finite
  type, finite presentation and finite local freeness all cross it as equivalences
  (`isQuasicoherentOnSite_chartSmallEtaleRestriction_iff`,
  `isFiniteTypeOnSite_chartSmallEtaleRestriction_iff`,
  `isFinitePresentation_chartSmallEtaleRestriction_iff`,
  `isFiniteLocallyFreeOnSite_chartSmallEtaleRestriction_iff`).  **The reflecting lemma the route
  needs is proved**, as
  `Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_reindex` of
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedFiniteTypeOnCharts.lean`, with
  `hasFiniteGlobalGenerators_of_reindex` and `hasFiniteGlobalGenerators_over_of_reindex` beneath
  it and the equivalence `isFiniteTypeOnSite_reindex_iff` above it; the 04M0 reading is
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_chartSmallEtaleRestriction_iff` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionFiniteType.lean`.  Its companion,
  invariance of finite type under isomorphism, is
  `Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso`, and the descent from a
  surjective chart the two feed is
  `AlgebraicGeometry.Space.isFiniteType_iff_over_of_isSurjective`.

  The whole site-theoretic half of the route is now carried out, in
  `StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeChartSchemeDescent.lean`:
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_of_isFiniteType_chartSchemeModule_of_isSurjective`
  takes finite type of `AlgebraicGeometry.Space.chartSchemeModule` — the chart restriction read
  on the Zariski site of the chart's *scheme* — at one surjective chart, and returns finite type
  on the small étale site of `X`.  That is the converse of
  `AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite` at one chart.

  What the route is short of is therefore a pure sections computation on the chart's scheme, with
  no site theory in it: that the hypothesis — the chart ideal finitely generated over every affine
  open of the chart's scheme — gives `Module.Finite` for the sections of `chartSchemeModule` of
  the defining ideal sheaf over every affine open, which
  `Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections`
  (Stacks 01XZ (4) `⟹` (2)) then turns into the `SheafOfModules.IsFiniteType` the descent
  consumes.  The *forward* direction of exactly that computation is the one this file carries out
  above, through `AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`; what is
  needed is its converse.  The development has two parallel readings of the chart restriction as
  a scheme module — `AlgebraicGeometry.Space.chartSchemeModule`, which the descent is phrased in,
  and `AlgebraicGeometry.Space.restrictToChart`, which
  `AlgebraicGeometry.Space.isFiniteType_restrictToChart` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionFromSite.lean` and this file's sections
  lemmas are phrased in — and **the two are compared**: the comparison is
  `AlgebraicGeometry.Space.restrictToChartIsoChartSchemeModule` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionCoherent.lean`, which this file does not
  import, and finiteness of sections crosses it by
  `Stacks.SheafOfModules.moduleFinite_sections_of_iso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/CoherentChartSchemeRestriction.lean`.

  So the whole converse is a chain of proved steps, and the step that has to be *written* is only
  the last transport below.

  1. `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart` and
     `AlgebraicGeometry.Space.ideal_idealSheafDataOfChart` turn the hypothesis into
     `(AlgebraicGeometry.Space.openChartIdeal … A W).FG`.
  2. `AlgebraicGeometry.Space.map_chartSectionsRingHom_openChartIdeal` of
     `StacksFrontier/AlgebraicGeometry/Spaces/ChartIdealSheafDataComparison.lean`, with
     `Ideal.FG.map`, turns that into `(chartIdeal … (openChart … A W)).FG` — the two rings differ
     by `AlgebraicGeometry.Scheme.Opens.topIso`, which is an isomorphism, and that file carries
     both of its one-sided inverses.
  3. `Module.Finite.iff_fg.mpr` makes it `Module.Finite`, the exact converse of the `.mp` used in
     `AlgebraicGeometry.Space.fg_chartIdeal_definingIdealSheaf_of_isFiniteTypeOnSite` below.
  4. The `ULift.up`-as-surjective-semilinear-map transport of
     `AlgebraicGeometry.Space.moduleFinite_sections_chartRestrictionSheaf`
     (`ChartRestrictionFromSite.lean`) carries that to
     `Module.Finite Γ(chartScheme A, W) Γ(chartRestrictionSheaf … , W)`; this is the one step
     with no existing statement, and it is that proof read backwards.
  5. `Stacks.SheafOfModules.moduleFinite_sections_of_iso` across
     `restrictToChartIsoChartRestrictionSheaf` and `restrictToChartIsoChartSchemeModule` moves it
     to `chartSchemeModule`, and
     `Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections`
     then gives the `SheafOfModules.IsFiniteType` that
     `AlgebraicGeometry.Space.isFiniteTypeOnSite_of_isFiniteType_chartSchemeModule_of_isSurjective`
     consumes.
* Through cartesian affine charts, avoiding the comparison altogether.  Restriction between
  affine charts carries the ideal of sections onto the ideal of sections,
  `AlgebraicGeometry.Space.chartIdeal_map_of_isCartesianOnAffineCharts`, again unconditional for a
  defining ideal sheaf, so the generators over an affine chart generate over every affine chart
  above it.  What has to be built around that is a `SheafOfModules.GeneratingSections` on each
  slice, which is what
  `Stacks.SheafOfModules.isFiniteTypeOnSite_of_locally_finite_generators` consumes.

Neither route is carried out here.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)

/-- **The sections of the defining ideal sheaf of a closed subspace over an affine étale chart
form a finitely generated ideal**, as soon as the ideal sheaf is of finite type on the small
étale site.

Quasi-coherence, the other hypothesis of
`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`, is unconditional for a
defining ideal sheaf. -/
theorem fg_chartIdeal_definingIdealSheaf_of_isFiniteTypeOnSite
    (hft : SheafOfModules.IsFiniteTypeOnSite (definingIdealSheaf B S hS X Z).toSheafOfModules)
    (A : SmallEtale B S hS X.1)
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A)) :
    (chartIdeal B S hS X (definingIdealSheaf B S hS X Z) A).FG :=
  Module.Finite.iff_fg.mp
    (module_finite_sections_of_isFiniteTypeOnSite
      (definingIdealSheaf B S hS X Z).toSheafOfModules
      (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z) hft A hA)

/-- **Finite type of `𝓘_Z` on the small étale site gives finite generation of the chart ideal over
every affine open of every étale scheme chart.**

This is the implication `⟹` of the comparison that
`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart`
carries as `hchart`, for the defining ideal sheaf of a closed subspace and at an arbitrary chart.

The chart ideal over `V` is the ideal of sections of `𝓘_Z` over the affine chart cut out by `V`,
transported along the ring isomorphism of `AlgebraicGeometry.Scheme.Opens.topIso`; the sections
are finitely generated by
`AlgebraicGeometry.Space.fg_chartIdeal_definingIdealSheaf_of_isFiniteTypeOnSite`, and finite
generation survives `Ideal.map`. -/
theorem fg_ideal_idealSheafDataOfChart_of_isFiniteTypeOnSite
    (hft : SheafOfModules.IsFiniteTypeOnSite (definingIdealSheaf B S hS X Z).toSheafOfModules)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).affineOpens) :
    ((idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
      (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) A).ideal V).FG :=
  Ideal.FG.map
    (fg_chartIdeal_definingIdealSheaf_of_isFiniteTypeOnSite B S hS X Z hft
      (openChart B S hS X.1 A V.1) V.2)
    (openChartTopRingHom B S hS X A V.1)

/-- **Finite type of `𝓘_Z` on the small étale site makes the sheaf of ideals it induces on every
étale scheme chart of finite type**, in the sense of
`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`. -/
theorem isFiniteType_idealSheafDataOfChart_of_isFiniteTypeOnSite
    (hft : SheafOfModules.IsFiniteTypeOnSite (definingIdealSheaf B S hS X Z).toSheafOfModules)
    (A : SmallEtale B S hS X.1) :
    (idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
      (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) A).IsFiniteType :=
  fun V => fg_ideal_idealSheafDataOfChart_of_isFiniteTypeOnSite B S hS X Z hft A V

/-- **Finite type of `𝓘_Z` on the small étale site gives finite generation of the ideal cut out by
the base change `Z ×_X A ⟶ A` over every affine open of the chart's scheme.**

This is the previous statement with the chart ideal in the spelling Stacks 084Q uses — the kernel
of pullback of regular functions along the base-changed closed immersion — which the two are
identified in by `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart`.  It is exactly
the implication `⟹` of the hypothesis `hchart` of
`AlgebraicGeometry.Space.isFinitePresentation_iff_isFiniteTypeOnSite_kernelIdealSheaf_of_chart`,
read at the chart `A`. -/
theorem fg_ideal_ker_rep_snd_of_isFiniteTypeOnSite
    (hft : SheafOfModules.IsFiniteTypeOnSite (definingIdealSheaf B S hS X Z).toSheafOfModules)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).affineOpens) :
    (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker.ideal V).FG := by
  rw [ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z A]
  exact fg_ideal_idealSheafDataOfChart_of_isFiniteTypeOnSite B S hS X Z hft A V

end AlgebraicGeometry.Space

end
