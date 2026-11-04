module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessEtaleChart

/-!
# Finite type descends from one étale scheme chart

Let `X` be an algebraic space over a scheme `S` of a big fppf site and let `M` be a
quasi-coherent `𝒪_X`-module.  `AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite`
reads finite type of `M` on each étale scheme chart; this file proves the *converse* at a
surjective chart: if the restriction of `M` to the Zariski site of one surjective étale scheme
chart is of finite type, then `M` is of finite type on the small étale site of `X`.

This is the étale-locality of finite type that Stacks 084Q appeals to — Properties of Spaces,
Section 66.30 — in the direction this development did not have.

## Main results

Both results are in the namespace `AlgebraicGeometry.Space`.

* `isFiniteTypeOnSite_chartSmallEtaleRestriction_of_isFiniteType_chartSchemeModule`:
  finite type of the chart restriction read on the chart's *scheme* gives finite type of the
  chart restriction read on the chart's small étale site.
* `isFiniteTypeOnSite_of_isFiniteType_chartSchemeModule_of_isSurjective`:
  **finite type descends from one surjective étale scheme chart.**

## Implementation notes

The three steps are each proved elsewhere, and the content of this file is only that they
compose.

1. From the Zariski site of the chart's scheme to the small étale site of the chart space.  The
   chart space is the Yoneda algebraic space of the chart's object, definitionally
   (`AlgebraicGeometry.Space.chartSpace_eq_yoneda`), so
   `AlgebraicGeometry.Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence` applies
   to it.  `AlgebraicGeometry.Space.chartSchemeModule` is by construction the image of
   `AlgebraicGeometry.Space.chartSmallEtaleQcoh` under the *inverse* of
   `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, so the counit of that
   equivalence identifies the module the first step produces with
   `AlgebraicGeometry.Space.chartSmallEtaleRestriction`; finite type is carried across it by
   `Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso`.
2. From the small étale site of the chart space to the slice of the small étale site of `X` at
   the chart, which is `AlgebraicGeometry.Space.isFiniteTypeOnSite_chartSmallEtaleRestriction_iff`
   — Stacks 03DM for clause (5) of Stacks 03DL at the comparison of Stacks 04M0.  This is the
   step that was missing, and it is why a reflecting direction for the reindexing of finite type
   had to be proved.
3. From the slice at a surjective chart to the whole small étale site, which is
   `AlgebraicGeometry.Space.isFiniteTypeOnSite_iff_over_of_isSurjective`, the clause of
   Stacks 03DN for finite type applied to the one-member covering family of a surjective chart.

Quasi-coherence of `M` is a hypothesis throughout because `chartSchemeModule` is only defined for
a quasi-coherent module: the passage to the Zariski site of the chart's scheme is an equivalence
of *quasi-coherent* categories, Descent, Proposition 03DX (2) at `τ = étale`.  No hypothesis
beyond quasi-coherence and the finiteness on the one chart is needed, and in particular nothing
is assumed about `X` beyond being an algebraic space.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- **Finite type of the chart restriction on the chart's scheme gives finite type of the chart
restriction on the chart's small étale site.**

The chart space is the Yoneda algebraic space of the chart's object definitionally, so
`AlgebraicGeometry.Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence` applies;
and `AlgebraicGeometry.Space.chartSchemeModule` is the image of
`AlgebraicGeometry.Space.chartSmallEtaleQcoh` under the inverse of that equivalence, so the
counit identifies the two. -/
theorem isFiniteTypeOnSite_chartSmallEtaleRestriction_of_isFiniteType_chartSchemeModule
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (hft : SheafOfModules.IsFiniteType (chartSchemeModule B S hS X M hM V)) :
    (chartSmallEtaleRestriction B S hS X M V).IsFiniteTypeOnSite :=
  Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso
    ((ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS
          ((SmallEtale.toOver B S hS X.1).obj V)).counitIso.app
        (chartSmallEtaleQcoh B S hS X M hM V)))
    (isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B S hS
      ((SmallEtale.toOver B S hS X.1).obj V)
      (chartSchemeModule B S hS X M hM V)
      (isQuasicoherent_chartSchemeModule B S hS X M hM V) hft)

/-- **Finite type descends from one surjective étale scheme chart.**  A quasi-coherent
`𝒪_X`-module whose restriction to the Zariski site of one étale scheme chart with surjective
structure morphism is of finite type is of finite type on the small étale site of `X`.

This is the converse of `AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite` read
at one surjective chart, and the étale-locality of finite type that Stacks 084Q appeals to. -/
theorem isFiniteTypeOnSite_of_isFiniteType_chartSchemeModule_of_isSurjective
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1)
    (hsurj : IsSurjective B S hS V.1.hom)
    (hft : SheafOfModules.IsFiniteType (chartSchemeModule B S hS X M hM V)) :
    SheafOfModules.IsFiniteTypeOnSite M :=
  (isFiniteTypeOnSite_iff_over_of_isSurjective B S hS X.1 X.2 M V hsurj).2
    ((isFiniteTypeOnSite_chartSmallEtaleRestriction_iff B S hS X M V).1
      (isFiniteTypeOnSite_chartSmallEtaleRestriction_of_isFiniteType_chartSchemeModule
        B S hS X M hM V hft))

end AlgebraicGeometry.Space

end
