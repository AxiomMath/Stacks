module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts

/-!
# Finite type on an étale chart, through the comparison of Stacks 04M0

`AlgebraicGeometry.Space.chartSmallEtaleRestriction` reads the restriction of an `𝒪_X`-module to
an étale scheme chart `U` of an algebraic space `X` as a module on the small étale site of the
chart, through the comparison equivalence of Stacks 04M0.  It is the reindexing of the
restriction `M|_U` to the slice of the small étale site of `X` along that equivalence, the two
structure sheaves agreeing on the nose by
`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence`.

This file is the finite-type companion of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_chartSmallEtaleRestriction_iff` and of
`AlgebraicGeometry.Space.isFinitePresentation_chartSmallEtaleRestriction_iff`: finite type,
Modules on Sites, Definition 03DL (5), is invariant under that comparison.  With it, every one of
the four local conditions of Stacks 03DL that this development reads on a chart — quasi-coherence
(6), finite type (5), finite presentation (7) and finite local freeness — crosses the comparison
as an equivalence.

## Main results

* `AlgebraicGeometry.Space.isFiniteTypeOnSite_chartSmallEtaleRestriction_iff`: **finite type is
  invariant under the comparison of Stacks 04M0.**

## Implementation notes

This is `Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_reindex_iff` at the
equivalence of ringed sites of Stacks 04M0, and it needs exactly the two dense-subsite
hypotheses that the finite-presentation companion needs and for the same reason: the two
directions transport a covering family along the two functors of the equivalence, so each spends
one of them.  They are
`AlgebraicGeometry.Space.isDenseSubsite_chartLocalizationEquivalence_inverse` and
`AlgebraicGeometry.Space.isDenseSubsite_chartLocalization_chartSpace`.

Unlike the finite-presentation companion it needs no sheafification data on the slices of the
slices, because `SheafOfModules.HasFiniteGlobalGenerators` is stated with coproducts and
epimorphisms rather than sheafified free sheaves.

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

/-- **Finite type is invariant under the comparison of Stacks 04M0.**  The restriction of an
`𝒪_X`-module to an étale scheme chart, read on the small étale site of the chart, is of finite
type exactly when the restriction to the slice of the small étale site of `X` is.

This is `Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_reindex_iff` — Modules on
Sites, Lemma 03DM for clause (5) of Stacks 03DL — at the equivalence of ringed sites of
Stacks 04M0. -/
theorem isFiniteTypeOnSite_chartSmallEtaleRestriction_iff
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X)) (U : SmallEtale B S hS X.1) :
    (chartSmallEtaleRestriction B S hS X M U).IsFiniteTypeOnSite ↔
      (M.over U).IsFiniteTypeOnSite :=
  (@Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_reindex_iff _ _ _ _
    ((SmallEtale.topology B S hS X.1).over U)
    (SmallEtale.topology B S hS (chartSpace B S hS X U).1)
    (SmallEtale.chartLocalizationEquivalence B S hS X.1 U)
    (isContinuous_chartLocalization_chartSpace B S hS X U)
    inferInstance
    ((structureRingSheaf B S hS X).over U)
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS X U)
    (isDenseSubsite_chartLocalization_chartSpace B S hS X U)
    (M.over U)).symm

end AlgebraicGeometry.Space

end
