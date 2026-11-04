module

public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDerivedSectionsTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction

/-!
# Sections cross the chart transport of an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `U` be an étale scheme chart of `X`.  The
chart transport of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean` carries an
`𝒪_X`-module to a module on the small étale site of the *scheme* `chartScheme U` in three steps:
restriction to the slice `X_étale/U`, the reindexing of Stacks 04M0, and the reindexing along the
comparison of the representable algebraic space of the chart with its scheme.  This file computes
the **sections** of the result: at an object `Z` of the small étale site of the chart's scheme
they are the sections of the original module over an étale chart of `X`, namely the one that the
two comparison equivalences attach to `Z`.

At a Zariski open `W` of the chart's scheme, taken into the small étale site by
`AlgebraicGeometry.SmallEtale.opensObj`, that chart is
`AlgebraicGeometry.Space.openChartOfComparison B S hS X U W` on the nose, and
`AlgebraicGeometry.Space.openChartOfComparisonTopIso` identifies it at `W = ⊤` with `U` itself,
up to isomorphism of charts.

## Main results

* `AlgebraicGeometry.Space.sections_representedSchemeReindex_eq` and
  `AlgebraicGeometry.Space.sections_chartLocalizationReindex_eq`: each reindexing crossed on its
  own, as an **equality** of functors into one category of modules.
* `AlgebraicGeometry.Space.sections_chartSchemeReindex_eq`: the two reindexings crossed together.
* `AlgebraicGeometry.Space.chartTransportSectionsIso`: the slice crossed as well — the whole
  chart transport followed by sections at `Z` is sections of the `𝒪_X`-module over the étale
  chart that the transport names.

## How the composite is reached, and why that matters

Each of the three crossings is `rfl`, and so is their composite; but asserting the composite
directly does not fit the heartbeat ceiling, and the reason is recorded with measurements in the
module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsTransport.lean`: the two sides of such
an equality have `CategoryTheory.Functor.comp` and `SheafOfModules.evaluation` as their heads,
so the unifier cannot use congruence and reduces both sides to structure literals through the
concrete site terms.

What is done here instead is to cross one step at a time and to compose the *equalities*, never
the two spellings: each step's statement has the composite on the left and a single `evaluation`
on the right, and the next step is reached by `congrArg` under the remaining functor, where the
two sides again share a head and congruence applies.  So the only equality the unifier ever has
to decide is one crossing at a time, and each of those is cheap.  Nothing below raises the
heartbeat ceiling.

Two further points matter.

*The chart has to stay spelled as the composite.*  The expensive identification is not the
crossing but the replacement of `e₁.functor.obj (e₂.inverse.obj Z)` by a chart named some other
way; that is why the statements below leave the chart in the form the comparisons produce, which
is also the form `AlgebraicGeometry.Space.openChartOfComparison` is defined in.

*The chart `U` is passed at the `AlgebraicGeometry.Space.SmallEtale` spelling*, and the localized
sheaf of rings is therefore written `((smallEtaleRingedSite B S hS X.1 X.2).over U).ringSheaf`
and not `(smallEtaleRingedSite B S hS X.1 X.2).ringSheaf.over U`.  At this spelling of `U` the
second form is not writable at all: its `CategoryTheory.Over U` has its object universe already
fixed, so `Category (Over U)` asks instance search for `max (u + 1) ?w =?= u + 1`, which has no
solution, while the first form takes the category from
`AlgebraicGeometry.RingedSite.category`.  The two sheaves of rings are definitionally equal, and
`chartTransportSectionsIso` crosses between them at its last step, the identification of
sections of the restriction to the slice at `V` with sections at `V.left`, which holds by
`Iso.refl`.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and
-- `Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck` are removed as instances for this
-- file, for the reason recorded in the implementation notes of
-- `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean`: they answer
-- `Abelian (SheafOfModules …)` and `IsGrothendieckAbelian (SheafOfModules …)` with the module
-- universe fixed to the join of the universes of the site and the rings, and a search reaching
-- one of them first ends in a universe constraint with no solution rather than in a recoverable
-- failure.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

section ChartTransport

attribute [local instance] isGrothendieckAbelian_modules
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  hasSheafify_chartLocalization wEqualsLocallyBijective_chartLocalization
  abelian_chartLocalizationModules abelian_chartModules
  additive_chartLocalizationReindex additive_representedSchemeReindex

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)

/-- **Sections cross the comparison of a representable algebraic space with its scheme.**  For
an object `Z` of the small étale site of the scheme underlying `V`, the sections at `Z` of the
reindexing of an `𝒪`-module on the small étale site of the algebraic space represented by `V`
are its sections at the corresponding object of that site.

The reindexing is `SheafOfModules.pushforward` along the inverse of the comparison, with the
identity structure map, so this is an equality and not merely an isomorphism. -/
theorem sections_representedSchemeReindex_eq (V : BigFppfOver B S hS)
    (Z : (representedSchemeRingedSite B S hS V).C) :
    representedSchemeReindex B S hS V ⋙
        SheafOfModules.evaluation.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS V).O) (op Z) =
      SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (representedRingedSite B S hS V).O)
        (op ((representedSmallEtaleEquivalence B S hS V).inverse.obj Z)) := rfl

/-- **Sections cross the reindexing of Stacks 04M0.**  For an object `W` of the small étale site
of the algebraic space represented by a chart `U`, the sections at `W` of the reindexing of an
`𝒪_X|_U`-module on the localization `X_étale/U` are its sections at the object of the slice that
the comparison of Stacks 04M0 attaches to `W`.

As for the other reindexing this is an equality: the reindexing is `SheafOfModules.pushforward`
along the comparison with the identity structure map. -/
theorem sections_chartLocalizationReindex_eq (W : (chartRingedSite B S hS X U).C) :
    chartLocalizationReindex B S hS X U ⋙
        SheafOfModules.evaluation.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O) (op W) =
      SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)
        (op ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.obj W)) := rfl

/-- **Sections cross both represented-space comparisons at once.**  For an object `Z` of the
small étale site of the chart's scheme, the sections at `Z` of the two reindexings applied to an
`𝒪_X|_U`-module on the localization `X_étale/U` are its sections at the object of the slice that
the two comparisons attach to `Z`.

The two crossings meet because the chart space *is* the Yoneda algebraic space of the chart's
object, `AlgebraicGeometry.Space.chartRingedSite_eq_representedRingedSite`.  The composite is
reached by rewriting the inner crossing under the outer reindexing, and not asserted as one
`rfl`; see "How the composite is reached, and why that matters" in the module documentation. -/
theorem sections_chartSchemeReindex_eq (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    chartLocalizationReindex B S hS X U ⋙
        (representedSchemeReindex B S hS ((SmallEtale.toOver B S hS X.1).obj U) ⋙
          SheafOfModules.evaluation.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS
              ((SmallEtale.toOver B S hS X.1).obj U)).O)
            (op Z)) =
      SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)
        (op ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.obj
          ((representedSmallEtaleEquivalence B S hS
            ((SmallEtale.toOver B S hS X.1).obj U)).inverse.obj Z))) :=
  (congrArg (fun G => chartLocalizationReindex B S hS X U ⋙ G)
      (sections_representedSchemeReindex_eq B S hS
        ((SmallEtale.toOver B S hS X.1).obj U) Z)).trans
    (sections_chartLocalizationReindex_eq B S hS X U _)

/-- **Sections cross the whole chart transport.**  Restricting an `𝒪_X`-module to the slice at an
étale scheme chart `U`, reindexing along the comparison of Stacks 04M0 and then along the
comparison of the represented algebraic space with its scheme, and taking sections at an object
`Z` of the small étale site of that scheme, gives the sections of the original module over the
étale chart of `X` that the two comparisons attach to `Z`.

At `Z = AlgebraicGeometry.SmallEtale.opensObj … W` for a Zariski open `W` of the chart's scheme
the chart on the right is `AlgebraicGeometry.Space.openChartOfComparison B S hS X U W`, and
`AlgebraicGeometry.Space.openChartOfComparisonTopIso` identifies it at `W = ⊤` with `U`.

This is the underived input that
`Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes` consumes at
`F = SheafOfModules.overFunctor 𝒪_X U`, whose hypothesis is
`AlgebraicGeometry.Space.computesSecond_overFunctor` for an arbitrary additive functor out of
the modules on the slice. -/
def chartTransportSectionsIso (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U ⋙
        (chartLocalizationReindex B S hS X U ⋙
          (representedSchemeReindex B S hS ((SmallEtale.toOver B S hS X.1).obj U) ⋙
            SheafOfModules.evaluation.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS
                ((SmallEtale.toOver B S hS X.1).obj U)).O) (op Z))) ≅
      SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        (op ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.obj
          ((representedSmallEtaleEquivalence B S hS
            ((SmallEtale.toOver B S hS X.1).obj U)).inverse.obj Z)).left) :=
  eqToIso (congrArg (fun G => SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U ⋙ G)
      (sections_chartSchemeReindex_eq B S hS X U Z)) ≪≫
    (Iso.refl _ : SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U ⋙
        SheafOfModules.evaluation.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)
          (op ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.obj
            ((representedSmallEtaleEquivalence B S hS
              ((SmallEtale.toOver B S hS X.1).obj U)).inverse.obj Z))) ≅
      SheafOfModules.evaluation.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        (op ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.obj
          ((representedSmallEtaleEquivalence B S hS
            ((SmallEtale.toOver B S hS X.1).obj U)).inverse.obj Z)).left))

end ChartTransport

end AlgebraicGeometry.Space

end
