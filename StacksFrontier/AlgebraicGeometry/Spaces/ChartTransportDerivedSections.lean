module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartTransportSections

/-!
# Derived sections cross the chart transport of an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `U` be an étale scheme chart of `X`.  The
chart transport of `StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean`
carries an `𝒪_X`-module to a module on the small étale site of the *scheme* `chartScheme U` in
three steps — restriction to the slice `X_étale/U`, the reindexing of Stacks 04M0, and the
reindexing along the comparison of the representable algebraic space of the chart with its
scheme — and
`AlgebraicGeometry.Space.chartTransportSectionsIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportSections.lean`) computes the **sections** of
the result as an equality-up-to-`Iso.refl` of underived functors.

This file passes that computation to the **unbounded right derived functors**: the derived
sections of an `𝒪_X`-module read through the whole chart transport are the derived restriction to
the slice, followed by the two derived reindexings, followed by derived sections at the chosen
object of the small étale site of the chart's scheme.

## Main results

* `AlgebraicGeometry.Space.chartSliceReindex`, `AlgebraicGeometry.Space.chartSchemeSections` and
  `AlgebraicGeometry.Space.chartTransportSections`: the three underived functors of the transport,
  named at the spellings of the localized sheaf of rings at which their instances resolve.
* `AlgebraicGeometry.Space.derivedChartTransportSectionsIso`: the derived restriction to the slice
  followed by the derived sections functor of the transport is the unbounded right derived functor
  of the composite.  This is the one new mathematical step: it is
  `Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes` at the whole transport at once.
* `AlgebraicGeometry.Space.derivedChartTransportSectionsSplitIso`: the derived sections functor of
  the transport splits off the derived reindexing of Stacks 04M0.
* `AlgebraicGeometry.Space.derivedChartTransportIso`: the two composed with
  `AlgebraicGeometry.Space.derivedSectionsRepresentedSchemeReindexIso` — the whole chain, from the
  unbounded right derived functor of sections through the chart transport to the derived
  restriction followed by the two derived reindexings followed by derived sections at `Z`.

## How the composite is reached, and why that matters

The hypothesis `Stacks.Cohomology.LerayUnbounded.ComputesSecond` of
`derivedCompIsoOfComputes` is proved for restriction to a slice of the small étale ringed site of
an algebraic space and an **arbitrary** additive functor out of the modules on that slice:
`AlgebraicGeometry.Space.computesSecond_overFunctor`.  So the derived statement is available for
the whole of the transport in one application, with the underived input
`chartTransportSectionsIso` and with `e = Iso.refl` — and that is what is done here.

The route of composing the three one-step derived crossings of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsTransport.lean` is *not* taken, and the
module documentation of that file records why: chaining them puts
`CategoryTheory.Functor.comp` against `SheafOfModules.evaluation` at a junction, which costs
4,664,592 heartbeats.  Deriving the composite directly avoids every such junction, and the two
statements below are checked in well under a second.

## The spellings, which are not cosmetic

`Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes` forces **one** middle category on the
restriction functor and on the sections functor of the transport, and one target category on the
latter and on the conclusion.  The two sheaves of rings on a slice —
`(smallEtaleRingedSite B S hS X.1 X.2).ringSheaf.over U`, which is the codomain of
`SheafOfModules.overFunctor`, and `((smallEtaleRingedSite B S hS X.1 X.2).over U).ringSheaf`,
which is the domain of `AlgebraicGeometry.Space.chartLocalizationReindex` — are definitionally
equal, but `AlgebraicGeometry.RingedSite.over` is a `def` returning a structure literal, so the
reduction between them is not available at reducible transparency and instance search declines
it.  A `CategoryTheory.Functor.Additive` instance for the sections functor of the transport
synthesized at one spelling therefore does not answer the goal at the other, and that — not a
heartbeat ceiling — is what blocks the application.

The repair used here is to name the functors with their domain and codomain **ascribed**:
`chartSliceReindex` is `chartLocalizationReindex` with its domain written at the
`ringSheaf.over U` spelling, and `chartTransportSections` is the composite written there too.
These are `abbrev`s, so they are reducible and everything known about the underlying functors
applies to them unchanged; what they add is that the instances below are stated, and so resolve,
at the one spelling the application needs.  Each of the four instances that the ascription puts
out of reach of search is supplied explicitly, from the corresponding instance at the other
spelling (`isEquivalence_chartSliceReindex`, `preservesFiniteLimits_chartSliceReindex`,
`preservesFiniteColimits_chartSliceReindex`) or by the `rfl` that the sections equalities
reduce it to (`additive_chartSchemeSections`, `additive_chartTransportSections`).

Two further points need care.

*The chart `U` is passed at the `(smallEtaleRingedSite B S hS X.1 X.2).C` spelling and not at
`AlgebraicGeometry.Space.SmallEtale`.*  At the latter `(…).ringSheaf.over U` is not writable at
all: `CategoryTheory.Over U` has its object universe already fixed there, so
`CategoryTheory.Category (Over U)` asks instance search to solve `max (u + 1) ?w =?= u + 1`,
which has no solution.  Pinning that category instead — a local
`Category.{u, u + 1} (Over U)` got from `((smallEtaleRingedSite …).over U).C` — does not work
either: the *statement* of such an instance does not elaborate, failing after 21 s on the very
goal it would supply.

*The two spellings of `U` are not interchangeable in the other direction either.*  At
`(smallEtaleRingedSite B S hS X.1 X.2).C` the chart that the transport names cannot be written:
`AlgebraicGeometry.Space.SmallEtale.chartLocalizationEquivalence B S hS X.1 U` needs
`Category (Over U)` for its codomain and fails there, while at
`AlgebraicGeometry.Space.SmallEtale` it elaborates and the identification of the two rings of
sections

`(representedSchemeRingedSite B S hS …).ringSheaf.obj.obj (op Z)
  = (smallEtaleRingedSite B S hS X.1 X.2).ringSheaf.obj.obj (op chart)`

is inside the default heartbeat ceiling — whereas at
`(smallEtaleRingedSite B S hS X.1 X.2).C` the same identification exceeds it.  So the conclusion
below is stated with the transport's own composite on the right and not with sections at the
chart; see the implementation notes for what that leaves to do.

## Implementation notes

What is **not** here is the last link of comparison (i) of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean`: that the
unbounded right derived functor of the composite is derived sections of `𝒪_X` at the chart the
transport names.  The underived statement is proved — it is `chartTransportSectionsIso` — and the
derived one needs `SheafOfModules.evaluation (smallEtaleRingedSite …).ringSheaf (op chart)` to be
written with its codomain at the category the transport forces, which is the identification the
previous section records as writable only at the `AlgebraicGeometry.Space.SmallEtale` spelling of
`U`, at which the slice sheaf of rings that this file's statements are about cannot be written.

That pair of restrictions is not jointly unsatisfiable, and **the link is proved**, in
`StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportDerivedChartSections.lean`:
`AlgebraicGeometry.Space.derivedChartTransportChartIso`, with the whole chain
`AlgebraicGeometry.Space.derivedChartTransportSectionsChartIso`.  What that file establishes
is that the two spellings of `U` are definitionally equal — so a
declaration stated at either applies at the other with no transport at all — and that the
restriction is only on what may be *written*: a statement that writes `CategoryTheory.Over U`
needs the `(…).C` spelling, a statement that writes the chart needs the other, and the two can
sit in different declarations of one file and be composed by application.  So the codomain
ascription is made at the `AlgebraicGeometry.Space.SmallEtale` spelling
(`AlgebraicGeometry.Space.chartSectionsCrossed`) and the derived statement at the
`(smallEtaleRingedSite …).C` spelling; no ceiling is raised there either.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
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

-- The derived-category models are the `local instance`s of
-- `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean` and of
-- `StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsTransport.lean`, re-enabled here
-- rather than restated: they are `CategoryTheory.HasDerivedCategory.standard`, which instance
-- search cannot produce at a goal whose universe is already fixed to `u + 1`.
attribute [local instance] hasDerivedCategory_modules hasDerivedCategory_modules_over
  hasDerivedCategoryStandard_chartModules
  hasDerivedCategoryStandard_representedSchemeModules
  hasDerivedCategoryStandard_representedSchemeSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : (smallEtaleRingedSite B S hS X.1 X.2).C)

/-- **The reindexing of Stacks 04M0 out of the slice at a chart**, which is
`AlgebraicGeometry.Space.chartLocalizationReindex`, with its domain written at the
`SheafOfModules.overFunctor` spelling `(smallEtaleRingedSite B S hS X.1 X.2).ringSheaf.over U` of
the localized sheaf of rings rather than at the `AlgebraicGeometry.RingedSite.ringSheaf` spelling
`((smallEtaleRingedSite B S hS X.1 X.2).over U).ringSheaf`.

The two sheaves of rings are definitionally equal and this is an `abbrev`, so this is the same
functor; what the ascription buys is that the instances below are stated at the spelling the
derived composite needs.  See "The spellings, which are not cosmetic" in the module
documentation. -/
abbrev chartSliceReindex :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).over U) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O) :=
  chartLocalizationReindex B S hS X U

/-- The reindexing of Stacks 04M0 is additive at the ascribed domain, by the same `rfl` as
`AlgebraicGeometry.Space.additive_chartLocalizationReindex`: a pushforward of sheaves of modules
acts on a morphism by acting on its underlying map of presheaves. -/
local instance additive_chartSliceReindex : (chartSliceReindex B S hS X U).Additive :=
  ⟨fun {_ _} _ _ => rfl⟩

/-- The reindexing of Stacks 04M0 is an equivalence at the ascribed domain: it is the functor of
`AlgebraicGeometry.Space.chartLocalizationModulesEquivalence`. -/
local instance isEquivalence_chartSliceReindex : (chartSliceReindex B S hS X U).IsEquivalence :=
  inferInstanceAs ((chartLocalizationReindex B S hS X U).IsEquivalence)

/-- The reindexing of Stacks 04M0 preserves finite limits at the ascribed domain, being an
equivalence. -/
local instance preservesFiniteLimits_chartSliceReindex :
    PreservesFiniteLimits (chartSliceReindex B S hS X U) :=
  inferInstanceAs (PreservesFiniteLimits (chartLocalizationReindex B S hS X U))

/-- The reindexing of Stacks 04M0 preserves finite colimits at the ascribed domain, being an
equivalence. -/
local instance preservesFiniteColimits_chartSliceReindex :
    PreservesFiniteColimits (chartSliceReindex B S hS X U) :=
  inferInstanceAs (PreservesFiniteColimits (chartLocalizationReindex B S hS X U))

/-- **Sections at an object of the small étale site of the chart's scheme, read on the small étale
site of the algebraic space represented by the chart.**  It is the reindexing along the comparison
of a representable algebraic space with its scheme, followed by sections at `Z`.

The domain is written at the `AlgebraicGeometry.Space.chartRingedSite` spelling, which is the
codomain spelling of `AlgebraicGeometry.Space.chartSliceReindex`; the two sites are equal by
`AlgebraicGeometry.Space.chartRingedSite_eq_representedRingedSite`, an `rfl`. -/
abbrev chartSchemeSections (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (chartRingedSite B S hS X U).O) ⥤
      ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS
        ((SmallEtale.toOver B S hS X.1).obj U)).O).obj.obj (op Z)) :=
  representedSchemeReindex B S hS ((SmallEtale.toOver B S hS X.1).obj U) ⋙
    SheafOfModules.evaluation.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS
        ((SmallEtale.toOver B S hS X.1).obj U)).O) (op Z)

/-- `AlgebraicGeometry.Space.chartSchemeSections` is additive.  It is not synthesized: the
generic instance for a composite would need the additivity of the reindexing at the ascribed
domain, which is a second spelling of the site.  Instead
`AlgebraicGeometry.Space.sections_representedSchemeReindex_eq` collapses the composite to a single
`SheafOfModules.evaluation`, whose additivity is the `rfl` that evaluation of a sheaf of modules
is evaluation of the underlying presheaf. -/
local instance additive_chartSchemeSections (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    (chartSchemeSections B S hS X U Z).Additive := by
  change Functor.Additive (representedSchemeReindex B S hS _ ⋙ _)
  rw [sections_representedSchemeReindex_eq B S hS ((SmallEtale.toOver B S hS X.1).obj U) Z]
  exact ⟨fun {_ _} _ _ => rfl⟩

/-- **The sections functor of the chart transport.**  An `𝒪_X|_U`-module on the slice at an étale
scheme chart `U`, reindexed along the comparison of Stacks 04M0 and then along the comparison of
the represented algebraic space with its scheme, and evaluated at an object `Z` of the small étale
site of that scheme.

It is the functor that `AlgebraicGeometry.Space.chartTransportSectionsIso` computes, with its
domain written at the `SheafOfModules.overFunctor` spelling of the localized sheaf of rings. -/
abbrev chartTransportSections (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).over U) ⥤
      ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS
        ((SmallEtale.toOver B S hS X.1).obj U)).O).obj.obj (op Z)) :=
  chartSliceReindex B S hS X U ⋙ chartSchemeSections B S hS X U Z

/-- The sections functor of the chart transport is additive, both of its factors being additive
at the one spelling of the site of the chart. -/
local instance additive_chartTransportSections (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    (chartTransportSections B S hS X U Z).Additive :=
  inferInstanceAs ((chartSliceReindex B S hS X U ⋙ chartSchemeSections B S hS X U Z).Additive)

/-- **Derived sections cross the chart transport.**  Let `U` be an étale scheme chart of an
algebraic space `X` and let `Z` be an object of the small étale site of the chart's scheme.  Then
the unbounded right derived functor of restriction of `𝒪_X`-modules to the slice at `U`, followed
by the unbounded right derived functor of the sections functor of the chart transport at `Z`, is
the unbounded right derived functor of the composite.

Both sides are right derived functors of one and the same functor on the unbounded homotopy
category: the comparison for the derived restriction is invertible on a K-injective complex with
no hypothesis, and the one for the derived sections functor of the transport is invertible at the
degreewise restriction of a K-injective complex by
`AlgebraicGeometry.Space.computesSecond_overFunctor`, which is Stacks 08FI at the slice together
with Stacks 0D6G and which is stated for an arbitrary additive functor out of the modules on the
slice.  Uniqueness of right derived functors identifies the two.

The whole transport is derived in one application, with `e = Iso.refl`; the module documentation
records why composing the three one-step derived crossings of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsTransport.lean` is not the route. -/
def derivedChartTransportSectionsIso (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    Stacks.DerivedFunctor.totalRightDerived
        (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U) ⋙
      Stacks.DerivedFunctor.totalRightDerived (chartTransportSections B S hS X U Z) ≅
      Stacks.DerivedFunctor.totalRightDerived
        (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U ⋙
          chartTransportSections B S hS X U Z) :=
  Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes _ _ _ (Iso.refl _)
    (computesSecond_overFunctor B S hS X.1 X.2 U _)

/-- **The derived sections functor of the chart transport splits off the derived reindexing of
Stacks 04M0.**  The unbounded right derived functor of the sections functor of the transport is
the derived reindexing of Stacks 04M0 followed by the unbounded right derived functor of sections
at `Z` on the small étale site of the algebraic space represented by the chart.

This is `Stacks.Injectives.derivedPrecompIso` at the equivalence of module categories of
Stacks 04M0; the remaining derived reindexing is split off by
`AlgebraicGeometry.Space.derivedSectionsRepresentedSchemeReindexIso`. -/
def derivedChartTransportSectionsSplitIso (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    Stacks.DerivedFunctor.totalRightDerived (chartTransportSections B S hS X U Z) ≅
      (chartSliceReindex B S hS X U).mapDerivedCategory ⋙
        Stacks.DerivedFunctor.totalRightDerived (chartSchemeSections B S hS X U Z) :=
  Stacks.Injectives.derivedPrecompIso _ _

/-- **The chart transport, derived.**  Let `U` be an étale scheme chart of an algebraic space `X`
and let `Z` be an object of the small étale site of the chart's scheme.  Then the unbounded right
derived functor of sections through the whole chart transport is the derived restriction of
`𝒪_X`-modules to the slice at `U`, followed by the derived reindexing of Stacks 04M0, followed by
the derived reindexing along the comparison of the represented algebraic space with its scheme,
followed by derived sections at `Z`.

It is `AlgebraicGeometry.Space.derivedChartTransportSectionsIso` composed with
`AlgebraicGeometry.Space.derivedChartTransportSectionsSplitIso` and with
`AlgebraicGeometry.Space.derivedSectionsRepresentedSchemeReindexIso`.  This is the
derived-functor layer of comparison (i) of
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/RelativeAbsolute.lean`; what it
does not do is name the left-hand side as derived sections of `𝒪_X` at the chart the transport
produces, and the implementation notes of this file record the measurement that blocks that. -/
def derivedChartTransportIso (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    Stacks.DerivedFunctor.totalRightDerived
        (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U ⋙
          chartTransportSections B S hS X U Z) ≅
      Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U) ⋙
        ((chartSliceReindex B S hS X U).mapDerivedCategory ⋙
          ((representedSchemeReindex B S hS
              ((SmallEtale.toOver B S hS X.1).obj U)).mapDerivedCategory ⋙
            Stacks.DerivedFunctor.totalRightDerived
              (SheafOfModules.evaluation.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS
                  ((SmallEtale.toOver B S hS X.1).obj U)).O) (op Z)))) :=
  (derivedChartTransportSectionsIso B S hS X U Z).symm ≪≫
    Functor.isoWhiskerLeft _ (derivedChartTransportSectionsSplitIso B S hS X U Z ≪≫
      Functor.isoWhiskerLeft _ (derivedSectionsRepresentedSchemeReindexIso B S hS
        ((SmallEtale.toOver B S hS X.1).obj U) Z))

end ChartTransport

end AlgebraicGeometry.Space

end
