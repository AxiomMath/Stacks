module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartTransportDerivedChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDefinition

/-!
# `RΓ(U, E)` at an étale chart is the derived chart transport at the whole of the chart's scheme

Let `X` be an algebraic space over a scheme `S`, let `U` be an étale scheme chart of `X` and let
`E` be an object of `D_QCoh(𝒪_X)`.  `StacksFrontier/AlgebraicGeometry/Spaces/
ChartTransportDerivedChartSections.lean` identifies the unbounded right derived functor of
sections through the whole chart transport with `RΓ(V, -)` for the étale chart `V` that the two
comparison equivalences of Stacks 04M0 and Stacks 03ED attach to a chosen object `Z` of the small
étale site of the chart's scheme, and identifies `RΓ(U, -)` with `RΓ` over the chart attached to
the Zariski open `⊤`; what it leaves to its consumer is the composition of the two, which at the
concrete object `Z = AlgebraicGeometry.SmallEtale.opensObj … ⊤` it records as outside the
heartbeat ceiling.  This file pays that specialization.

What makes it payable is that the composition is taken **on objects** rather than on functors.
See "Where the cost sits" below: the two sides of the composition land in the derived
categories of modules over two spellings of one ring, and asking for the two *functor* categories
— hence for the two `CategoryTheory.HasDerivedCategory` data — to be identified is what exceeds
the ceiling, while asking for the two objects to be identified does not.

## Main results

* `AlgebraicGeometry.Space.chartSchemeTopObject`: the whole of the chart's scheme, as an object
  of its small étale site.
* `AlgebraicGeometry.Space.derivedChartSectionsTransportAppIso`: **the composition.**  For any
  object `Z` of the small étale site of the chart's scheme and any isomorphism between the chart
  that the comparisons attach to `Z` and `U` itself, the derived sections of an `𝒪_X`-module over
  `U` are the derived chart transport at `Z`, read over the ring `𝒪_X(U)` along the induced
  isomorphism of rings of sections.
* `AlgebraicGeometry.Space.chartDerivedSectionsTransportTopIso`: that iso at `Z = ⊤` and at the
  isomorphism `AlgebraicGeometry.Space.openChartOfComparisonTopIso`, stated through
  `AlgebraicGeometry.Space.chartDerivedSections` — which is the complex `RΓ(U, E)` that both
  sides of Stacks 0DII are about.

## Where the cost sits

Everything below refers to the default heartbeat ceiling, which nothing here raises.

*The ring identification is cheap; the identification of the two derived categories built on it
is not.*  At an object `Z` of the small étale site of the chart's scheme write `V` for the chart
`AlgebraicGeometry.Space.chartOfComparison … Z`.  Then

`(representedSchemeRingedSite B S hS …).ringSheaf.obj.obj (op Z)
  = (smallEtaleRingedSite B S hS X.1 X.2).ringSheaf.obj.obj (op V)`

holds by `rfl` and so does the induced equality of `ModuleCat`s — both inside the ceiling, and
both needed, since the left-hand spelling is the one the derived chart transport produces and the
right-hand one is the spelling at which restriction of scalars along `e : V ≅ U` is written.  The
equality of the two `DerivedCategory`s is `rfl` too, but only once a
`CategoryTheory.HasDerivedCategory` instance exists at the right-hand spelling: instance search
does not invert the projections of a ringed site, so neither
`AlgebraicGeometry.Space.hasDerivedCategoryStandard_representedSchemeSections` nor
`AlgebraicGeometry.Space.hasDerivedCategoryStandard_chartSections` answers a goal whose ring is
`𝒪_X(V)`.  `AlgebraicGeometry.Space.hasDerivedCategoryStandard_spaceChartSections` supplies it,
at the spelling of the chart's type that `chartOfComparison` has — which is
`AlgebraicGeometry.Space.SmallEtale` and not `(smallEtaleRingedSite …).C`, the two being keyed
apart through the type argument of `Opposite.op` exactly as recorded for
`AlgebraicGeometry.Space.additive_chartSectionsCrossedSlice`.

*With that instance in place the composition still may not be written on functors.*  Stated as

`RΓ(U, -) ≅ chartTransportDerived … Z ⋙ restrictScalarsDerived 𝒪_X e.hom`

the elaborator exceeds 200,000 heartbeats at `whnf` on the second factor of the composite, and it
does so at an *abstract* `Z` as well as at `Z = ⊤`: what it is asked to do is to identify the two
functor categories, hence the two `HasDerivedCategory` instances, and not merely the two rings.
The same is true of the intermediate form with
`Stacks.DerivedFunctor.totalRightDerived (chartSectionsCrossed … Z)` in place of the chart
transport.  Taken on objects — `(RΓ(U, -)).obj E ≅ (restrictScalarsDerived …).obj
((chartTransportDerived … Z).obj E)` — the identification asked for is the one that `rfl` gives
cheaply, and the whole composition, together with its specialization to `⊤`, checks in under a
second.

*So the specialization to `⊤` is free once the object-level form is stated at an abstract `Z`.*
`AlgebraicGeometry.Space.chartDerivedSectionsTransportTopIso` is
`AlgebraicGeometry.Space.derivedChartSectionsTransportAppIso` applied, with no further
unification: `AlgebraicGeometry.Space.openChartOfComparison … ⊤` is by construction
`chartOfComparison …` at `AlgebraicGeometry.Space.chartSchemeTopObject`, both being reducible
abbreviations.

## What this does not do

The restriction of scalars is not removed.  It is not removable here — the rings `𝒪_X(U)` and
`𝒪_X(V)` are isomorphic and not equal, `AlgebraicGeometry.Space.openChartOfComparison … ⊤` going
through `CategoryTheory.Functor.preimage` — and it is harmless only on the `Prop` side of
pseudo-coherence, by
`PseudoCoherence.isPseudoCoherentFrom_restrictScalars_ringEquiv`.  Absorbing it there asks for a
`RingEquiv` whose underlying ring map is the one `restrictScalarsDerived` is written along, and
that is left to the consumer; the isomorphism supplied here is what such a consumer needs.  **The
consumer exists**: `StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsPseudoCoherentAtTop
.lean` absorbs it, in both clauses of Stacks 064Q, by `RingEquiv.ofBijective` of the ring map
itself together with `StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv`.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- Removed as instances for this file for the reason recorded in the implementation notes of
-- `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean`: they answer
-- `Abelian (SheafOfModules …)` and `IsGrothendieckAbelian (SheafOfModules …)` with the module
-- universe fixed to the join of the universes of the site and the rings, and a search reaching
-- one of them first ends in a universe constraint with no solution rather than in a recoverable
-- failure.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

section ChartTransportTop

attribute [local instance] smallEtaleRingedSite_essentiallySmall
  hasSheafifyAddCommGrp_smallEtaleRingedSite
  wEqualsLocallyBijectiveAddCommGrp_smallEtaleRingedSite
  hasRightDerivedFunctor_chartSections
  isGrothendieckAbelian_modules
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  hasSheafify_chartLocalization wEqualsLocallyBijective_chartLocalization
  abelian_chartLocalizationModules abelian_chartModules
  additive_chartLocalizationReindex additive_representedSchemeReindex

-- The derived-category models of
-- `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleSliceKInjective.lean` and of
-- `StacksFrontier/AlgebraicGeometry/Spaces/ChartDerivedSectionsTransport.lean`, re-enabled here
-- rather than restated: they are `CategoryTheory.HasDerivedCategory.standard`, which instance
-- search cannot produce at a goal whose universe is already fixed to `u + 1`.
attribute [local instance] hasDerivedCategory_modules hasDerivedCategory_modules_over
  hasDerivedCategory_sections
  hasDerivedCategoryStandard_chartModules
  hasDerivedCategoryStandard_representedSchemeModules
  hasDerivedCategoryStandard_representedSchemeSections

-- The ascribed-domain instances of
-- `StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportDerivedSections.lean` and of
-- `StacksFrontier/AlgebraicGeometry/Spaces/ChartTransportDerivedChartSections.lean`, re-enabled for
-- the same reason: their declarations are public, their `instance` attribute is not.
attribute [local instance] additive_chartSliceReindex isEquivalence_chartSliceReindex
  preservesFiniteLimits_chartSliceReindex preservesFiniteColimits_chartSliceReindex
  additive_chartSchemeSections additive_chartTransportSections
  additive_chartSectionsCrossed

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)

/-- The standard derived category of the modules of sections of `𝒪_X` at an étale chart of `X`.

It is named because instance search cannot produce `CategoryTheory.HasDerivedCategory.standard`
at a goal whose universe is already fixed to `u + 1`, and it is stated at the
`AlgebraicGeometry.Space.SmallEtale` spelling of the chart's type rather than at
`(smallEtaleRingedSite B S hS X.1 X.2).C` because that is the spelling of the chart that
`AlgebraicGeometry.Space.chartOfComparison` produces; the two are keyed apart through the type
argument of `Opposite.op`, as recorded at
`AlgebraicGeometry.Space.additive_chartSectionsCrossedSlice`. -/
local instance hasDerivedCategoryStandard_spaceChartSections (W : SmallEtale B S hS X.1) :
    HasDerivedCategory.{u + 1}
      (ModuleCat.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
          (op W))) :=
  HasDerivedCategory.standard _

/-- **The whole of a chart's scheme, as an object of its small étale site.**  This is the object
`Z` at which the chart that the two comparison equivalences attach to `Z` is the chart `U` itself,
by `AlgebraicGeometry.Space.openChartOfComparisonTopIso`. -/
abbrev chartSchemeTopObject : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C :=
  AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B) (chartScheme U)
    ((SmallEtale.toOver B S hS X.1).obj U).left.property ⊤

/-- **Derived sections over an étale chart are the derived chart transport, on objects.**  Let
`U` be an étale scheme chart of an algebraic space `X`, let `Z` be an object of the small étale
site of the chart's scheme and let `e` be an isomorphism between the étale chart that the
comparisons of Stacks 04M0 and Stacks 03ED attach to `Z` and `U` itself.  Then for every object
`E` of the derived category of `𝒪_X`-modules, `RΓ(U, E)` is the derived chart transport of `E` at
`Z`, read over the ring `𝒪_X(U)` along the isomorphism of rings of sections induced by `e`.

This is `Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrictIso` at `e`, evaluated at
`E`, followed by the image under the restriction of scalars of the chain
`AlgebraicGeometry.Space.derivedChartSectionsCrossedIso` and
`AlgebraicGeometry.Space.derivedChartTransportSectionsChartIso` at `E`.  It is stated on objects
and not on functors; see "Where the cost sits" in the module documentation for why the
functor form is out of reach and this one is cheap. -/
def derivedChartSectionsTransportAppIso
    (Z : (representedSchemeRingedSite B S hS ((SmallEtale.toOver B S hS X.1).obj U)).C)
    (e : chartOfComparison B S hS X U Z ≅ U)
    (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) :
    (Stacks.Cohomology.HypercohomologyEdge.derivedSections
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U).obj E ≅
      (Stacks.Cohomology.HypercohomologyEdge.restrictScalarsDerived
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          e.hom).obj
        ((chartTransportDerived B S hS X U Z).obj E) :=
  haveI : IsIso (C := (smallEtaleRingedSite B S hS X.1 X.2).C) e.hom := Iso.isIso_hom _
  (Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrictIso
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      e.hom).app E ≪≫
    (Stacks.Cohomology.HypercohomologyEdge.restrictScalarsDerived
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) e.hom).mapIso
        (((derivedChartSectionsCrossedIso B S hS X U Z).symm ≪≫
          derivedChartTransportSectionsChartIso B S hS X U Z).app E)

/-- **`RΓ(U, E)` is the derived chart transport at the whole of the chart's scheme.**  For an
object `E` of `D_QCoh(𝒪_X)` and an étale scheme chart `U` of `X`, the complex `RΓ(U, E)` of
`𝒪_X(U)`-modules — which is what both sides of Stacks 0DII are about — is the derived restriction
of `E` to the slice `X_étale/U`, followed by the derived reindexing of Stacks 04M0, followed by
the derived reindexing along the comparison of the represented algebraic space with its scheme,
followed by derived sections at the whole of the chart's scheme, read over `𝒪_X(U)` along the
isomorphism of rings of sections induced by
`AlgebraicGeometry.Space.openChartOfComparisonTopIso`.

This is `AlgebraicGeometry.Space.derivedChartSectionsTransportAppIso` at
`Z = AlgebraicGeometry.Space.chartSchemeTopObject` and at that isomorphism of charts, applied and
not re-elaborated: `AlgebraicGeometry.Space.openChartOfComparison … ⊤` is `chartOfComparison …`
at `chartSchemeTopObject` by construction, both being reducible abbreviations. -/
def chartDerivedSectionsTransportTopIso (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    chartDerivedSections B S hS X.1 X.2 U E ≅
      (Stacks.Cohomology.HypercohomologyEdge.restrictScalarsDerived
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          (openChartOfComparisonTopIso B S hS X U).hom).obj
        ((chartTransportDerived B S hS X U (chartSchemeTopObject B S hS X U)).obj E.obj) :=
  derivedChartSectionsTransportAppIso B S hS X U (chartSchemeTopObject B S hS X U)
    (openChartOfComparisonTopIso B S hS X U) E.obj

end ChartTransportTop

end AlgebraicGeometry.Space

end
