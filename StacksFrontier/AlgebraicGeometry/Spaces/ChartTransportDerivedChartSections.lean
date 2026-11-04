module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartTransportDerivedSections
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.SectionsRestrictionIsomorphism
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.BoundedBelowRestriction

/-!
# Derived chart transport and derived sections over the chart

Let `X` be an algebraic space over a scheme `S` and let `U` be an étale scheme chart of `X`. The
chart transport carries an `𝒪_X`-module to a module on the small étale site of the scheme of the
chart: restriction to the slice `X_étale/U`, then the reindexing of Stacks 04M0, then the
reindexing along the comparison of the representable algebraic space of the chart with its scheme.
This file identifies the unbounded right derived functor of sections through the whole transport
with `RΓ(V, -)` on the small étale site of `X`, where `V` is the étale chart that the two
comparison equivalences attach to an object `Z` of the small étale site of the chart's scheme.

## Main definitions

* `AlgebraicGeometry.Space.chartOfComparison`: the étale chart of `X` attached to `Z`.
* `AlgebraicGeometry.Space.chartSectionsCrossed`: sections of an `𝒪_X`-module over that chart,
  with codomain the modules over the ring of sections at `Z`.
* `AlgebraicGeometry.Space.chartTransportDerived`: the derived chart transport followed by
  derived sections at `Z`.

## Main results

* `AlgebraicGeometry.Space.derivedChartSectionsCrossedIso`: the unbounded right derived functor of
  `chartSectionsCrossed` is `RΓ` over the chart.
* `AlgebraicGeometry.Space.derivedChartTransportChartIso`: the unbounded right derived functor of
  sections through the whole chart transport is derived sections over the chart.
* `AlgebraicGeometry.Space.derivedChartTransportSectionsChartIso`: derived sections over the chart
  are the derived restriction to the slice, followed by the two derived reindexings, followed by
  derived sections at `Z`.
* `AlgebraicGeometry.Space.derivedChartSectionsTopIso`: `RΓ(U, -)` is `RΓ` over the chart attached
  to `⊤`, after the restriction of scalars along the induced isomorphism of rings of sections.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

section ChartTransport

attribute [local instance] smallEtaleRingedSite_essentiallySmall
  hasSheafifyAddCommGrp_smallEtaleRingedSite
  wEqualsLocallyBijectiveAddCommGrp_smallEtaleRingedSite
  hasRightDerivedFunctor_chartSections
  isGrothendieckAbelian_modules
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  hasSheafify_chartLocalization wEqualsLocallyBijective_chartLocalization
  abelian_chartLocalizationModules abelian_chartModules
  additive_chartLocalizationReindex additive_representedSchemeReindex

attribute [local instance] hasDerivedCategory_modules hasDerivedCategory_modules_over
  hasDerivedCategory_sections
  hasDerivedCategoryStandard_chartModules
  hasDerivedCategoryStandard_representedSchemeModules
  hasDerivedCategoryStandard_representedSchemeSections

attribute [local instance] additive_chartSliceReindex isEquivalence_chartSliceReindex
  preservesFiniteLimits_chartSliceReindex preservesFiniteColimits_chartSliceReindex
  additive_chartSchemeSections additive_chartTransportSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

section Chart

variable (U : SmallEtale B S hS X.1)

/-- The étale chart of `X` that the two comparison equivalences attach to an object `Z` of the
small étale site of the chart's scheme: the composite of the comparison of Stacks 04M0 with the
comparison of a representable algebraic space and its scheme, evaluated at `Z`. -/
abbrev chartOfComparison (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) : SmallEtale B S hS X.1 :=
  ((SmallEtale.chartLocalizationEquivalence B S hS X.1 U).functor.obj
    ((representedSmallEtaleEquivalence B S hS
      ((SmallEtale.toOver B S hS X.1).obj U)).inverse.obj Z)).left

/-- Sections of an `𝒪_X`-module over the chart `chartOfComparison B S hS X U Z`, with codomain
the modules over the ring of sections at `Z` of the small étale site of the chart's scheme. -/
abbrev chartSectionsCrossed (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⥤
      ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS
        ((SmallEtale.toOver B S hS X.1).obj U)).O).obj.obj (op Z)) :=
  SheafOfModules.evaluation.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (op (chartOfComparison B S hS X U Z))

/-- The functor `chartSectionsCrossed B S hS X U Z` is additive. -/
local instance additive_chartSectionsCrossed (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    (chartSectionsCrossed B S hS X U Z).Additive :=
  ⟨fun {_ _} _ _ => rfl⟩

/-- The unbounded right derived functor of `AlgebraicGeometry.Space.chartSectionsCrossed` is
derived sections of `𝒪_X` over the chart `chartOfComparison B S hS X U Z`. -/
def derivedChartSectionsCrossedIso (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    Stacks.DerivedFunctor.totalRightDerived (chartSectionsCrossed B S hS X U Z) ≅
      Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        (chartOfComparison B S hS X U Z) :=
  Iso.refl _

/-- Derived sections over an étale chart `U` are derived sections over the chart the comparisons
attach to the whole of the chart's scheme, followed by the restriction of scalars along the induced
isomorphism of rings of sections. -/
def derivedChartSectionsTopIso :
    Stacks.Cohomology.HypercohomologyEdge.derivedSections
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U ≅
      Stacks.Cohomology.HypercohomologyEdge.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          (openChartOfComparison B S hS X U ⊤) ⋙
        Stacks.Cohomology.HypercohomologyEdge.restrictScalarsDerived
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          (openChartOfComparisonTopIso B S hS X U).hom :=
  haveI : IsIso (C := (smallEtaleRingedSite B S hS X.1 X.2).C)
      (openChartOfComparisonTopIso B S hS X U).hom := Iso.isIso_hom _
  Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrictIso
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (openChartOfComparisonTopIso B S hS X U).hom

end Chart

attribute [local instance] additive_chartSectionsCrossed

section Slice

variable (U : (smallEtaleRingedSite B S hS X.1 X.2).C)

/-- The functor `chartSectionsCrossed B S hS X U Z` is additive, for `U` an object of
`(smallEtaleRingedSite B S hS X.1 X.2).C`. -/
local instance additive_chartSectionsCrossedSlice (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    (chartSectionsCrossed B S hS X U Z).Additive :=
  additive_chartSectionsCrossed B S hS X U Z

/-- The derived restriction of `𝒪_X`-modules to the slice at `U`, followed by the derived
reindexing of Stacks 04M0, followed by the derived reindexing along the comparison of the
represented algebraic space with its scheme, followed by derived sections at `Z`. -/
abbrev chartTransportDerived (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⥤
      DerivedCategory (ModuleCat.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS
          ((SmallEtale.toOver B S hS X.1).obj U)).O).obj.obj (op Z))) :=
  Stacks.DerivedFunctor.totalRightDerived
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U) ⋙
    ((chartSliceReindex B S hS X U).mapDerivedCategory ⋙
      ((representedSchemeReindex B S hS
          ((SmallEtale.toOver B S hS X.1).obj U)).mapDerivedCategory ⋙
        Stacks.DerivedFunctor.totalRightDerived
          (SheafOfModules.evaluation.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (representedSchemeRingedSite B S hS
              ((SmallEtale.toOver B S hS X.1).obj U)).O) (op Z))))

/-- The unbounded right derived functor of sections through the whole chart transport is the
unbounded right derived functor of sections of `𝒪_X` over the étale chart that the two comparison
equivalences attach to `Z`. -/
def derivedChartTransportChartIso (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    Stacks.DerivedFunctor.totalRightDerived
        (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) U ⋙
          chartTransportSections B S hS X U Z) ≅
      Stacks.DerivedFunctor.totalRightDerived (chartSectionsCrossed B S hS X U Z) :=
  Stacks.DerivedFunctor.totalRightDerivedIsoOfIso _ (chartTransportSectionsIso B S hS X U Z)

/-- Derived sections of an `𝒪_X`-module over the étale chart the comparisons attach to `Z` are
the derived restriction to the slice at `U`, followed by the derived reindexing of Stacks 04M0,
followed by the derived reindexing along the comparison of the represented algebraic space with its
scheme, followed by derived sections at `Z`. -/
def derivedChartTransportSectionsChartIso (Z : (representedSchemeRingedSite B S hS
    ((SmallEtale.toOver B S hS X.1).obj U)).C) :
    Stacks.DerivedFunctor.totalRightDerived (chartSectionsCrossed B S hS X U Z) ≅
      chartTransportDerived B S hS X U Z :=
  (derivedChartTransportChartIso B S hS X U Z).symm ≪≫ derivedChartTransportIso B S hS X U Z

end Slice

end ChartTransport

end AlgebraicGeometry.Space

end
