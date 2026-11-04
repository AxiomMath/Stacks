module

public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationFromAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSchemeRestriction

/-!
# Finite presentation of the chart restriction on an arbitrary chart

Let `X` be an algebraic space over a scheme `S` in a big fppf site `B` and let `M` be a
quasi-coherent `𝒪_X`-module of finite presentation on the small étale site of `X`.  The file
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationChartSchemeRestriction.lean` proves that
the **global sections** of the chart restriction form a finitely presented module over an
*affine* chart.  This file removes both restrictions: the sections statement is proved over an
affine open of an arbitrary chart, and the sections statements over the affine opens of the
chart's scheme — which cover it — are assembled into finite presentation of the chart
restriction as an `AlgebraicGeometry.Scheme.Modules`.

The outcome is the comparison that Properties of Spaces, Section 05VR takes for granted: a
module of finite presentation on the small étale site of an algebraic space restricts to a
module of finite presentation, in the Zariski sense, on every étale scheme chart.  It is the
finite-presentation companion of `AlgebraicGeometry.Space.isQuasicoherent_restrictToChart`.

## Main results

* `AlgebraicGeometry.Space.finitePresentation_sections_chartSchemeModule`: over an **affine
  open** of the chart's scheme the sections of the chart restriction form a finitely presented
  module.  This is the Zariski-local form of
  `AlgebraicGeometry.Space.finitePresentation_sectionsTop_chartSchemeModule`.
* `AlgebraicGeometry.Space.isFinitePresentation_chartSchemeModule`: the chart restriction of a
  module of finite presentation on the site is of finite presentation **on every** étale scheme
  chart.

The same statement for `AlgebraicGeometry.Space.restrictToChart`, the reading of the chart
restriction that the chartwise hypotheses of the flat-locus files are stated on, is
`AlgebraicGeometry.Space.isFinitePresentation_restrictToChart` of
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationChartRestriction.lean`.

## Implementation notes

**The chart cut out by an open is the open.**  `AlgebraicGeometry.Space.openChartOfComparison` is
the chart which a Zariski open becomes under the two comparison equivalences, and its scheme is
that open on the nose, so affineness of the chart's scheme is `IsAffineOpen` of the open —
`AlgebraicGeometry.Space.isAffine_chartScheme_openChartOfComparison`.  This is the same device
that removes affineness from the coherence statement in
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentChartSchemeNonAffine.lean`.

**The sections lemma is a copy, not a reuse.**  Its proof is the chain of four applications of
`Stacks.SheafOfModules.finitePresentation_sections_pushforward` of
`AlgebraicGeometry.Space.finitePresentation_sectionsTop_chartSchemeModule` with the open `⊤`
replaced by `W` throughout; only the first step, the affineness of the chart cut out by the open,
differs.  The heartbeat budget is per-declaration, so the two are kept as separate declarations,
exactly as the finite-type pair
`AlgebraicGeometry.Space.moduleFinite_sectionsTop_chartSchemeModule` and
`AlgebraicGeometry.Space.moduleFinite_sections_chartSchemeModule` are.

**Bijectivity, not surjectivity.**  Finite presentation of sections descends along the
comparison ring maps because each of them is bijective, not merely surjective; see the module
documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationChartSchemeRestriction.lean`.

**From the sections to the sheaf.**  The assembly is
`Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover`, the
implication (5) ⇒ (3) of Stacks 01XZ with no Noetherian hypothesis, whose quasi-coherence input
is `AlgebraicGeometry.Space.isQuasicoherent_chartSchemeModule`.

No declaration here carries a `stacks` tag: the comparison is a convention of Properties of
Spaces, Section 05VR rather than a numbered statement, and the clauses of Stacks 01XZ and 03DX
that are used are already covered in the tree.

## References

* [Stacks Project, Tag 05VR](https://stacks.math.columbia.edu/tag/05VR)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))

/-! ### The sections over an affine open of the chart scheme -/

/-- **The sections of the chart restriction of a module of finite presentation over an affine
open of the chart's scheme are finitely presented.**  For a quasi-coherent `𝒪_X`-module of finite
presentation on the small étale site, any étale chart and any *affine open* `W` of the chart's
scheme, the sections over `W` of the `AlgebraicGeometry.Scheme.Modules` which `M` becomes on the
chart's scheme form a finitely presented module over the functions on `W`.

This is `AlgebraicGeometry.Space.finitePresentation_sectionsTop_chartSchemeModule` with the open
`⊤` of an affine chart replaced by an affine open of an arbitrary chart: the chain of four
pushforwards — the slice at the chart, the comparison of Stacks 04M0, the comparison of the
representable case of Stacks 03ED, and the inclusion of the small Zariski site — identifies the
sections with those of `M` over the étale chart
`AlgebraicGeometry.Space.openChartOfComparison … W`, whose scheme is affine by
`AlgebraicGeometry.Space.isAffine_chartScheme_openChartOfComparison`. -/
theorem finitePresentation_sections_chartSchemeModule
    (hM : M.IsQuasicoherentOnSite) (hfp : SheafOfModules.IsFinitePresentationOnSite M)
    (V : SmallEtale B S hS X.1) {W : (chartScheme V).Opens} (hW : IsAffineOpen W) :
    Module.FinitePresentation ((chartScheme V).ringCatSheaf.obj.obj (op W))
      ((chartSchemeModule B S hS X M hM V).val.obj (op W)) := by
  let U := _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B) (chartScheme V)
    (chartFppfObject B S hS X V).left.property W
  have h0 := module_finitePresentation_sections_of_isFinitePresentationOnSite
    (B := B) (S := S) (hS := hS) (F := X.1) (hF := X.2) M
    hM hfp (openChartOfComparison B S hS X V W)
    (isAffine_chartScheme_openChartOfComparison B S hS X V hW)
  have h1 := Stacks.SheafOfModules.finitePresentation_sections_pushforward
    (𝟙 ((structureRingSheaf B S hS X).over V)) M
    ((SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor.obj
      ((representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V)).inverse.obj
        U))
    Function.bijective_id h0
  have hcont : (SmallEtale.chartLocalizationEquivalence B S hS X.1 V).functor.IsContinuous
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      ((SmallEtale.topology B S hS X.1).over V) :=
    isContinuous_chartLocalization_chartSpace B S hS X V
  have h2 := Stacks.SheafOfModules.finitePresentation_sections_pushforward
    (𝟙 (chartStructureRingSheaf B S hS X V)) (M.over V)
    ((representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V)).inverse.obj U)
    Function.bijective_id h1
  have h3 := Stacks.SheafOfModules.finitePresentation_sections_pushforward
    (Stacks.SheafOfModules.reindexBackSharp
      (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X V)))
      (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X V))
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X V)))
    (chartSmallEtaleRestriction B S hS X M V)
    U
    (Stacks.SheafOfModules.bijective_reindexBackSharp_app _ _ _) h2
  have h4 := Stacks.SheafOfModules.finitePresentation_sections_pushforward
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B) (chartScheme V)
      (chartFppfObject B S hS X V).left.property)
    (chartSchemeEtaleModule B S hS X M hM V) W
    (_root_.AlgebraicGeometry.SmallEtale.bijective_structureMap_hom_app _ _ _ _) h3
  exact Stacks.SheafOfModules.finitePresentation_sections_of_iso
    (chartSchemeModuleIsoRestrictModule B S hS X M hM V) W h4

/-! ### Finite presentation on an arbitrary chart -/

/-- **The chart restriction of a module of finite presentation on the site is of finite
presentation on every étale scheme chart.**  The affine opens of the chart's scheme cover it, and
over each of them the sections of the chart restriction form a finitely presented module, so the
implication (5) ⇒ (3) of Stacks 01XZ applies. -/
theorem isFinitePresentation_chartSchemeModule
    (hM : M.IsQuasicoherentOnSite) (hfp : SheafOfModules.IsFinitePresentationOnSite M)
    (V : SmallEtale B S hS X.1) :
    SheafOfModules.IsFinitePresentation (chartSchemeModule B S hS X M hM V) :=
  have _hq : SheafOfModules.IsQuasicoherent (chartSchemeModule B S hS X M hM V) :=
    isQuasicoherent_chartSchemeModule B S hS X M hM V
  Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover _
    (fun W : (chartScheme V).affineOpens => (W : (chartScheme V).Opens))
    (TopologicalSpace.IsOpenCover.mk
      (_root_.AlgebraicGeometry.iSup_affineOpens_eq_top (chartScheme V)))
    (fun W => W.2)
    (fun W => finitePresentation_sections_chartSchemeModule B S hS X M hM hfp V W.2)

end AlgebraicGeometry.Space

end
