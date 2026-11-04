module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentPullbackCompSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartLiftRestrictionChart

/-!
# Naturality of the acting group in the chart, reduced to a statement about sections

`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`
asks that restricting a section of the acting sheaf
`AlgebraicGeometry.Space.liftActionSheaf` to the chart presented by a restriction of a chart
presentation and then reading it as an acting section is the same as reading it at the original
presentation and restricting the acting section.  This file reduces that equation of acting
sections to a statement about *sections of Zariski modules on the chart's scheme*, which is the
form in which the four geometric compatibilities of the identification can be used.

## The reduction

An acting section of a chart presentation is determined by the derivation it induces
(`AlgebraicGeometry.Space.ChartLiftPresentation.derivOfActionSection_bijective`), and the
restriction of an acting section is *defined* by its derivation, so the equation to be proved is
an equation of derivations of `Γ(W, ⊤)`.  Both derivations are `θ ∘ d` for the universal
differential `Stacks.Smooth.pullbackD` of the chart square, and the restriction of a derivation
is restriction of regular functions along the morphism of ambient charts.  So it is enough to
have

* a map `σ` of the global sections of the two Zariski cotangent sheaves of the chart square which
  carries the universal differential of the larger presentation to that of the smaller one, and
* that the identification of the acting sheaf's chart sections with the acting group carries
  `σ` to restriction of regular functions along the morphism of ambient charts.

The first is a statement about `Stacks.Smooth.pullbackCotangentSheaf` alone; the second is where
the comparison of the two descriptions of the acting sheaf enters.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction` ·
  `isActionSectionRestrictionNatural_of_coe`: **the reduction** — the naturality in the chart of
  the identification follows from those two statements.
* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction` ·
  `derivOfActionSection_eq_restrictDeriv_of_coe` and
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction` ·
  `eq_restrictActionSection_of_derivOfActionSection`: its two halves, the passage to derivations
  and the passage back to acting sections.
* `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction` ·
  `chartCotangentSection` and `chartCotangentSection_pullbackD`: **the first obligation is
  discharged** — the comparison of the global sections of the two Zariski cotangent sheaves of
  the chart square carries one universal differential to the other, by
  `Stacks.Smooth.pullbackCotangentCompSection_pullbackD` at the factorization of the reduction
  of the presented lift.  Hence
  `AlgebraicGeometry.Space.ChartLiftPresentation.Restriction` ·
  `isActionSectionRestrictionNatural_of_chartCotangentSection`, the reduction to the single
  remaining statement.
* `AlgebraicGeometry.Space.ChartLiftPresentation.derivExt` and
  `AlgebraicGeometry.Space.ChartLiftPresentation.coe_derivOfActionSection_apply`: the two generic
  facts about the acting derivations of a chart presentation that the reduction uses — that a
  derivation into the conormal data of the chart thickening is determined by the regular
  functions its values are, and that the derivation induced by an acting section is that section
  on the universal differential.

## Implementation notes

**The predicate can be proved only through `rw`, never by `exact` against a restatement of its
body, and that is a matter of cost rather than style.**  Writing out the body of
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural` at
a single section `g` and checking a term of the predicate against it exhausts the
200 000-heartbeat budget — in this module, and also inside
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ChartLiftRestrictionChart` itself, where the
predicate is declared.  Keyed rewriting with the same equation is instant, which is also how the
one consumer of the predicate in the library uses it.  So the last step below is `intro` followed by
`rw`, and the equation rewritten with is proved as its own declaration.

Everything else here is **generic**: the two facts about derivations are stated for an arbitrary
chart presentation, and the reduction takes the acting sections, the map `σ` and both
compatibilities as arguments, so that no argument at the point of use is a restatement.  Proofs
are in term mode; the same chain written with `rw` exhausts the budget, the cost being the
instance blocks of the `letI`-laden types of
`AlgebraicGeometry.Space.ChartLiftPresentation.Deriv` and
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`.

The values of the acting sections are compared as *regular functions on the ambient chart* —
`Subtype.val` of the conormal data — rather than as elements of the conormal data with its module
structure.  That avoids the `letI` preamble entirely in the hypothesis, and loses nothing: the
conormal data is a subtype of `Γ(U', ⊤)`, and
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.restrictConormal` is characterised by
its underlying regular function.

**A correction to the decomposition written at the predicate.**  The docstring of
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`
lists the compatibility of the source comparison
`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso` — the composite of
[Stacks Project, Tag 04CU] and [Stacks Project, Tag 04CS] — as one of the four things owed, and
suggests proving it through the uniqueness principle [Stacks Project, Tag 04CX].  That is more
than is needed: a restriction *keeps* the chart square of `q`, so the factor
`AlgebraicGeometry.Space.chartSquareDifferentialsAssociatedIso`, which is where both of those
tags sit, is literally the same term at the two presentations and cancels.  What the source
compatibility actually reduces to is a composition law for
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` against
`AlgebraicGeometry.Space.modulePullbackCompIso` — which is also exactly what the implementation
notes of `StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleSchemeAgreement` record as the one
remaining obligation of [Stacks Project, Tag 04G2] (2), so the two tags share it.

No `@[stacks]` attribute is claimed: what is proved is a reduction of one step of
[Stacks Project, Tag 04AM] to statements about sections, not an assertion of a tag.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

namespace ChartLiftPresentation

variable {C S hS} {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1}

/-- **An acting derivation of a chart presentation is determined by the regular functions its
values are.**  Two `Γ(V, ⊤)`-derivations of `Γ(W, ⊤)` with values in the conormal data of the
chart thickening are equal as soon as, at every regular function on the chart of `Y`, their
values are the same regular function on the ambient chart.

This is `Derivation.ext` followed by `Subtype.ext`; it is stated separately because the module
structures of `AlgebraicGeometry.Space.ChartLiftPresentation.Deriv` have to be in scope for the
former, and introducing them at a concrete presentation is what does not fit the heartbeat
budget. -/
theorem derivExt (P : ChartLiftPresentation C S hS p q a.hom U') {δ₁ δ₂ : P.Deriv}
    (h : ∀ x : Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens)),
      letI := P.isAffineAmbient
      letI := Stacks.Smooth.algebraAppLE P.chartHomScheme P.tgt_le_preimage
      letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
      letI := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
      letI := Stacks.Smooth.moduleOfAppLEBase P.chartHomScheme P.redHomScheme
        P.tgt_le_preimage P.sub_le_preimage P.conormal
      letI := Stacks.Smooth.isScalarTowerOfAppLEBase P.chartHomScheme P.redHomScheme
        P.tgt_le_preimage P.sub_le_preimage P.conormal
      (δ₁ x).val = (δ₂ x).val) :
    δ₁ = δ₂ := by
  let := P.isAffineAmbient
  let := Stacks.Smooth.algebraAppLE P.chartHomScheme P.tgt_le_preimage
  let := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  let := Stacks.Smooth.moduleOfAppLE P.redHomScheme P.sub_le_preimage P.conormal
  let := Stacks.Smooth.moduleOfAppLEBase P.chartHomScheme P.redHomScheme
    P.tgt_le_preimage P.sub_le_preimage P.conormal
  let := Stacks.Smooth.isScalarTowerOfAppLEBase P.chartHomScheme P.redHomScheme
    P.tgt_le_preimage P.sub_le_preimage P.conormal
  exact Derivation.ext fun x => Subtype.ext (h x)

/-- The regular function underlying the value of the derivation attached to an acting section is
the one underlying the value of that section at the universal differential.  This is
`AlgebraicGeometry.Space.ChartLiftPresentation.derivOfActionSection_apply` read on the regular
functions, so that the module structures of the conormal data do not have to be in scope. -/
theorem coe_derivOfActionSection_apply (P : ChartLiftPresentation C S hS p q a.hom U')
    (θ : P.ActionSection) (x : Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens))) :
    (P.derivOfActionSection θ x).val =
      (θ (Stacks.Smooth.pullbackD P.chartHomScheme P.redHomScheme ⊤ P.sub_le_preimage x)).val :=
  congrArg Subtype.val (P.derivOfActionSection_apply θ x)

namespace Restriction

variable {P : ChartLiftPresentation C S hS p q a.hom U'} {V' : SmallEtale C S hS X'.1}
  (R : Restriction P V')

/-- **The passage to derivations.**  Suppose given acting sections `θ` of a chart presentation
and `θ'` of a restriction of it, and a map `σ` of the global sections of the two Zariski
cotangent sheaves of the chart square which carries the universal differential of the larger
presentation to that of the smaller one.  If `θ'` composed with `σ` is `θ` followed by
restriction of regular functions along the morphism of ambient charts, then the derivation
attached to `θ'` is the restriction of the derivation attached to `θ`. -/
theorem derivOfActionSection_eq_restrictDeriv_of_coe (θ : P.ActionSection)
    (θ' : R.presentation.ActionSection)
    (σ : Γ(P.chartCotangent, (⊤ : P.subScheme.Opens)) →
      Γ(R.presentation.chartCotangent, (⊤ : R.presentation.subScheme.Opens)))
    (hσ : ∀ x : Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens)),
      σ (Stacks.Smooth.pullbackD P.chartHomScheme P.redHomScheme ⊤ P.sub_le_preimage x) =
        Stacks.Smooth.pullbackD R.presentation.chartHomScheme R.presentation.redHomScheme ⊤
          R.presentation.sub_le_preimage x)
    (hmain : ∀ y : Γ(P.chartCotangent, (⊤ : P.subScheme.Opens)),
      (θ' (σ y)).val = R.ambientMapScheme.appTop.hom (θ y).val) :
    R.presentation.derivOfActionSection θ' =
      R.restrictDeriv (P.derivOfActionSection θ) :=
  derivExt R.presentation fun x =>
    ((coe_derivOfActionSection_apply R.presentation θ' x).trans
      ((congrArg (fun z => (θ' z).val) (hσ x).symm).trans
        ((hmain _).trans
          (congrArg (fun z => R.ambientMapScheme.appTop.hom z)
            (coe_derivOfActionSection_apply P θ x).symm)))).trans
      (R.coe_restrictDeriv_apply (P.derivOfActionSection θ) x).symm

/-- **The passage back to acting sections**, at one section of the acting sheaf: the chart-level
reading of its restriction is the restriction of its chart-level reading as soon as the two
derivations agree.  This is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.eq_restrictActionSection`, which is
the uniqueness half of
`AlgebraicGeometry.Space.ChartLiftPresentation.derivOfActionSection_bijective`. -/
theorem eq_restrictActionSection_of_derivOfActionSection
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (g : (liftActionSheaf C S hS Z q a).val.obj (op P.subEtaleChart))
    (h : R.presentation.derivOfActionSection (actionSectionEquiv C S hS R.presentation hw hv
          ((liftActionSheaf C S hS Z q a).val.map
            (R.subEtaleChartMap (Z := Z) (a := a)).op g)) =
        R.restrictDeriv (P.derivOfActionSection (actionSectionEquiv C S hS P hw hv g))) :
    actionSectionEquiv C S hS R.presentation hw hv
        ((liftActionSheaf C S hS Z q a).val.map (R.subEtaleChartMap (Z := Z) (a := a)).op g) =
      R.restrictActionSection (actionSectionEquiv C S hS P hw hv g) :=
  R.eq_restrictActionSection h

/-- **The naturality in the chart of the identification of the acting group, reduced to a
statement about sections.**  Granted a map `σ` of the global sections of the two Zariski
cotangent sheaves of the chart square which carries the universal differential of the larger
presentation to that of the smaller one, the identification of the acting sheaf's chart sections
with the acting group of a chart presentation is natural in the chart as soon as it carries `σ`
to restriction of regular functions along the morphism of ambient charts.

This is
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.IsActionSectionRestrictionNatural`
with its two remaining obligations isolated. -/
theorem isActionSectionRestrictionNatural_of_coe
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (σ : Γ(P.chartCotangent, (⊤ : P.subScheme.Opens)) →
      Γ(R.presentation.chartCotangent, (⊤ : R.presentation.subScheme.Opens)))
    (hσ : ∀ x : Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens)),
      σ (Stacks.Smooth.pullbackD P.chartHomScheme P.redHomScheme ⊤ P.sub_le_preimage x) =
        Stacks.Smooth.pullbackD R.presentation.chartHomScheme R.presentation.redHomScheme ⊤
          R.presentation.sub_le_preimage x)
    (hmain : ∀ (g : (liftActionSheaf C S hS Z q a).val.obj (op P.subEtaleChart))
      (y : Γ(P.chartCotangent, (⊤ : P.subScheme.Opens))),
      ((actionSectionEquiv C S hS R.presentation hw hv
            ((liftActionSheaf C S hS Z q a).val.map
              (R.subEtaleChartMap (Z := Z) (a := a)).op g)) (σ y)).val =
        R.ambientMapScheme.appTop.hom ((actionSectionEquiv C S hS P hw hv g) y).val) :
    R.IsActionSectionRestrictionNatural (Z := Z) (a := a) hw hv := by
  intro g
  rw [R.eq_restrictActionSection_of_derivOfActionSection hw hv g
    (R.derivOfActionSection_eq_restrictDeriv_of_coe _ _ σ hσ (hmain g))]

/-- **The comparison of the global sections of the two Zariski cotangent sheaves of the chart
square.**  The chart square of `q` is kept by a restriction and the presented lift is
precomposed with the morphism of the two closed subschemes, so the cotangent sheaf of the
restricted presentation is the pullback of the one of `P` along that morphism; this is the
induced map of global sections,
`Stacks.Smooth.pullbackCotangentCompSection` at the factorization
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.subMapScheme_comp_redHomScheme`. -/
noncomputable def chartCotangentSection :
    Γ(P.chartCotangent, (⊤ : P.subScheme.Opens)) →
      Γ(R.presentation.chartCotangent, (⊤ : R.presentation.subScheme.Opens)) :=
  Stacks.Smooth.pullbackCotangentCompSection P.chartHomScheme P.redHomScheme R.subMapScheme
    R.presentation.redHomScheme R.subMapScheme_comp_redHomScheme

/-- **The comparison of the two cotangent sheaves carries the universal differential of the
larger presentation to that of the smaller one**. -/
theorem chartCotangentSection_pullbackD (x : Γ(P.tgtScheme, (⊤ : P.tgtScheme.Opens))) :
    R.chartCotangentSection
        (Stacks.Smooth.pullbackD P.chartHomScheme P.redHomScheme ⊤ P.sub_le_preimage x) =
      Stacks.Smooth.pullbackD R.presentation.chartHomScheme R.presentation.redHomScheme ⊤
        R.presentation.sub_le_preimage x :=
  Stacks.Smooth.pullbackCotangentCompSection_pullbackD P.chartHomScheme P.redHomScheme
    R.subMapScheme R.presentation.redHomScheme R.subMapScheme_comp_redHomScheme x

/-- **The naturality in the chart of the identification of the acting group, reduced to one
statement about sections.**  The identification is natural in the chart as soon as it carries
the comparison
`AlgebraicGeometry.Space.ChartLiftPresentation.Restriction.chartCotangentSection` of the global
sections of the two Zariski cotangent sheaves of the chart square to restriction of regular
functions along the morphism of ambient charts. -/
theorem isActionSectionRestrictionNatural_of_chartCotangentSection
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (hmain : ∀ (g : (liftActionSheaf C S hS Z q a).val.obj (op P.subEtaleChart))
      (y : Γ(P.chartCotangent, (⊤ : P.subScheme.Opens))),
      ((actionSectionEquiv C S hS R.presentation hw hv
            ((liftActionSheaf C S hS Z q a).val.map
              (R.subEtaleChartMap (Z := Z) (a := a)).op g)) (R.chartCotangentSection y)).val =
        R.ambientMapScheme.appTop.hom ((actionSectionEquiv C S hS P hw hv g) y).val) :
    R.IsActionSectionRestrictionNatural (Z := Z) (a := a) hw hv :=
  R.isActionSectionRestrictionNatural_of_coe hw hv R.chartCotangentSection
    R.chartCotangentSection_pullbackD hmain

end Restriction

end ChartLiftPresentation

end AlgebraicGeometry.Space

end
