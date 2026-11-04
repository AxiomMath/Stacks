module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftPairBaseDerivation

/-!
# The difference of two lifts over an arbitrary étale chart

Let `X ⊆ X'` be a first-order thickening of algebraic spaces, `q : Y ⟶ Bb` a morphism and
`a : X ⟶ Y` a morphism over `Bb`.  A section of the sheaf of lifts
`AlgebraicGeometry.Space.liftsSubfunctor` over an object `U'` of the small étale site of `X'` is a
lift of `a` over that chart.

`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftPairBaseDerivation` produces the chart-free
difference of two lifts `a', b' : X' ⟶ Y` over `Bb` as a global section of the acting sheaf of
[Stacks Project, Tag 061D].  This file restricts the whole lifting problem along a chart and
applies it there, so that **two lifts over an arbitrary chart `U'` have a difference, with no
chart presentation and no hypothesis beyond the thickening**.

That is the construction a `AlgebraicGeometry.Space.LiftDifferenceFamily` needs at each chart;
see "What is not done here" for the one identification still owed.

## Main definitions

* `AlgebraicGeometry.Space.chartLiftHom`: a section of the sheaf of lifts over `U'`, read as a
  morphism of algebraic spaces `chartSpace U' ⟶ Y`.
* `AlgebraicGeometry.Space.chartLiftPairGlobalSection`: **the difference of two lifts over an
  arbitrary chart**, as a global section of the acting sheaf of the thickening restricted along
  that chart.

## Main results

* `AlgebraicGeometry.Space.chartLiftHom_comp`: a lift is a morphism over `Bb`, and
  `AlgebraicGeometry.Space.chartLiftHom_comp_eq`: two lifts over one chart have the same
  composite with `q`.  That is the hypothesis `a' ≫ q = b' ≫ q` of
  `AlgebraicGeometry.Space.liftPairGlobalSectionOfCompEq`.
* `AlgebraicGeometry.Space.preimage_ι_comp_chartLiftHom_eq` and
  `AlgebraicGeometry.Space.inclusion_comp_chartLiftHom_eq`: two lifts over one chart agree on the
  closed subspace of the restricted thickening.  That is its hypothesis `i ≫ a' = i ≫ b'`.
* `AlgebraicGeometry.Space.inclusion_comp_chartLiftHom`: the inclusion of the restricted
  thickening followed by a lift is the restriction of `a` itself, so the acting sheaf of the
  restricted problem is the acting sheaf of the original one restricted.

## Implementation notes

**Nothing here is geometry.**  The restriction of the thickening is
`AlgebraicGeometry.Space.isThickening_preimage` and
`AlgebraicGeometry.Space.isFirstOrderThickening_preimage` ([Stacks Project, Tag 09ZX]) at
`f := AlgebraicGeometry.Space.chartToSpace`, which is already stated for an *arbitrary* morphism
of algebraic spaces; no étale hypothesis is used and no chart presentation appears.  The two
hypotheses of `AlgebraicGeometry.Space.liftPairGlobalSectionOfCompEq` are the two clauses of
`AlgebraicGeometry.Space.IsChartLift` read through
`AlgebraicGeometry.Space.isChartLift_iff_restrict`, one for each of the two lifts.

**Why a section of the sheaf of lifts is a morphism at all.**
`AlgebraicGeometry.Space.chartSpace` is by definition the algebraic space represented by the
chart, so a section of `AlgebraicGeometry.Space.liftsSubfunctor` over `U'` — an element of
`Y.1.obj (op ((SmallEtale.toOver _ _ _ _).obj U'))` satisfying
`AlgebraicGeometry.Space.IsChartLift` — becomes a morphism of algebraic spaces by
`CategoryTheory.yonedaEquiv.symm` and `CategoryTheory.ObjectProperty.homMk`, the category of
algebraic spaces being a full subcategory of presheaves.  Every equation between such morphisms
is then an equation of presheaf morphisms by
`CategoryTheory.ObjectProperty.hom_ext`.  No declaration in the tree packaged this passage
before, which is why it is here.

## What is not done here

**One identification is owed, and it is the only thing between this file and the first
unconditional `AlgebraicGeometry.Space.LiftDifferenceFamily`:** the global sections of the acting
sheaf of the *restricted* thickening, which is where
`AlgebraicGeometry.Space.chartLiftPairGlobalSection` lands, have to be identified with the
sections over `U'` of the *transported* acting sheaf
`AlgebraicGeometry.Space.liftActionSheafTransport`, which is where a
`AlgebraicGeometry.Space.LiftDifferenceFamily` takes its values.  Four of the five links of that
chain are in the tree:

* `AlgebraicGeometry.Space.liftActionSheafTransport_obj` is `rfl`: the sections over `U'` are the
  sections of `AlgebraicGeometry.Space.liftActionSheaf` over the base-changed chart
  `AlgebraicGeometry.Space.thickeningChartBaseChange.obj U'`;
* `AlgebraicGeometry.Space.smallEtaleInternalHomChartPullbackHomEquiv` reads the sections of an
  internal Hom at a chart as morphisms of the module pullbacks to the chart space, with
  `AlgebraicGeometry.Space.smallEtaleInternalHomOverIso` ([Stacks Project, Tag 0E8H]) behind it;
* `AlgebraicGeometry.Space.smallEtaleInternalHomSectionsEquiv` turns morphisms of modules back
  into global sections of an internal Hom;
* the two modules restrict correctly, by
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` ([Stacks Project, Tag 04CU])
  and `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso` ([Stacks Project,
  Tag 04CO], functorial by its `_comp`).

The missing link is the comparison of the base-changed chart
`AlgebraicGeometry.Space.thickeningChartBaseChange.obj U'` with the closed subspace
`Z.preimage (chartToSpace U').hom` of the chart space, **for a bare `U'`**.  The only such
comparison in the tree,
`AlgebraicGeometry.Space.ChartLiftPresentation.subEtaleChartIso`, needs a chart presentation —
an affine chart square of `q` and a presenting closed immersion — and so is not available at an
arbitrary object of the site.

## References

* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
  {Bb X' Y : AlgebraicSpaces C S hS}

/-! ### A lift over a chart as a morphism of algebraic spaces -/

/-- **A section of the sheaf of lifts over a chart, as a morphism of algebraic spaces.**  The
chart space is the algebraic space represented by the chart, so the datum of a section is already
a morphism of presheaves; the category of algebraic spaces being a full subcategory, that is a
morphism of algebraic spaces. -/
def chartLiftHom (p : X' ⟶ Bb) (q : Y ⟶ Bb) {Z : Subfunctor X'.1} (a : Z.toFunctor ⟶ Y.1)
    (U' : SmallEtale C S hS X'.1)
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    chartSpace C S hS X' U' ⟶ Y :=
  ObjectProperty.homMk (yonedaEquiv.symm β.1)

/-- **A lift over a chart is a morphism over `Bb`.**  This is the first clause of
`AlgebraicGeometry.Space.IsChartLift`. -/
theorem chartLiftHom_comp (p : X' ⟶ Bb) (q : Y ⟶ Bb) {Z : Subfunctor X'.1}
    (a : Z.toFunctor ⟶ Y.1) (U' : SmallEtale C S hS X'.1)
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    chartLiftHom C S hS p q a U' β ≫ q = chartToSpace C S hS X' U' ≫ p :=
  ObjectProperty.hom_ext _ β.2.1

/-- **Two lifts over one chart have the same composite with `q`**, both being the structure
morphism of the chart followed by `p`.  This is the hypothesis `a' ≫ q = b' ≫ q` of
`AlgebraicGeometry.Space.liftPairGlobalSectionOfCompEq`. -/
theorem chartLiftHom_comp_eq (p : X' ⟶ Bb) (q : Y ⟶ Bb) {Z : Subfunctor X'.1}
    (a : Z.toFunctor ⟶ Y.1) (U' : SmallEtale C S hS X'.1)
    (β γ : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    chartLiftHom C S hS p q a U' β ≫ q = chartLiftHom C S hS p q a U' γ ≫ q :=
  (chartLiftHom_comp C S hS p q a U' β).trans
    (chartLiftHom_comp C S hS p q a U' γ).symm

/-! ### Two lifts agree on the closed subspace of the restricted thickening -/

/-- **Two lifts over one chart agree on the preimage of the closed subspace in that chart.**
Both restrict there to the restriction of `a`, by the second clause of
`AlgebraicGeometry.Space.IsChartLift` in the form
`AlgebraicGeometry.Space.isChartLift_iff_restrict`. -/
theorem preimage_ι_comp_chartLiftHom_eq (p : X' ⟶ Bb) (q : Y ⟶ Bb) {Z : Subfunctor X'.1}
    (a : Z.toFunctor ⟶ Y.1) (U' : SmallEtale C S hS X'.1)
    (β γ : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    (Z.preimage U'.1.hom).ι ≫ (chartLiftHom C S hS p q a U' β).hom =
      (Z.preimage U'.1.hom).ι ≫ (chartLiftHom C S hS p q a U' γ).hom :=
  (((isChartLift_iff_restrict C S hS p q a U' _).mp β.2).2).trans
    (((isChartLift_iff_restrict C S hS p q a U' _).mp γ.2).2).symm

/-- **The inclusion of the restricted thickening followed by a lift is the restriction of `a`.**
So the acting sheaf of the restricted lifting problem is the acting sheaf of the original one,
restricted — not a new morphism's. -/
theorem inclusion_comp_chartLiftHom (p : X' ⟶ Bb) (q : Y ⟶ Bb) {Z : Subfunctor X'.1}
    (a : Z.toFunctor ⟶ Y.1) (hG : IsThickening C S hS X' Z)
    (U' : SmallEtale C S hS X'.1)
    (β : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    (IsThickening.inclusion C S hS
          (isThickening_preimage C S hS Z (chartToSpace C S hS X' U') hG) ≫
        chartLiftHom C S hS p q a U' β).hom =
      Z.fromPreimage (chartToSpace C S hS X' U').hom ≫ a :=
  ((isChartLift_iff_restrict C S hS p q a U' _).mp β.2).2

/-- **Two lifts over one chart agree on the closed subspace of the restricted thickening.**  This
is the hypothesis `i ≫ a' = i ≫ b'` of
`AlgebraicGeometry.Space.liftPairGlobalSectionOfCompEq`, at the restricted thickening. -/
theorem inclusion_comp_chartLiftHom_eq (p : X' ⟶ Bb) (q : Y ⟶ Bb) {Z : Subfunctor X'.1}
    (a : Z.toFunctor ⟶ Y.1) (hG : IsThickening C S hS X' Z)
    (U' : SmallEtale C S hS X'.1)
    (β γ : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    IsThickening.inclusion C S hS
          (isThickening_preimage C S hS Z (chartToSpace C S hS X' U') hG) ≫
        chartLiftHom C S hS p q a U' β =
      IsThickening.inclusion C S hS
          (isThickening_preimage C S hS Z (chartToSpace C S hS X' U') hG) ≫
        chartLiftHom C S hS p q a U' γ :=
  ObjectProperty.hom_ext _
    ((inclusion_comp_chartLiftHom C S hS p q a hG U' β).trans
      (inclusion_comp_chartLiftHom C S hS p q a hG U' γ).symm)

/-! ### The difference of two lifts over a chart -/

/-- **The difference of two lifts over an arbitrary chart of `X'`**, as a global section of the
acting sheaf of [Stacks Project, Tag 061D] for the thickening restricted along that chart.

No chart presentation is used and no hypothesis is carried beyond `G ⊂ X'` being a first-order
thickening: the restriction of the thickening along the chart is [Stacks Project, Tag 09ZX] at an
arbitrary morphism, and the two hypotheses of
`AlgebraicGeometry.Space.liftPairGlobalSectionOfCompEq` are the two clauses of
`AlgebraicGeometry.Space.IsChartLift` for the two lifts.

This is what a `AlgebraicGeometry.Space.LiftDifferenceFamily` is to take as its value at `U'`;
what is still owed is the identification of the home of this section with the sections of
`AlgebraicGeometry.Space.liftActionSheafTransport` over `U'`, for which see the module
documentation. -/
def chartLiftPairGlobalSection (p : X' ⟶ Bb) (q : Y ⟶ Bb) {Z : Subfunctor X'.1}
    (a : Z.toFunctor ⟶ Y.1) (hG : IsThickening C S hS X' Z)
    (hX : IsFirstOrderThickening C S hS X' Z)
    (U' : SmallEtale C S hS X'.1)
    (β γ : (liftsSubfunctor C S hS p q a).toFunctor.obj (op U')) :
    (liftActionSheaf C S hS
      ⟨Z.preimage (chartToSpace C S hS X' U').hom,
        (isThickening_preimage C S hS Z (chartToSpace C S hS X' U') hG).1⟩ q
      (IsThickening.inclusion C S hS
          (isThickening_preimage C S hS Z (chartToSpace C S hS X' U') hG) ≫
        chartLiftHom C S hS p q a U' γ)).sections :=
  liftPairGlobalSectionOfCompEq C S hS
    (isThickening_preimage C S hS Z (chartToSpace C S hS X' U') hG)
    (chartLiftHom C S hS p q a U' β) (chartLiftHom C S hS p q a U' γ)
    (inclusion_comp_chartLiftHom_eq C S hS p q a hG U' β γ) q
    (isFirstOrderThickening_preimage C S hS Z (chartToSpace C S hS X' U') hX)
    (chartLiftHom_comp_eq C S hS p q a U' β γ)

end AlgebraicGeometry.Space

end
