module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullbackEquations
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection

/-!
# The source comparison of a chart presentation is the general chart-square comparison

`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso` is
`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso` at the data a chart
presentation carries.  This file records that as an equation **between the isomorphisms**, which
is the one place it is cheap: everything proved about the general comparison — in particular the
factorizations of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullbackEquations` and the
derivation compatibility of
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsDerivation` — then transfers to
the presentation by `congrArg`, with no projection taken underneath a `def`.

A consumer wanting the components of `chartSourceIso` should compose this with
`AlgebraicGeometry.Space.chartDifferentialsAssociatedCotangentIso_hom` or `…_inv` rather than
project `chartSourceIso` itself; the measurement in
`StacksFrontier.AlgebraicGeometry.Spaces.ChartSquareDifferentialsChartPullbackEquations` says why.

## Main results

* `AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso_eq`: the source comparison **is**
  the general chart-square comparison at the presentation's chart square, its presented étale
  chart of the subspace, and the reduction of the presented lift.

No `@[stacks]` attribute is claimed.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

namespace ChartLiftPresentation

variable {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1}
  (P : ChartLiftPresentation C S hS p q a.hom U')

/-- **The source comparison at a presented chart is the general chart-square comparison.**  The
two charts of `q` carried by the presentation are its chart square, the presented étale chart of
the subspace is the chart of the source, and the reduction of the presented lift is the morphism
of the site through which the composite factors — which is exactly what
`AlgebraicGeometry.Space.ChartLiftPresentation.subChart_comp` provides.

This is `rfl`, and it is stated between the isomorphisms so that the general comparison's
factorizations and its derivation compatibility transfer by `congrArg`. -/
theorem chartSourceIso_eq
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
    chartSourceIso C S hS P hw hv =
      chartDifferentialsAssociatedCotangentIso C S hS q a
        (ObjectProperty.homMk P.tgtChart) (ObjectProperty.homMk P.bseChart) P.chartHom
        ((isEtale_iff_presheaf_of_yoneda C S hS P.tgtChart).2 hw)
        ((isEtale_iff_presheaf_of_yoneda C S hS P.bseChart).2 hv)
        P.chartSq' P.subEtaleChart (P.incl ≫ P.liftHom) P.subChart_comp :=
  rfl

end ChartLiftPresentation

end AlgebraicGeometry.Space

end
