module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen

/-!
# The chartwise conditions follow from the conditions on the site

`AlgebraicGeometry.Space.IsQuasicoherentOnCharts` and
`AlgebraicGeometry.Space.IsFinitePresentationOnCharts` say that the restriction of an
`𝒪_X`-module to every étale scheme chart is quasi-coherent, resp. of finite presentation, as a
module on the Zariski site of that scheme.  Properties of Spaces, Section 05VR defines both
properties for a module on an algebraic space on the small étale site instead, and the chartwise
readings are the form in which the scheme-level theorems — Stacks 0399 for the openness of a
flat locus, say — consume them.

This file supplies the implication from the site-level finite-presentation condition to the
chartwise reading of quasi-coherence, so that a theorem whose source hypothesis is the
site-level one need not carry a chartwise reading as an extra hypothesis.  The corresponding
passage from quasi-coherence on the site is
`AlgebraicGeometry.Space.isQuasicoherentOnCharts_of_isQuasicoherentOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartRestrictionFromSite.lean`, and the chartwise reading
of finite presentation is
`AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFinitePresentationOnSite` of
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationChartRestriction.lean`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnCharts_of_isFinitePresentationOnSite`: an
  `𝒪_X`-module of finite presentation on the site is quasi-coherent on charts, finite
  presentation on the site implying quasi-coherence on the site.

## Implementation notes

The statement is `AlgebraicGeometry.Space.isQuasicoherentOnCharts_of_isQuasicoherentOnSite`
with the algebraic space bundled into an object of
`AlgebraicGeometry.Space.AlgebraicSpaces`: the chartwise predicate is stated for a functor
together with a proof that it is an algebraic space, the chart-restriction theorem for the
bundled pair, and the two presentations agree by `rfl`.

It does not ask for quasi-coherence on the site: that follows from finite presentation on the
site, by `SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite`.

## References

* [Stacks Project, Tag 05VR](https://stacks.math.columbia.edu/tag/05VR)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An `𝒪_X`-module of finite presentation on the small étale site is quasi-coherent on
charts.**  Finite presentation on the site implies quasi-coherence on the site, by
`SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite`. -/
theorem isQuasicoherentOnCharts_of_isFinitePresentationOnSite
    (hX : IsAlgebraicSpace B S hS X) (F : Modules.{u, u} B S hS X hX)
    (hF : SheafOfModules.IsFinitePresentationOnSite F) :
    IsQuasicoherentOnCharts B S hS hX F := by
  have : SheafOfModules.IsFinitePresentationOnSite F := hF
  exact isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS ⟨X, hX⟩ F
    (SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite F)

end AlgebraicGeometry.Space

end
