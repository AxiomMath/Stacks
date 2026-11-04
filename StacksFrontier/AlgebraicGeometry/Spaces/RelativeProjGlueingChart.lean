module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj

/-!
# The glued relative Proj, read on the étale chart it is glued from

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `𝒜` be a quasi-coherent
graded `𝒪_X`-algebra.  `AlgebraicGeometry.Space.RelativeProjGlueingData` glues the relative Proj
`Proj_X(𝒜)` out of the relative Proj `P_U` of the algebra on an étale chart `U ⟶ X`, and
`AlgebraicGeometry.Space.RelativeProjChart` is the datum that the basic properties of the
structure morphism `π : Proj_X(𝒜) ⟶ X` — Stacks 084E, 084F, 084G — are stated against: a
surjective étale scheme chart of the target together with a cartesian square identifying the
base change of `π` along it with a relative Proj of schemes.

This file connects the two: the glueing datum carries exactly that chart presentation, with the
cartesian square supplied by `AlgebraicGeometry.Space.RelativeProjGlueingData`'s own
`isPullback_chart_toBase`.  So every property of `π` that is proved from a chart presentation is
available for the glued relative Proj with no further input, and in particular for the blowing
up of an algebraic space along a closed subspace of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupRelativeProj.lean`.

Separatedness is recorded as the first such consequence, because it is one of the geometric
inputs of the universal property of blowing up: the uniqueness half of Tag 085U compares two
morphisms into the blowup through a scheme-theoretically dense open of their source, and that
comparison needs the blowup morphism to be separated.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjGlueingData.relativeProjChart` is the chart presentation
  of the glued relative Proj: the étale chart of the glueing datum, the relative Proj situation
  it carries on that chart, and the cartesian square over it.

## Main results

* `AlgebraicGeometry.Space.RelativeProjGlueingData.isSeparated_toBase`: the structure morphism
  of a glued relative Proj is separated.
* `AlgebraicGeometry.Space.isSeparated_blowUpToBase` and
  `AlgebraicGeometry.Space.isSeparated_blowUpAlongHom`: the structure morphism of the blowing up
  of an algebraic space in a quasi-coherent sheaf of ideals, respectively along a closed
  subspace, is separated.

## Implementation notes

No `@[stacks]` attribute is attached to anything here.  Stacks 084E is carried by
`AlgebraicGeometry.Space.isSeparated_relativeProj`, which is the tag's own statement for a
morphism presented on a chart; what is added below is that the glueing construction supplies
such a presentation, so the three declarations about separatedness are that one lemma applied,
not a second formalization of the tag.

The chart presentation needs no field beyond what the glueing datum already has.  Its chart is
the presenting scheme of the étale presentation of the base and its situation is the one the
glueing datum carries there, so the two identifications of schemes it asks for are the glueing
datum's `chartBaseIso` and `projChartIso`; the morphism from the chart of the source to the
source is the étale chart `P_U ⟶ Proj_X(𝒜)` of the quotient, and the cartesian square is
`AlgebraicGeometry.Space.RelativeProjGlueingData.isPullback_chart_toBase`, which is the
statement that over an étale chart of the base the glued space is the relative Proj of a scheme.

## References

* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 084E](https://stacks.math.columbia.edu/tag/084E)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

namespace RelativeProjGlueingData

variable (d : RelativeProjGlueingData B S hS X hX)

/-- **The glued relative Proj, presented on the étale chart it is glued from.** The chart of the
presentation is the presenting scheme `U` of the étale presentation of the base, the situation on
it is the one the glueing datum carries, and the cartesian square is
`AlgebraicGeometry.Space.RelativeProjGlueingData.isPullback_chart_toBase`: over `U` the glued
space is the relative Proj `P_U` of a scheme. -/
def relativeProjChart : RelativeProjChart B S hS d.toBase d.chartSituation where
  chart := d.presentation.U
  chartHom := d.presentation.toSpace
  chartHom_etale := d.presentation.etale
  chartHom_surjective := d.presentation.surjective
  baseIso := d.chartBaseIso
  proj := d.projChart
  projHom := d.projChartHom
  projIso := d.projChartIso
  projHom_comp := d.projChartHom_comp
  projToSpace := d.chart
  isPullback := d.isPullback_chart_toBase

/-- **The structure morphism of a glued relative Proj is separated.** This is Stacks 084E,
`AlgebraicGeometry.Space.isSeparated_relativeProj`, applied to the chart presentation the
glueing datum carries. -/
theorem isSeparated_toBase : IsSeparated B S hS d.toBase :=
  isSeparated_relativeProj B S hS d.isAlgebraicSpace_relativeProj d.toBase d.relativeProjChart

end RelativeProjGlueingData

/-! ### Separatedness of the blowing up of an algebraic space -/

section Blowup

variable {Y : AlgebraicSpaces B S hS}
  (N : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
  (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
  (P : Presentation B S hS Y.obj Y.property)
  (hcU : B.Contains (reesChartSituation N hN P).relativeProj)
  (hcR : B.Contains (reesRelationSituation N hN P).relativeProj)

/-- **The blowing up of an algebraic space in a quasi-coherent sheaf of ideals has separated
structure morphism.** The blowup is the relative Proj of the Rees algebra, glued from the
relative Proj on an étale chart, so this is Stacks 084E for that glueing datum. -/
theorem isSeparated_blowUpToBase
    (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget N hN P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource N hN P hcU hcR))) :
    IsSeparated B S hS (blowUpToBase N hN P hcU hcR heq) :=
  (reesGlueingData N hN P hcU hcR heq).isSeparated_toBase

section Centre

variable (Z : ClosedSubspaces B S hS Y.obj) (P : Presentation B S hS Y.obj Y.property)

variable
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)

/-- **The blowing up of an algebraic space along a closed subspace has separated structure
morphism.** The blowup of Stacks 085Q is the relative Proj of the Rees algebra of the defining
ideal sheaf of the centre, so this is Stacks 084E for its glueing datum. -/
theorem isSeparated_blowUpAlongHom
    (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR))) :
    IsSeparated B S hS (blowUpAlongHom Z P hcU hcR heq).hom :=
  isSeparated_blowUpToBase (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR heq

end Centre

end Blowup

end AlgebraicGeometry.Space

end
