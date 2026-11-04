module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeEtaleSquareComparison

/-!
# The chart-space comparison is bijective exactly when the base-change comparison is

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`, let
`M` be a quasi-coherent `𝒪_Y`-module and let `d` be a diagram of affine étale scheme charts over
`f`.  `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_bijective_comparison`
reduces the bijectivity of `AlgebraicGeometry.Space.modulePullbackChartBaseChange B S hS f M d`
to the bijectivity of one component of the comparison
`AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison` of the chart-space square of `d`.
This file shows the reduction is an **equivalence**: the two statements imply each other.

## Main results

* `AlgebraicGeometry.Space.bijective_modulePullbackEtaleSquareComparison_app_iff`: the component
  of the comparison of the chart-space square over the identity chart is bijective if and only
  if the canonical base-change comparison at `(f, d)` is.

## Implementation notes

Both directions are the identity
`AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison_baseChange` — the comparison carries
the base-change comparison of the square to the one at `(f, d)` — together with the bijectivity
of the base-change comparison of the square itself, which
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange` supplies because the
restriction of `M` to the chart space of `d.V` carries a presentation which is right exact on the
sections over the identity chart.  A composite of two maps, one of which is bijective, is
bijective exactly when the other is.

The content of the equivalence is negative and worth recording: the reduction loses nothing, so
the component statement is not weaker than the chart bijectivity of Stacks 083K, and no proof of
it can avoid the coherence of the comparisons of Stacks 03LU and 03LW that the chart bijectivity
needs.  See the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartBaseChangeEtaleSquareComparison.lean`.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The comparison of the chart-space square of a diagram of affine étale charts is bijective
on the sections over the identity chart exactly when the canonical base-change comparison at
`(f, d)` is bijective.**

The forward implication is
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_bijective_comparison`.  For
the converse, the comparison carries the base-change comparison of the square to the one at
`(f, d)` (`AlgebraicGeometry.Space.modulePullbackEtaleSquareComparison_baseChange`), and the
former is bijective by `AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange`, the
restriction of `M` to the chart space of `d.V` carrying a presentation which is right exact on
the sections over the identity chart; so the comparison is the one base-change comparison
composed with the inverse of the other. -/
theorem bijective_modulePullbackEtaleSquareComparison_app_iff (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    Function.Bijective
        ((modulePullbackEtaleSquareComparison B S hS f (chartSpaceMapOver B S hS d.g)
          (chartToSpace B S hS X d.U) (chartToSpace B S hS Y d.V)
          (isEtale_chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS Y d.V)
          (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm) M).val.app
          (op (chartSpaceIdChartDiagram B S hS f d).U)) ↔
      letI := chartDiagramAlgebra B S hS f d
      Function.Bijective (modulePullbackChartBaseChange B S hS f M d) := by
  obtain ⟨P, hgen, -, hex⟩ :=
    exists_presentation_rightExact_app_idEtaleChart B S hS Y M hM d.V hV
  let _ := chartDiagramAlgebra B S hS (chartSpaceMapOver B S hS d.g)
    (chartSpaceIdChartDiagram B S hS f d)
  have hb := bijective_modulePullbackChartBaseChange B S hS (chartSpaceMapOver B S hS d.g)
    ((etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V)).obj M)
    (isQuasicoherentOnSite_etaleModulePullback B S hS (chartToSpace B S hS Y d.V)
      (isEtale_chartToSpace B S hS Y d.V) M hM)
    P (chartSpaceIdChartDiagram B S hS f d) hU hV hgen hex
  have key := modulePullbackEtaleSquareComparison_baseChange B S hS f
    (chartSpaceMapOver B S hS d.g) (chartToSpace B S hS X d.U) (chartToSpace B S hS Y d.V)
    (isEtale_chartToSpace B S hS X d.U) (isEtale_chartToSpace B S hS Y d.V)
    (chartSpaceMapOver_comp_chartToSpace B S hS f d.g d.comm.symm) M
    (chartSpaceIdChartDiagram B S hS f d)
  refine ⟨bijective_modulePullbackChartBaseChange_of_bijective_comparison B S hS f M hM d hU hV,
    fun hbf ↦ ⟨fun x y hxy ↦ ?_, fun t ↦ ?_⟩⟩
  · obtain ⟨z, hz⟩ := hb.2 x
    obtain ⟨w, hw⟩ := hb.2 y
    refine hz ▸ hw ▸ congrArg _ (hbf.1 ?_)
    refine (key z).symm.trans (Eq.trans ?_ (key w))
    exact (congrArg _ hz).trans (hxy.trans (congrArg _ hw).symm)
  · obtain ⟨z, hz⟩ := hbf.2 t
    exact ⟨_, (key z).trans hz⟩

end AlgebraicGeometry.Space

end
