module

public import StacksFrontier.AlgebraicGeometry.ProjThetaCompare.Glue

/-!
# The relative twist of a quasi-coherent graded algebra, transported to a relative `Proj` situation

`Stacks.AlgebraicGeometry.ProjThetaCompare.chartComparisonIso` glues a comparison of the twisting
sheaf of a relative `Proj` *situation* with a chart-indexed glueing on the other side, taking that
side's charts, chart identifications, graded rings, restriction maps and chart-refinement law as
hypotheses. **This file instantiates it once and for all at the relative twists of [Stacks, Tag
01NR]**, whose chart-refinement law is
`Stacks.AlgebraicGeometry.ProjThetaCompare.pullbackIsoOfRestrictIso_comp_twistMap_relativeTwist`.

The instantiation is done **at the level of variables**, with the situation, the graded algebra,
the comparison morphism and the chartwise graded homomorphisms all free. That is deliberate: the
chart data of the relative `Proj` of a concrete graded algebra are large terms, and substituting
them into the abstract glueing one argument at a time exceeds the elaborator's deterministic
budget. Here every argument of the glueing is a projection of a variable, and a
consumer pays only for the five hypotheses it supplies.

## Main results

* `Stacks.AlgebraicGeometry.ProjThetaCompare.twistSheafAlgebraComparisonIso`: **the relative twist
  of a quasi-coherent graded algebra, transported along a chartwise comparison to the twisting
  sheaf of a relative `Proj` situation**, in every degree in which each chart twist comparison is
  invertible.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjTwistComparison
open Stacks.RelativeProj.Situation
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

namespace Stacks.AlgebraicGeometry.ProjThetaCompare

open Stacks.RelativeProj

variable {s : Situation.{u}} (A : SheafGradedAlgebra s.base) (n : ℤ)
  (c : relativeProj s ⟶
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).scheme)
  (ι : ∀ W : s.base.affineOpens, A.grading W.1 →+*ᵍ s.sectionRingGrading W.1)
  (hι : ∀ W : s.base.affineOpens, (s.sectionRingGrading W.1)₊ ≤ (A.grading W.1)₊.map (ι W))
  (hfac : ∀ W : s.base.affineOpens, relativeProjChart s W ≫ c
    = AlgebraicGeometry.Proj.map (ι W) (hι W)
      ≫ (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).chart W.1 W.2)
  (hnest : ∀ {W W' : s.base.affineOpens} (h : W' ≤ W),
    (gradedSectionRestriction s W'.1 W.1 h).comp (ι W) = (ι W').comp (A.res h))

include A ι hι hfac hnest in
/-- **The relative twist of a quasi-coherent graded algebra, transported to the twisting sheaf of a
relative `Proj` situation.** The data are exactly those of an isomorphism of chart-indexed
glueings: for every affine open `W` of the base a homomorphism `ι W` of the graded rings of local
sections covering the irrelevant ideal, compatible with the restriction maps, and with
`chart_s W ≫ c = Proj.map (ι W) ≫ chart_A W`; plus invertibility of each chart twist comparison.

This is `Stacks.AlgebraicGeometry.ProjThetaCompare.chartComparisonIso` with the other side's chart
data read off `Stacks.AlgebraicGeometry.RelativeProj.relativeProj` and
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso`. -/
public def twistSheafAlgebraComparisonIso
    (hinv : ∀ W : s.base.affineOpens, IsIso (twistMap (ι W) (hι W) n)) :
    (Scheme.Modules.pullback c).obj (relativeTwist A n) ≅ twistSheaf s n :=
  chartComparisonIso c (fun W => A.grading W.1) (relativeTwist A n)
    (fun W => (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).chart W.1 W.2) n
    (fun W => chartRestrictTwistIso A n W)
    (fun {_ _} h => A.res h)
    (fun {W W'} h => irrelevant_le_map_res A W'.1 W.1 h W'.2 W.2)
    (fun {W W'} h => projMap_res_comp_chart A W' W h)
    (fun {W W'} h => pullbackIsoOfRestrictIso_comp_twistMap_relativeTwist A n W' W h)
    ι hι hfac hnest hinv

end Stacks.AlgebraicGeometry.ProjThetaCompare

end
