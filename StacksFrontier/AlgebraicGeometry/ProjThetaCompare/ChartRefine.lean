module

public import StacksFrontier.AlgebraicGeometry.ProjThetaCompare.Morphism
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.ComparisonChart
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.PullbackChartRefine

/-!
# The chart-refinement law of Tag 01NR's twists, at `Stacks.ProjTwistComparison.twistMap`

`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso_hom_eq` is the two-chart compatibility of
the chart identifications of the relative twists of [Stacks, Tag 01NR]: over a nested pair
`T ⊆ U` of affine opens of the base, reading a section of `𝒪(n)` on the chart of `U` and then
comparing down is reading it on the chart of `T`. Its comparison of the chart twists is Tag
01NO's `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`.

The glueing of a morphism over a chart cover consumes the same law with the comparison written as
`Stacks.ProjTwistComparison.twistMap` instead — that is the shape
`Stacks.ProjTwistComparison.twistMap_chartMember_pullback_eq` and
`twistMap_comp_pullbackChartDesc` take as their hypothesis `hν`, and the shape in which the
chart-refinement law of the second glueing of the relative twists,
`Stacks.RelativeProj.Situation.pullbackIsoOfRestrictIso_comp_twistMap_projMap`, is already
available. **This file proves that law.**

## The route

Both sides are morphisms out of an inverse image, so the law is proved on the other side of the
pullback--pushforward adjunction. There the left-hand side is, by
`Stacks.AlgebraicGeometry.PushforwardCocycle.transpose_cocycle`, the transpose of the chart
identification over `U` — which is `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTheta` — followed
by the direct image of `Stacks.ProjTwistComparison.pushforwardTwistMap` and the congruence
isomorphism; and the right-hand side is the transpose of the chart identification over `T`. The
identity between them is
`Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTheta_comp_pushNested`, Tag 01NR's own two-chart
compatibility on sections, once Tag 01NO's pushed-forward comparison is identified with the
direct image of `pushforwardTwistMap` — which is
`Stacks.AlgebraicGeometry.ProjThetaCompare.pushNested_eq_pushforwardTwistMap`, the one place the
pointwise identification of the two `θ`'s enters.

## Main results

* `Stacks.AlgebraicGeometry.ProjThetaCompare.pushforwardCongr_map_comp`: a coherence for the
  congruence isomorphisms of the direct image, at the level of variables.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.projMap_res_comp_chart`: the chart factorization with
  the transition morphism written as `AlgebraicGeometry.Proj.map` of the restriction map.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.pushNested_eq_pushforwardTwistMap`: **Tag 01NO's
  pushed-forward twist comparison is the direct image of
  `Stacks.ProjTwistComparison.pushforwardTwistMap`.**
* `Stacks.AlgebraicGeometry.ProjThetaCompare.chartTheta_comp_pushforwardTwistMap`: Tag 01NR's
  two-chart compatibility with that comparison in place of Tag 01NO's.
* `Stacks.AlgebraicGeometry.ProjThetaCompare.pullbackIsoOfRestrictIso_comp_twistMap_relativeTwist`:
  **the chart-refinement law**, in the shape the glueing consumes.

## Not done here

No tag is claimed: this is a coherence law of a glueing restated at a second spelling of one
comparison map.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.PushforwardCocycle
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.Tag07ZGTwist

namespace Stacks.AlgebraicGeometry.ProjThetaCompare

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### A coherence for the congruence isomorphisms of the direct image -/

/-- **The direct image of a congruence isomorphism, followed by a congruence isomorphism, is a
congruence isomorphism.** At the level of variables; every instance of it below would otherwise
ask the kernel to compare two presheaf restrictions along equal opens at the transition morphisms
of a relative projective spectrum. -/
public theorem pushforwardCongr_map_comp {X Y Z : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g)
    (c : Y ⟶ Z) {d : X ⟶ Z} (hgc : g ≫ c = d) (hfc : f ≫ c = d) (N : X.Modules) :
    (Scheme.Modules.pushforward c).map ((Scheme.Modules.pushforwardCongr hfg).hom.app N)
        ≫ (Scheme.Modules.pushforwardCongr hgc).hom.app N
      = (Scheme.Modules.pushforwardCongr hfc).hom.app N := by
  subst hfg
  obtain rfl : hgc = hfc := Subsingleton.elim _ _
  have hid : (Scheme.Modules.pushforward c).map
      ((Scheme.Modules.pushforwardCongr (rfl : f = f)).hom.app N) =
      𝟙 ((Scheme.Modules.pushforward (f ≫ c)).obj N) :=
    (congrArg (fun z => (Scheme.Modules.pushforward c).map z)
      (pushforwardCongr_refl_hom_app f rfl N)).trans (CategoryTheory.Functor.map_id _ _)
  exact (eq_whisker hid _).trans (Category.id_comp _)

/-! ### Tag 01NO's pushed-forward comparison at the second spelling -/

section Instance

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (n : ℤ) (T U : S.affineOpens)
  (h : (T.1 : S.Opens) ≤ (U.1 : S.Opens))

/-- **The chart factorization of a nested pair of affine opens of the base, with the transition
morphism written as `AlgebraicGeometry.Proj.map` of the restriction map.** -/
public theorem projMap_res_comp_chart :
    AlgebraicGeometry.Proj.map (A.res h) (irrelevant_le_map_res A T.1 U.1 h T.2 U.2)
        ≫ (relativeProj A).chart (U.1 : S.Opens) U.2
      = (relativeProj A).chart (T.1 : S.Opens) T.2 :=
  (congrArg (· ≫ (relativeProj A).chart (U.1 : S.Opens) U.2)
      (projMap_res_eq_projInclusionMap A T.1 U.1 h T.2 U.2)).trans
    ((relativeProj A).chart_transition (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)

/-- **Tag 01NO's pushed-forward twist comparison is the direct image of
`Stacks.ProjTwistComparison.pushforwardTwistMap`**, followed by the congruence isomorphism for the
chart factorization. -/
public theorem pushNested_eq_pushforwardTwistMap :
    ChartTransRelativeProj.pushNested A (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2 n
      = (Scheme.Modules.pushforward ((relativeProj A).chart (U.1 : S.Opens) U.2)).map
            (Stacks.ProjTwistComparison.pushforwardTwistMap (A.res h)
              (irrelevant_le_map_res A T.1 U.1 h T.2 U.2) n)
        ≫ (Scheme.Modules.pushforwardCongr (projMap_res_comp_chart A T U h)).hom.app
            (twistingSheaf (A.grading (T.1 : S.Opens)) n) := by
  refine Eq.trans (ChartTransRelativeProj.pushNested_eq A (T.1 : S.Opens) (U.1 : S.Opens) h
    T.2 U.2 n) ?_
  refine Eq.trans (eq_whisker (congrArg
    (fun z => (Scheme.Modules.pushforward ((relativeProj A).chart (U.1 : S.Opens) U.2)).map z)
    (transpose_projInclusionTwistIso_eq A T.1 U.1 h T.2 U.2 n)) _) ?_
  refine Eq.trans (eq_whisker (CategoryTheory.Functor.map_comp _ _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (pushforwardCongr_map_comp
    (projMap_res_eq_projInclusionMap A T.1 U.1 h T.2 U.2)
    ((relativeProj A).chart (U.1 : S.Opens) U.2)
    ((relativeProj A).chart_transition (T.1 : S.Opens) (U.1 : S.Opens) h T.2 U.2)
    (projMap_res_comp_chart A T U h) (twistingSheaf (A.grading (T.1 : S.Opens)) n))

/-- **Tag 01NR's two-chart compatibility of the chart identifications, with
`Stacks.ProjTwistComparison.pushforwardTwistMap` as the comparison of the chart twists.** -/
public theorem chartTheta_comp_pushforwardTwistMap :
    chartTheta A n U
        ≫ (Scheme.Modules.pushforward ((relativeProj A).chart (U.1 : S.Opens) U.2)).map
            (Stacks.ProjTwistComparison.pushforwardTwistMap (A.res h)
              (irrelevant_le_map_res A T.1 U.1 h T.2 U.2) n)
        ≫ (Scheme.Modules.pushforwardCongr (projMap_res_comp_chart A T U h)).hom.app
            (twistingSheaf (A.grading (T.1 : S.Opens)) n)
      = chartTheta A n T :=
  Eq.trans (whisker_eq _ (pushNested_eq_pushforwardTwistMap A n T U h).symm)
    (chartTheta_comp_pushNested A n T U h)

/-! ### The chart-refinement law -/

/-- Tag 01NR's chart identification of the `n`-th relative twist, in the `restrict` form the
twist datum carries it in. `Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso` is this followed
by the identification of restriction with inverse image. -/
public abbrev chartRestrictTwistIso :
    (relativeTwist A n).restrict ((relativeProj A).chart (U.1 : S.Opens) U.2) ≅
      twistingSheaf (A.grading (U.1 : S.Opens)) n :=
  (GluedTwistAlgebra.twistDataOfGradedAlgebra A).chartData.chartIso (U.1 : S.Opens) U.2 n

/-- **The chart-refinement law of the glueing of Tag 01NR's relative twists**, with the comparison
of the chart twists written as `Stacks.ProjTwistComparison.twistMap`.

This is the shape `Stacks.ProjTwistComparison.twistMap_chartMember_pullback_eq` and
`twistMap_comp_pullbackChartDesc` consume, and the shape in which the same law for the second
glueing of the relative twists is already available as
`Stacks.RelativeProj.Situation.pullbackIsoOfRestrictIso_comp_twistMap_projMap`.

Proved on the other side of the adjunction, where it is
`Stacks.AlgebraicGeometry.ProjThetaCompare.chartTheta_comp_pushforwardTwistMap`. -/
public theorem pullbackIsoOfRestrictIso_comp_twistMap_relativeTwist :
    (Scheme.Modules.pullbackIsoOfRestrictIso ((relativeProj A).chart (U.1 : S.Opens) U.2)
          (chartRestrictTwistIso A n U)
          (AlgebraicGeometry.Proj.map (A.res h) (irrelevant_le_map_res A T.1 U.1 h T.2 U.2))
          (projMap_res_comp_chart A T U h).symm).hom
        ≫ Stacks.ProjTwistComparison.twistMap (A.res h)
            (irrelevant_le_map_res A T.1 U.1 h T.2 U.2) n
      = (((Scheme.Modules.restrictFunctorIsoPullback
            ((relativeProj A).chart (T.1 : S.Opens) T.2)).app (relativeTwist A n)).symm
          ≪≫ chartRestrictTwistIso A n T).hom := by
  refine transpose_injective ((relativeProj A).chart (T.1 : S.Opens) T.2)
    (relativeTwist A n) ?_
  refine Eq.trans (congrArg (fun z => transpose ((relativeProj A).chart (T.1 : S.Opens) T.2)
      (relativeTwist A n) z)
    ((eq_whisker (Scheme.Modules.pullbackIsoOfRestrictIso_hom
        ((relativeProj A).chart (U.1 : S.Opens) U.2) (chartRestrictTwistIso A n U)
        (AlgebraicGeometry.Proj.map (A.res h) (irrelevant_le_map_res A T.1 U.1 h T.2 U.2))
        (projMap_res_comp_chart A T U h).symm) _).trans
      (((Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))).trans
        (eq_whisker (Scheme.Modules.pullbackCongr_symm_hom_app
          (projMap_res_comp_chart A T U h) (relativeTwist A n)) _)))) ?_
  refine ((transpose_cocycle
    (AlgebraicGeometry.Proj.map (A.res h) (irrelevant_le_map_res A T.1 U.1 h T.2 U.2))
    ((relativeProj A).chart (U.1 : S.Opens) U.2)
    ((relativeProj A).chart (T.1 : S.Opens) T.2) (projMap_res_comp_chart A T U h)
    (relativeTwist A n) (twistingSheaf (A.grading (U.1 : S.Opens)) n)
    (twistingSheaf (A.grading (T.1 : S.Opens)) n)
    (((Scheme.Modules.restrictFunctorIsoPullback
        ((relativeProj A).chart (U.1 : S.Opens) U.2)).app (relativeTwist A n)).symm
      ≪≫ chartRestrictTwistIso A n U).hom
    (Stacks.ProjTwistComparison.twistMap (A.res h)
      (irrelevant_le_map_res A T.1 U.1 h T.2 U.2) n) _ rfl).symm).trans ?_
  refine Eq.trans (whisker_eq _ (eq_whisker (congrArg
    (fun z => (Scheme.Modules.pushforward ((relativeProj A).chart (U.1 : S.Opens) U.2)).map z)
    (Stacks.ProjTwistComparison.transpose_twistMap (A.res h)
      (irrelevant_le_map_res A T.1 U.1 h T.2 U.2) n)) _)) ?_
  exact chartTheta_comp_pushforwardTwistMap A n T U h

end Instance

end Stacks.AlgebraicGeometry.ProjThetaCompare

end
