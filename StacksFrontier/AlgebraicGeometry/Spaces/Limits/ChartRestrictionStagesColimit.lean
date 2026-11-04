module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsStagesColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme

/-!
# The functions on the charts of a limit situation, read by restriction

Let `X = lim X_i` be a limit situation, let `U₀ ⟶ X₀` be an affine étale chart of the chosen
stage and let `U_i = U₀ ×_{X₀} X_i` be the induced chart of the stage `i`, with limit `U`. Two
descriptions of the regular functions on these charts occur in the proof of Stacks 07SQ:

* as a filtered colimit, `Γ(U) = colim_i Γ(U_i)`, the transition maps being pullback along the
  morphisms of the system of charts and the maps to the vertex pullback along the projections of
  the limiting cone;
* as restrictions of global functions of the algebraic spaces, `Γ(X_i) ⟶ Γ(U_i)` and
  `Γ(X) ⟶ Γ(U)`.

This file records the two statements that let the second be read inside the first: the colimit
itself, over the chosen limiting cone of the system of charts, and the commuting square relating
restriction at a stage chart with restriction at the limit chart.

Both are needed in order to read a polynomial over `Γ(X_i)` and a family of functions on `U_i` at
one and the same stage, which is the data the square of Stacks 084U is formed from.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.isStagesColimit_appTop_chartStagesCone`: the regular
  functions on the limit chart are the filtered colimit of those on the stage charts.
* `AlgebraicGeometry.Space.LimitSituation.globalFunctionsChartRestriction_limitEtaleChart`:
  restricting a global function of a stage to the chart of that stage and then pulling back to
  the limit chart is the same as pulling the function back to the limit and restricting there.

## Implementation notes

*Why nothing is proved from scratch.* The colimit is the affine case of Stacks 01Z0 for the
structure sheaf, `AlgebraicGeometry.isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed`,
applied to the diagram `AlgebraicGeometry.Space.LimitSituation.chartStagesDiagram` and its
limiting cone; every member of that diagram is affine by
`AlgebraicGeometry.Space.LimitSituation.isAffine_chartStagesDiagram_obj`, which is what the
hypothesis of that statement asks for. The commuting square is
`AlgebraicGeometry.Space.LimitSituation.limitGlobalFunctionsEquiv_naturality` with its two
equivalences evaluated by `.limitGlobalFunctionsEquiv_val` and `.stageGlobalFunctionsEquiv_val`;
those two evaluate to the section family read at the limit chart and at the stage chart, which is
`AlgebraicGeometry.Space.globalFunctionsChartRestriction` by definition.

So the content of this file is a change of spelling, from the section family read at a chart to
the restriction homomorphism. The spelling matters: the square of Stacks 084U,
`AlgebraicGeometry.Space.commSq_chart_specOfGlobalFunctions`, and the canonical morphism to the
spectrum of the global functions, `AlgebraicGeometry.Space.exists_specMap_of_globalHom`, are both
stated through the restriction homomorphism.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 084U](https://stacks.math.columbia.edu/tag/084U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

namespace LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X) {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀}

/-- **The regular functions on the limit chart are the filtered colimit of those on the stage
charts.** The system of charts of a limit situation at an affine scheme-valued point is a system
of affine schemes with a limiting cone, so the affine case of Stacks 01Z0 for the structure sheaf
applies to it. -/
theorem isStagesColimit_appTop_chartStagesCone (hI : A.ChartsBounded) :
    Stacks.IsStagesColimit
      (G := fun i : A.Stages => (Γ((A.chartStagesDiagram U₀ f₀).obj (op i), ⊤) : Type u))
      (T := (Γ((A.chartStagesConeOfChartsBounded U₀ f₀ hI).pt, ⊤) : Type u))
      (fun (i j : A.Stages) (h : i ≤ j) x =>
        ((A.chartStagesDiagram U₀ f₀).map (homOfLE h).op).appTop.hom x)
      (fun (i : A.Stages) x =>
        ((A.chartStagesConeOfChartsBounded U₀ f₀ hI).π.app (op i)).appTop.hom x) := by
  have _ : ∀ a : (A.Stages)ᵒᵖ, IsAffine ((A.chartStagesDiagram U₀ f₀).obj a) :=
    fun a => A.isAffine_chartStagesDiagram_obj U₀ f₀ a
  exact isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed (A.chartStagesDiagram U₀ f₀)
    (A.chartStagesConeOfChartsBounded U₀ f₀ hI) (A.isLimit_chartStagesConeOfChartsBounded U₀ f₀ hI)

/-- **Restriction to the charts commutes with pullback along a projection of the limit.** A
global function of a stage restricted to the chart of that stage and then pulled back along the
projection of the limiting cone of the system of charts agrees with the function pulled back to
the limit and restricted to the limit chart. -/
theorem globalFunctionsChartRestriction_limitEtaleChart (hX : IsAlgebraicSpace B S hS X)
    (hI : A.ChartsBounded)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (i : A.Stages) (σ : globalFunctions B S hS (A.stage i.1).obj) :
    globalFunctionsChartRestriction B S hS (A.limitSpace hX)
        (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI) hf₀)
        (globalFunctionsMap B S hS (A.projection hX i.1) σ)
      = ((A.chartStagesConeOfChartsBounded U₀ f₀ hI).π.app (op i)).appTop.hom
          (globalFunctionsChartRestriction B S hS (A.stage i.1)
            (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i) σ) := by
  have h := A.limitGlobalFunctionsEquiv_naturality hX hI hf₀ hsurj hpb i σ
  rw [A.limitGlobalFunctionsEquiv_val hX hI hf₀ hsurj hpb,
    A.stageGlobalFunctionsEquiv_val hf₀ hsurj hpb] at h
  exact h

end LimitSituation

end AlgebraicGeometry.Space

end
