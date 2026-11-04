module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelationCoverSectionsColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionPushforwardComparison

/-!
# The chart section maps of Stacks 07SI commute with restriction along induced maps of charts

`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_coverColimits` carries four
compatibilities `hpt`, `hqt`, `hpi`, `hqi`: the restrictions from the charts `Uᵢ` to the charts
`Wᵢ` along the maps induced by a morphism `W₀ ⟶ U₀` over `X₀` commute with the chart section maps
`AlgebraicGeometry.Space.LimitSituation.chartStageTransition` and `.chartLimitInclusion`.  This
file proves all four, and records the consumer with them discharged.

## Main results

* `AlgebraicGeometry.Space.chartPullbackSectionMap_naturality`: the chart section map of a
  morphism out of an inverse image is natural in the chart diagram.  This is
  `AlgebraicGeometry.Space.modulePullbackChartSection_naturality` followed by the naturality of
  the morphism.
* `AlgebraicGeometry.Space.LimitSituation.chartStageCoverRestriction_chartStageTransition` and
  `.chartLimitCoverRestriction_chartLimitInclusion`: the four compatibilities.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_coverChartColimits`: Stacks 07SI
  for an arbitrary module over a cover of the relation, with only the two colimit assertions `hU`
  and `hW` for the chart systems left.  It carries no tag.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_chartSystemColimits`: Stacks 07SI
  reduced to the colimit assertion for the sections over a single affine chart system, with the
  charts chosen.  It carries no tag.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The chart section map of a morphism out of an inverse image is natural in the chart
diagram.**  If `i : U' ⟶ U` and `j : V' ⟶ V` are maps of charts compatible with two chart
diagrams `d'` and `d` over `f`, then restricting along `i` after the chart section map of `d` is
the chart section map of `d'` after restricting along `j`. -/
theorem chartPullbackSectionMap_naturality {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (N : Modules.{u, u} B S hS Y.1 Y.2)
    (ψ : (modulePullback B S hS f).obj M ⟶ N) (d d' : ChartDiagram B S hS Y.1 Z.1 f.hom)
    (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (hcond : (SmallEtale.toOver B S hS Y.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS Z.1).map j)
    (y : M.val.obj (op d.V)) :
    N.val.map i.op (chartPullbackSectionMap B S hS f M N ψ d y)
      = chartPullbackSectionMap B S hS f M N ψ d' (M.val.map j.op y) := by
  refine (PresheafOfModules.naturality_apply ψ.val i.op _).symm.trans ?_
  exact congrArg (ψ.val.app (op d'.U))
    (modulePullbackChartSection_naturality B S hS f M d d' i j hcond y).symm

namespace LimitSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)
  {U₀ W₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶ A.system.obj (op A.base)}
  (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
  (hg₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk g₀))

/-- **The stagewise compatibilities `hpt` and `hqt`**: restriction from `Uⱼ` to `Wⱼ` after the
chart section map `ℱᵢ(Uᵢ) → ℱⱼ(Uⱼ)` is the chart section map `ℱᵢ(Wᵢ) → ℱⱼ(Wⱼ)` after restriction
from `Uᵢ` to `Wᵢ`.  The square of charts is
`AlgebraicGeometry.Space.AffineChartSystem.inducedMap_naturality`. -/
theorem chartStageCoverRestriction_chartStageTransition {τ : _} (hτ : τ ≫ f₀ = g₀)
    {i j : A.Stages} (h : i ≤ j) (y : A.chartStageSections F₀ hf₀ i) :
    A.chartStageCoverRestriction F₀ hf₀ hg₀ hτ j
        (A.chartStageTransition (A.chartSystem U₀ f₀) hf₀ F₀ h y)
      = A.chartStageTransition (A.chartSystem W₀ g₀) hg₀ F₀ h
          (A.chartStageCoverRestriction F₀ hf₀ hg₀ hτ i y) :=
  chartPullbackSectionMap_naturality (A.transition h) (A.stageModule F₀ i) (A.stageModule F₀ j)
    (A.stageTransitionComparison F₀ i j h) (A.stagesChartDiagram (A.chartSystem U₀ f₀) hf₀ h)
    (A.stagesChartDiagram (A.chartSystem W₀ g₀) hg₀ h)
    (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ hτ j)
    (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ hτ i)
    ((A.chartSystem U₀ f₀).inducedMap_naturality (A.chartSystem W₀ g₀) hτ
      ((stagesOverEquivalence A).functor.map (homOfLE h).op)).symm y

/-- **The compatibilities `hpi` and `hqi` at the limit**: restriction from `U` to `W` after the
chart section map `ℱᵢ(Uᵢ) → ℱ(U)` is the chart section map `ℱᵢ(Wᵢ) → ℱ(W)` after restriction
from `Uᵢ` to `Wᵢ`.  The square of charts is
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.inducedMap_comp_π`. -/
theorem chartLimitCoverRestriction_chartLimitInclusion (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) {τ : _} (hτ : τ ≫ f₀ = g₀) (i : A.Stages)
    (y : A.chartStageSections F₀ hf₀ i) :
    A.chartLimitCoverRestriction F₀ hf₀ hg₀ hX hI hτ
        (A.chartLimitInclusion (A.chartSystem U₀ f₀) hf₀ F₀ (A.chartLimitBridge U₀ f₀ hI) hX i y)
      = A.chartLimitInclusion (A.chartSystem W₀ g₀) hg₀ F₀ (A.chartLimitBridge W₀ g₀ hI) hX i
          (A.chartStageCoverRestriction F₀ hf₀ hg₀ hτ i y) :=
  chartPullbackSectionMap_naturality (A.projection hX i.1) (A.stageModule F₀ i)
    (A.limitModule F₀ hX) (A.stageProjectionComparison F₀ hX i)
    (A.limitChartDiagram (A.chartSystem U₀ f₀) hf₀ (A.chartLimitBridge U₀ f₀ hI) hX i)
    (A.limitChartDiagram (A.chartSystem W₀ g₀) hg₀ (A.chartLimitBridge W₀ g₀ hI) hX i)
    (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
      (A.chartSystem W₀ g₀) (A.chartLimitBridge W₀ g₀ hI) hf₀ hg₀ hτ)
    (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ hτ i)
    (AffineChartSystem.LimitBridge.inducedMap_comp_π (A.chartLimitBridge U₀ f₀ hI)
      (A.chartLimitBridge W₀ g₀ hI) hτ ((stagesOverEquivalence A).functor.obj (op i))) y

/-- **Stacks 07SI for an arbitrary module over a cover of the relation, with only the colimit
assertions for the two chart systems left.**  This is
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_coverColimits` with its four
compatibilities discharged by
`AlgebraicGeometry.Space.LimitSituation.chartStageCoverRestriction_chartStageTransition` and
`.chartLimitCoverRestriction_chartLimitInclusion`.  What remains is that the sections over the
chart system of `U₀` and over the chart system of `W₀` are filtered colimits (`hU`, `hW`); it
carries no tag. -/
theorem isSectionsColimit_of_coverChartColimits
    {t v : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶
      yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
    (ht : t ≫ f₀ = g₀) (hv : v ≫ f₀ = g₀) (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) (hsurj : IsSurjective B S hS f₀)
    (hglue : ∀ (i : A.Stages) (N : Modules.{u, u} B S hS (A.stage i.1).obj (A.stage i.1).property)
      (x : (moduleSetSheaf B S hS (A.stage i.1) N).obj.obj
        (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i))),
      (moduleSetSheaf B S hS (A.stage i.1) N).obj.map
          (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ ht i).op x =
        (moduleSetSheaf B S hS (A.stage i.1) N).obj.map
          (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ hv i).op x →
      ∃ σ : N.sections, σ.val (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)) = x)
    (hglueX : ∀ (N : Modules.{u, u} B S hS (A.limitSpace hX).obj (A.limitSpace hX).property)
      (x : (moduleSetSheaf B S hS (A.limitSpace hX) N).obj.obj
        (op (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI) hf₀))),
      (moduleSetSheaf B S hS (A.limitSpace hX) N).obj.map
          (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
            (A.chartSystem W₀ g₀) (A.chartLimitBridge W₀ g₀ hI) hf₀ hg₀ ht).op x =
        (moduleSetSheaf B S hS (A.limitSpace hX) N).obj.map
          (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
            (A.chartSystem W₀ g₀) (A.chartLimitBridge W₀ g₀ hI) hf₀ hg₀ hv).op x →
      ∃ σ : N.sections, σ.val (op (A.limitEtaleChart (A.chartSystem U₀ f₀)
        (A.chartLimitBridge U₀ f₀ hI) hf₀)) = x)
    (hU : Stacks.IsStagesColimit
      (fun i j h => A.chartStageTransition (A.chartSystem U₀ f₀) hf₀ F₀ (i := i) (j := j) h)
      (fun i => A.chartLimitInclusion (A.chartSystem U₀ f₀) hf₀ F₀
        (A.chartLimitBridge U₀ f₀ hI) hX i))
    (hW : Stacks.IsStagesColimit
      (fun i j h => A.chartStageTransition (A.chartSystem W₀ g₀) hg₀ F₀ (i := i) (j := j) h)
      (fun i => A.chartLimitInclusion (A.chartSystem W₀ g₀) hg₀ F₀
        (A.chartLimitBridge W₀ g₀ hI) hX i)) :
    A.IsSectionsColimit F₀ hX :=
  A.isSectionsColimit_of_coverColimits F₀ hf₀ hg₀ ht hv hX hI hsurj hglue hglueX
    (fun _ _ h y => A.chartStageCoverRestriction_chartStageTransition F₀ hf₀ hg₀ ht h y)
    (fun _ _ h y => A.chartStageCoverRestriction_chartStageTransition F₀ hf₀ hg₀ hv h y)
    (fun i y => A.chartLimitCoverRestriction_chartLimitInclusion F₀ hf₀ hg₀ hX hI ht i y)
    (fun i y => A.chartLimitCoverRestriction_chartLimitInclusion F₀ hf₀ hg₀ hX hI hv i y)
    hU hW


/-- **Stacks 07SI reduced to the colimit assertion for one affine chart system.**  If, for every
affine étale chart `V₀ ⟶ X₀` of the chosen stage, the sections of `ℱᵢ` over the charts
`Vᵢ = Xᵢ ×_{X₀} V₀` have the sections of `ℱ` over `V = X ×_{X₀} V₀` as their filtered colimit,
then `Γ(X, ℱ)` is the filtered colimit of the `Γ(Xᵢ, ℱᵢ)`.

The chart `U₀` is an affine étale chart surjective on points, by Stacks 03H6
(`AlgebraicGeometry.Space.LimitSituation.exists_affine_isSurjective_etaleChart_stage`); the cover
`W₀` of its relation is
`AlgebraicGeometry.Space.LimitSituation.exists_relationCover_stages_limit`; and the hypothesis is
used at `U₀` and at `W₀` in
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_coverChartColimits`.  Nothing about
`ℱ₀` is used beyond the hypothesis, which is where quasi-coherence enters. -/
theorem isSectionsColimit_of_chartSystemColimits (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof)
    (hchart : ∀ {V₀ : BigAffineFppf B S hS}
      {e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V₀) ⟶ A.system.obj (op A.base)}
      (he₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk e₀)),
      Stacks.IsStagesColimit
        (fun i j h => A.chartStageTransition (A.chartSystem V₀ e₀) he₀ F₀ (i := i) (j := j) h)
        (fun i => A.chartLimitInclusion (A.chartSystem V₀ e₀) he₀ F₀
          (A.chartLimitBridge V₀ e₀ hI) hX i)) :
    A.IsSectionsColimit F₀ hX := by
  obtain ⟨U₀, f₀, hf₀, hsurj⟩ :=
    LimitSituation.exists_affine_isSurjective_etaleChart_stage B S hS A A.base
  obtain ⟨W₀, g₀, hg₀, t, v, ht, hv, hglue, hglueL⟩ :=
    A.exists_relationCover_stages_limit hf₀ hsurj
  exact A.isSectionsColimit_of_coverChartColimits F₀ hf₀ hg₀ ht hv hX hI hsurj hglue
    (hglueL hX hI) (hchart hf₀) (hchart hg₀)

end LimitSituation

end AlgebraicGeometry.Space

end
