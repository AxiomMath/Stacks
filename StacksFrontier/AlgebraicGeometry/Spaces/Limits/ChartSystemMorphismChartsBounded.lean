module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedRelationSystemSupplement

/-!
# The equalizer presentation of Stacks 07SI over a chart, under `ChartsBounded`

`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartSystemMorphism.lean` reindexes the morphism of
chart systems induced by a morphism of affine scheme-valued points by the stages of a limit
situation, and reduces the assertion of Stacks 07SI to equalizer presentations of the groups of
global sections over the chart system of an affine point and the chart system of its relation.
There the limits of the chart systems are taken under the size bound `#I < cof(ord(cutoff))` on
the index category.

This file restates that development under the weaker size bound
`AlgebraicGeometry.Space.LimitSituation.ChartsBounded` on the chart systems of the stages, through
the limit bridge `AlgebraicGeometry.Space.LimitSituation.chartLimitBridgeOfChartsBounded`.  Each
declaration carries the name of the one it generalizes with the suffix `_of_chartsBounded` (or
`OfChartsBounded` for a definition).

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.chartStagesConeOfChartsBounded`: a limiting cone over
  the system of charts of the stages, from the limit of the chart system of Stacks 07SF.
* `AlgebraicGeometry.Space.LimitSituation.chartStagesRestrictionLimitOfChartsBounded`: restriction
  of a global function at the limit along the comparison of the two limits.

## Main results

* `LimitSituation.isSectionsColimit_of_equalizerPresentation_of_relationChart_of_chartsBounded`:
  the assertion of Stacks 07SI follows from equalizer presentations of its groups of global
  sections over the chart system of an affine point and the chart system of its relation.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

universe v u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace AlgebraicGeometry

namespace Space

namespace LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X) {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶ A.system.obj (op A.base)}
  {τ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (E : AffineChartSystem B S hS (op A.base) A.system R₀ g₀)

/-! ### The equalizer presentation of Stacks 07SI over a chart and its relation -/

section Relation

variable (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)

variable (V : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ A.system.obj (op A.base))

/-- **A limiting cone over that system**, from the limit of the chart system of Stacks 07SF. -/
noncomputable def chartStagesConeOfChartsBounded (hI : A.ChartsBounded) :
    Cone (A.chartStagesDiagram V g) :=
  stagesSchemeCone A (A.chartSystem V g) (A.chartLimitBridgeOfChartsBounded V g hI)

/-- **That cone is limiting.** -/
noncomputable def isLimit_chartStagesConeOfChartsBounded (hI : A.ChartsBounded) :
    IsLimit (A.chartStagesConeOfChartsBounded V g hI) :=
  isLimit_stagesSchemeCone A (A.chartSystem V g) (A.chartLimitBridgeOfChartsBounded V g hI)

/-- **Restriction of a global function at the limit along the comparison of the two limits.**
This is `AlgebraicGeometry.appTopHomLimit` of
`AlgebraicGeometry.Space.LimitSituation.stagesSchemeHom`; taken at the two projections of the
relation of a chart it is the pair `p'`, `q'` of the equalizer presentation of Stacks 07SI. -/
noncomputable def chartStagesRestrictionLimitOfChartsBounded (hτ : τ ≫ f₀ = g₀)
    (hI : A.ChartsBounded) :
    (Γ((A.chartStagesConeOfChartsBounded U₀ f₀ hI).pt, ⊤) : Type u) →
      (Γ((A.chartStagesConeOfChartsBounded R₀ g₀ hI).pt, ⊤) : Type u) :=
  appTopHomLimit (stagesSchemeHom A (A.chartSystem U₀ f₀) (A.chartSystem R₀ g₀) hτ)
    (A.isLimit_chartStagesConeOfChartsBounded U₀ f₀ hI) (A.chartStagesConeOfChartsBounded R₀ g₀ hI)

/-- **The restriction at the limit is compatible with the projections of the two cones.**  It is
the hypothesis `hpi`, or `hqi`, of
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation_of_isAffine`. -/
theorem chartStagesRestrictionLimit_π_of_chartsBounded (hτ : τ ≫ f₀ = g₀) (hI : A.ChartsBounded)
    (i : A.Stages) (x : Γ((A.chartStagesDiagram U₀ f₀).obj (op i), ⊤)) :
    A.chartStagesRestrictionLimitOfChartsBounded hτ hI
        (((A.chartStagesConeOfChartsBounded U₀ f₀ hI).π.app (op i)).appTop.hom x)
      = ((A.chartStagesConeOfChartsBounded R₀ g₀ hI).π.app (op i)).appTop.hom
          (A.chartStagesRestriction hτ i x) :=
  appTopHomLimit_π _ (A.isLimit_chartStagesConeOfChartsBounded U₀ f₀ hI)
    (A.chartStagesConeOfChartsBounded R₀ g₀ hI) i x

/-- **The assertion of Stacks 07SI follows from equalizer presentations of its groups of global
sections over the chart system of an affine point and the chart system of its relation**, with no
compatibility and no colimit assertion left as a hypothesis.

Let `U₀ ⟶ X₀` be an affine scheme-valued point of the chosen stage whose relation
`R₀ = U₀ ×_{X₀} U₀` is again affine — which at a separated stage is
`AlgebraicGeometry.Space.LimitSituation.exists_affine_relationChart_of_isAbsolutelySeparated` —
and let `t` and `yoneda s` be its two projections.  Both are morphisms over `X₀`, so each induces
a restriction map `Γ(Uᵢ, ⊤) → Γ(Rᵢ, ⊤)`; if `Γ(Xᵢ, ℱᵢ)` is in bijection with the equalizer of the
two, and `Γ(X, ℱ)` with the equalizer of the two maps at the limit, compatibly with the transition
maps and the projections, then `Γ(X, ℱ)` is the filtered colimit of the `Γ(Xᵢ, ℱᵢ)`.

This is
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation_of_isAffine`
with its two systems of schemes taken to be the two chart systems, its cones taken to be their
limits of Stacks 07SF, and all four of its compatibilities discharged by
`AlgebraicGeometry.Space.LimitSituation.chartStagesRestriction_map` and
`.chartStagesRestrictionLimit_π_of_chartsBounded`, that is, by the naturality in the stage of the
induced map of charts.  What remains hypothetical is exactly the stagewise equalizer
presentation `e` and its form `eT` at the limit, which is the content of Stacks 07SG and
Stacks 03M8 and is **not proved here**; this statement is therefore not the tag.

**The two remaining hypotheses restrict the coefficients, and the restriction is not visible in
the signature.**  The module `F₀` is an arbitrary object of `Modules`, but `e` presents its
sections as an equalizer of sections of `Γ(Uᵢ, ⊤)` — the *structure* sheaf of the chart, not of
any pullback of `F₀`.  So `e` is satisfiable only for an `F₀` whose stagewise sections are those
of the structure sheaf, which is the case Stacks 07SQ consumes and the case
`AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivEqualizer` supplies; for a general `F₀`
— already for `F₀ = 0` over a chart with nonzero sections — it cannot be satisfied and this
statement is vacuous rather than false.  Stacks 07SI at general quasi-coherent coefficients
therefore needs a differently shaped consumer, whose equalizer is taken over the sections of the
pullback of `F₀` to the chart system; it is not an instance of this one. -/
theorem isSectionsColimit_of_equalizerPresentation_of_relationChart_of_chartsBounded
    (hX : IsAlgebraicSpace B S hS X) (hI : A.ChartsBounded)
    (f₀' : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base))
    {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
      yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
    {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶
      (BigAffineFppf.inclusion B S hS).obj U₀}
    (hpb : IsPullback t (yoneda.map s) f₀' f₀')
    (e : ∀ i : A.Stages, A.stageSections F₀ i ≃
      {x : Γ((A.chartStagesDiagram U₀ f₀').obj (op i), ⊤) //
        A.chartStagesRestriction (τ := t) (f₀ := f₀') rfl i x
          = A.chartStagesRestriction (τ := yoneda.map s) hpb.w.symm i x})
    (eT : A.limitSections F₀ hX ≃
      {x : Γ((A.chartStagesConeOfChartsBounded U₀ f₀' hI).pt, ⊤) //
        A.chartStagesRestrictionLimitOfChartsBounded (τ := t) (f₀ := f₀') rfl hI x
          = A.chartStagesRestrictionLimitOfChartsBounded (τ := yoneda.map s) hpb.w.symm hI x})
    (he : ∀ (i j : A.Stages) (h : i ≤ j) (σ : A.stageSections F₀ i),
      (e j (A.stageTransition F₀ i j h σ)).1
        = ((A.chartStagesDiagram U₀ f₀').map (homOfLE h).op).appTop.hom (e i σ).1)
    (heT : ∀ (i : A.Stages) (σ : A.stageSections F₀ i),
      (eT (A.stageProjection F₀ hX i σ)).1
        = ((A.chartStagesConeOfChartsBounded U₀ f₀' hI).π.app (op i)).appTop.hom (e i σ).1) :
    A.IsSectionsColimit F₀ hX :=
  have : ∀ a, IsAffine ((A.chartStagesDiagram U₀ f₀').obj a) :=
    A.isAffine_chartStagesDiagram_obj U₀ f₀'
  have : ∀ a, IsAffine ((A.chartStagesDiagram R₀ (t ≫ f₀')).obj a) :=
    A.isAffine_chartStagesDiagram_obj R₀ (t ≫ f₀')
  A.isSectionsColimit_of_equalizerPresentation_of_isAffine F₀ hX _ _
    (A.isLimit_chartStagesConeOfChartsBounded U₀ f₀' hI)
    (A.isLimit_chartStagesConeOfChartsBounded R₀ (t ≫ f₀') hI)
    (A.chartStagesRestriction_map (τ := t) (f₀ := f₀') rfl)
    (A.chartStagesRestriction_map (τ := yoneda.map s) hpb.w.symm)
    (A.chartStagesRestrictionLimit_π_of_chartsBounded (τ := t) (f₀ := f₀') rfl hI)
    (A.chartStagesRestrictionLimit_π_of_chartsBounded (τ := yoneda.map s) hpb.w.symm hI) e eT he heT

end Relation

end LimitSituation

end Space

end AlgebraicGeometry

end
