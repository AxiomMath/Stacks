module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartModuleEvaluationNaturality

/-!
# Evaluation of global sections at the charts, natural in the stage

`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_evaluationNaturality` reduces
Stacks 07SI, at arbitrary coefficients, to its two naturality hypotheses `he` and `heT` together
with the colimit and compatibility hypotheses on the systems of sections over the charts.  This
file **proves `he` and `heT`**, for the maps
`AlgebraicGeometry.Space.LimitSituation.chartStageTransition` and `.chartLimitInclusion`, and
records the consumer with both discharged.

## Main definitions

* `AlgebraicGeometry.Space.moduleSectionValue`: the value of a global section of a module on the
  small étale site at an object of the site.  It is `t.val U`, as a definition of its own.

## Main results

* `AlgebraicGeometry.Space.moduleSectionValue_sectionsMap`: the value over the source chart of a
  chart diagram of a map of global sections of the shape of Stacks 07SI — an inverse image
  followed by a comparison — is the chart section map applied to the value over the target chart.
* `AlgebraicGeometry.Space.LimitSituation.moduleSectionValue_stageTransition` and
  `.moduleSectionValue_stageProjection`: **the hypotheses `he` and `heT`**, at any chart system.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_chartColimits`: the consumer of
  the equalizer presentations with `e`, `eT`, `he` and `heT` all discharged, the maps `transU`
  and `ιU` being the chart section maps.  What is left is the colimit assertion for the system of
  sections over the relation and the compatibilities with the two restrictions, plus the colimit
  assertion `hU` for the chart system.  This is not Stacks 07SI and carries no tag.

## Implementation notes

*Why `moduleSectionValue` is a definition.*  The two equations are the composite of
`AlgebraicGeometry.Space.LimitSituation.stageTransition_eq` (resp. `stageProjection_eq`) with
`AlgebraicGeometry.Space.sectionsMap_modulePullbackSections_val`.  Written with the projection
`.val` applied to a section of `AlgebraicGeometry.Space.LimitSituation.stageModule`, that
composite is rejected by the kernel with a deterministic timeout, as recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartModuleEvaluationNaturality.lean`.  The
cause: the elaborated `.val` carries, in the implicit arguments of `Subtype.val`, the auxiliary
proof `stageModule._proof_2` of the algebraic-space property of the stage, where the generic
lemma carries `(A.stage j).property`; checking the two against each other with the transition
map and the chart both concrete is what exhausts the budget.  Stated through
`AlgebraicGeometry.Space.moduleSectionValue`, whose module argument fixes those implicit
arguments to the generic ones, the very same composite is checked at once, and the consumer
passes through it unchanged because the value lemmas of the equalizer presentations restate
through it by `rfl` at a variable section.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The value of a global section of a module on the small étale site at an object of the
site.**  See the implementation notes of this file for why this is a definition. -/
noncomputable def moduleSectionValue {Y : AlgebraicSpaces B S hS}
    (N : Modules.{u, u} B S hS Y.1 Y.2) (t : N.sections) (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    N.val.obj U :=
  t.val U

/-- `AlgebraicGeometry.Space.moduleSectionValue` is the value of the section. -/
theorem moduleSectionValue_eq_val {Y : AlgebraicSpaces B S hS}
    (N : Modules.{u, u} B S hS Y.1 Y.2) (t : N.sections) (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    moduleSectionValue N t U = t.val U :=
  rfl

/-- **The value over a chart of a map of global sections of the shape of Stacks 07SI.**  If `τ` is
an inverse image along `f` followed by a comparison `ψ`, the value of `τ σ` over the source chart
of a chart diagram `d` over `f` is the chart section map of `d` applied to the value of `σ` over
its target chart. -/
theorem moduleSectionValue_sectionsMap {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (N : Modules.{u, u} B S hS Y.1 Y.2)
    (ψ : (modulePullback B S hS f).obj M ⟶ N) (d : ChartDiagram B S hS Y.1 Z.1 f.hom)
    (τ : M.sections → N.sections)
    (hτ : ∀ σ, τ σ = SheafOfModules.sectionsMap ψ (modulePullbackSections B S hS f M σ))
    (σ : M.sections) :
    moduleSectionValue N (τ σ) (op d.U) =
      chartPullbackSectionMap B S hS f M N ψ d (moduleSectionValue M σ (op d.V)) :=
  (congrArg (fun t : N.sections => t.val (op d.U)) (hτ σ)).trans
    (sectionsMap_modulePullbackSections_val B S hS f M N ψ σ d)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)
  {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  (C : AffineChartSystem B S hS (op A.base) A.system U₀ f₀)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
  (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)

/-- **The hypothesis `he` of Stacks 07SI**: evaluation at the charts of a chart system carries the
transition map `Γ(Xᵢ, ℱᵢ) → Γ(Xⱼ, ℱⱼ)` to
`AlgebraicGeometry.Space.LimitSituation.chartStageTransition`. -/
theorem moduleSectionValue_stageTransition {i j : A.Stages} (h : i ≤ j)
    (σ : A.stageSections F₀ i) :
    moduleSectionValue (A.stageModule F₀ j) (A.stageTransition F₀ i j h σ)
        (op (A.stagesEtaleChart C hf₀ j)) =
      A.chartStageTransition C hf₀ F₀ h
        (moduleSectionValue (A.stageModule F₀ i) σ (op (A.stagesEtaleChart C hf₀ i))) :=
  moduleSectionValue_sectionsMap (A.transition h) (A.stageModule F₀ i) (A.stageModule F₀ j)
    (A.stageTransitionComparison F₀ i j h) (A.stagesChartDiagram C hf₀ h)
    (A.stageTransition F₀ i j h) (A.stageTransition_eq F₀ i j h) σ

/-- **The hypothesis `heT` of Stacks 07SI**: evaluation at the charts carries the map
`Γ(Xᵢ, ℱᵢ) → Γ(X, ℱ)` to `AlgebraicGeometry.Space.LimitSituation.chartLimitInclusion`. -/
theorem moduleSectionValue_stageProjection (LC : AffineChartSystem.LimitBridge C)
    (hX : IsAlgebraicSpace B S hS X) (i : A.Stages) (σ : A.stageSections F₀ i) :
    moduleSectionValue (A.limitModule F₀ hX) (A.stageProjection F₀ hX i σ)
        (op (A.limitEtaleChart C LC hf₀)) =
      A.chartLimitInclusion C hf₀ F₀ LC hX i
        (moduleSectionValue (A.stageModule F₀ i) σ (op (A.stagesEtaleChart C hf₀ i))) :=
  moduleSectionValue_sectionsMap (A.projection hX i.1) (A.stageModule F₀ i) (A.limitModule F₀ hX)
    (A.stageProjectionComparison F₀ hX i) (A.limitChartDiagram C hf₀ LC hX i)
    (A.stageProjection F₀ hX i) (A.stageProjection_eq F₀ hX i) σ

end AlgebraicGeometry.Space.LimitSituation

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)
  {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀}
  (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))

/-- `AlgebraicGeometry.Space.LimitSituation.chartModuleEqualizerPresentation_apply_val`, through
`AlgebraicGeometry.Space.moduleSectionValue`. -/
theorem chartModuleEqualizerPresentation_apply_moduleSectionValue
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀) (i : A.Stages)
    (σ : A.stageSections F₀ i) :
    (A.chartModuleEqualizerPresentation F₀ hf₀ hsurj hpb i σ).1
      = moduleSectionValue (A.stageModule F₀ i) σ
          (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)) :=
  A.chartModuleEqualizerPresentation_apply_val F₀ hf₀ hsurj hpb i σ

/-- `AlgebraicGeometry.Space.LimitSituation.chartLimitModuleEqualizerPresentation_apply_val`,
through `AlgebraicGeometry.Space.moduleSectionValue`. -/
theorem chartLimitModuleEqualizerPresentation_apply_moduleSectionValue
    (hX : IsAlgebraicSpace B S hS X) (hI : #A.I < B.cutoff.ord.cof)
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (σ : A.limitSections F₀ hX) :
    (A.chartLimitModuleEqualizerPresentation F₀ hf₀ hX hI hsurj hpb σ).1
      = moduleSectionValue (A.limitModule F₀ hX) σ
          (op (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI) hf₀)) :=
  A.chartLimitModuleEqualizerPresentation_apply_val F₀ hf₀ hX hI hsurj hpb σ

/-- If `a = b`, `b = g c` and `d = c`, then `a = g d`. -/
private theorem eq_trans_congr {α β : Type*} (g : α → β) {a b : β} {c d : α}
    (h₁ : a = b) (h₂ : b = g c) (h₃ : d = c) : a = g d :=
  (h₁.trans h₂).trans (congrArg g h₃.symm)

/-- **Stacks 07SI for an arbitrary module, with `he` and `heT` discharged.**  This is
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_evaluationNaturality` with `transU`
and `ιU` taken to be the chart section maps, so that its two naturality hypotheses are
`AlgebraicGeometry.Space.LimitSituation.moduleSectionValue_stageTransition` and
`.moduleSectionValue_stageProjection`.  The colimit assertions `hU` and `hR` and the
compatibilities with the restrictions to the relation remain hypotheses, so this is not
Stacks 07SI and carries no tag. -/
theorem isSectionsColimit_of_chartColimits
    (hX : IsAlgebraicSpace B S hS X) (hI : #A.I < B.cutoff.ord.cof)
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (transR : ∀ i j : A.Stages, i ≤ j →
      A.relationStageSections F₀ hf₀ hpb i → A.relationStageSections F₀ hf₀ hpb j)
    (ιR : ∀ i : A.Stages,
      A.relationStageSections F₀ hf₀ hpb i → A.relationLimitSections F₀ hf₀ hpb hX hI)
    (hpt : ∀ (i j : A.Stages) (h : i ≤ j) (y : A.chartStageSections F₀ hf₀ i),
      A.chartStageRelationRestriction F₀ hf₀ hpb rfl j
          (A.chartStageTransition (A.chartSystem U₀ f₀) hf₀ F₀ h y)
        = transR i j h (A.chartStageRelationRestriction F₀ hf₀ hpb rfl i y))
    (hqt : ∀ (i j : A.Stages) (h : i ≤ j) (y : A.chartStageSections F₀ hf₀ i),
      A.chartStageRelationRestriction F₀ hf₀ hpb hpb.w.symm j
          (A.chartStageTransition (A.chartSystem U₀ f₀) hf₀ F₀ h y)
        = transR i j h (A.chartStageRelationRestriction F₀ hf₀ hpb hpb.w.symm i y))
    (hpi : ∀ (i : A.Stages) (y : A.chartStageSections F₀ hf₀ i),
      A.chartLimitRelationRestriction F₀ hf₀ hpb hX hI rfl
          (A.chartLimitInclusion (A.chartSystem U₀ f₀) hf₀ F₀ (A.chartLimitBridge U₀ f₀ hI) hX i y)
        = ιR i (A.chartStageRelationRestriction F₀ hf₀ hpb rfl i y))
    (hqi : ∀ (i : A.Stages) (y : A.chartStageSections F₀ hf₀ i),
      A.chartLimitRelationRestriction F₀ hf₀ hpb hX hI hpb.w.symm
          (A.chartLimitInclusion (A.chartSystem U₀ f₀) hf₀ F₀ (A.chartLimitBridge U₀ f₀ hI) hX i y)
        = ιR i (A.chartStageRelationRestriction F₀ hf₀ hpb hpb.w.symm i y))
    (hU : Stacks.IsStagesColimit
      (fun _ _ h => A.chartStageTransition (A.chartSystem U₀ f₀) hf₀ F₀ h)
      (fun i =>
        A.chartLimitInclusion (A.chartSystem U₀ f₀) hf₀ F₀ (A.chartLimitBridge U₀ f₀ hI) hX i))
    (hR : Stacks.IsStagesColimit transR ιR) :
    A.IsSectionsColimit F₀ hX :=
  A.isSectionsColimit_of_equalizerPresentation F₀ hX hpt hqt hpi hqi
    (A.chartModuleEqualizerPresentation F₀ hf₀ hsurj hpb)
    (A.chartLimitModuleEqualizerPresentation F₀ hf₀ hX hI hsurj hpb)
    (fun i j h σ =>
      eq_trans_congr (A.chartStageTransition (A.chartSystem U₀ f₀) hf₀ F₀ h)
        (A.chartModuleEqualizerPresentation_apply_moduleSectionValue F₀ hf₀ hsurj hpb j
          (A.stageTransition F₀ i j h σ))
        (A.moduleSectionValue_stageTransition (A.chartSystem U₀ f₀) hf₀ F₀ h σ)
        (A.chartModuleEqualizerPresentation_apply_moduleSectionValue F₀ hf₀ hsurj hpb i σ))
    (fun i σ =>
      eq_trans_congr
        (A.chartLimitInclusion (A.chartSystem U₀ f₀) hf₀ F₀ (A.chartLimitBridge U₀ f₀ hI) hX i)
        (A.chartLimitModuleEqualizerPresentation_apply_moduleSectionValue F₀ hf₀ hX hI hsurj hpb
          (A.stageProjection F₀ hX i σ))
        (A.moduleSectionValue_stageProjection (A.chartSystem U₀ f₀) hf₀ F₀
          (A.chartLimitBridge U₀ f₀ hI) hX i σ)
        (A.chartModuleEqualizerPresentation_apply_moduleSectionValue F₀ hf₀ hsurj hpb i σ))
    hU hR

end AlgebraicGeometry.Space.LimitSituation

end
