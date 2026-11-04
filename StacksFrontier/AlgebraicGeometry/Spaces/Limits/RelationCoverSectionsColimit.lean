module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartModuleEvaluationValue
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RelationCoverSystem

/-!
# Stacks 07SI over a cover of the relation

`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_chartColimits` reduces Stacks 07SI
to colimit assertions over the chart system `Uᵢ` of an affine chart `U₀ ⟶ X₀` and over the system
`Rᵢ` of its relation `R₀ = U₀ ×_{X₀} U₀`.  The relation is affine only when `X₀` is separated.
This file replaces it by the chart system `Wᵢ` of an affine scheme `W₀` covering the relation, as
produced by `AlgebraicGeometry.Space.LimitSituation.exists_relationCover_stages_limit`; both
systems are then systems of affine charts.

## Main definitions

* `AlgebraicGeometry.Space.moduleSectionsEquivCoverEqualizer`: for an étale chart `U` of an
  algebraic space surjective on points and two maps `a, b : W ⟶ U` along which every section
  glues, the global sections of a module are the sections over `U` equalized by `a` and `b`.
* `AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivCoverEqualizer` and
  `.limitSectionsEquivCoverEqualizer`: that presentation at the stages and at the limit.

## Main results

* `AlgebraicGeometry.Space.moduleSections_ext_of_isSurjective`: a global section of a module is
  determined by its value on an étale chart surjective on points.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_coverColimits`: the consumer of
  the two presentations, with the equalizer presentations and their naturality discharged.  What
  remains is the compatibility of the restrictions to `Wᵢ` with the transition maps, and the two
  colimit assertions for the chart systems `Uᵢ` and `Wᵢ`.  This is not Stacks 07SI and carries no
  tag.

## Implementation notes

The value of a global section on a chart is written with
`AlgebraicGeometry.Space.moduleSectionValue` throughout, and the presentations are built for a
module that is a variable and only then instantiated; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartModuleEvaluationValue.lean` for the kernel
behaviour this avoids.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The presentation over a cover of the relation, for a module that is a variable -/

section Generic

variable {Y : AlgebraicSpaces B S hS} (N : Modules.{u, u} B S hS Y.1 Y.2)

/-- **A global section of a module is determined by its value on an étale chart surjective on
points.**  This is the injectivity half of Stacks 03M8,
`AlgebraicGeometry.Space.moduleSectionsEquivEqualizer`, at a self fibre product of the chart. -/
theorem moduleSections_ext_of_isSurjective {U : SmallEtale B S hS Y.1}
    (hU : IsSurjective B S hS U.1.hom) {σ τ : N.sections}
    (h : moduleSectionValue N σ (op U) = moduleSectionValue N τ (op U)) : σ = τ := by
  obtain ⟨R, p, q, hR⟩ := exists_etaleChart_isPullback_self B S hS Y
    (SpacesEtale.idObj B S hS Y) U ((SpacesEtale.isTerminal_idObj B S hS Y).from _)
  exact (moduleSectionsEquivEqualizer B S hS N hU hR).injective (Subtype.ext
    ((moduleSectionsEquivEqualizer_apply_val B S hS N hU hR σ).trans
      (h.trans (moduleSectionsEquivEqualizer_apply_val B S hS N hU hR τ).symm)))

/-- The value of a global section on a chart restricts to its value on another chart. -/
theorem moduleSectionValue_map {U W : SmallEtale B S hS Y.1} (a : W ⟶ U) (σ : N.sections) :
    (moduleSetSheaf B S hS Y N).obj.map a.op (moduleSectionValue N σ (op U))
      = moduleSectionValue N σ (op W) :=
  σ.property a.op

/-- **The global sections of a module, presented over a cover of the relation of a chart.**  Let
`U` be an étale chart of `Y`, surjective on points, and let `a, b : W ⟶ U` be two maps of charts
such that every section over `U` with equal restrictions along `a` and `b` is the value of a
global section.  Then evaluation at `U` identifies the global sections of `N` with the sections
over `U` equalized by `a` and `b`. -/
noncomputable def moduleSectionsEquivCoverEqualizer {U W : SmallEtale B S hS Y.1}
    (hU : IsSurjective B S hS U.1.hom) (a b : W ⟶ U)
    (hglue : ∀ x : (moduleSetSheaf B S hS Y N).obj.obj (op U),
      (moduleSetSheaf B S hS Y N).obj.map a.op x = (moduleSetSheaf B S hS Y N).obj.map b.op x →
        ∃ σ : N.sections, σ.val (op U) = x) :
    N.sections ≃ {x : (moduleSetSheaf B S hS Y N).obj.obj (op U) //
      (moduleSetSheaf B S hS Y N).obj.map a.op x = (moduleSetSheaf B S hS Y N).obj.map b.op x} :=
  Equiv.ofBijective
    (fun σ => ⟨moduleSectionValue N σ (op U),
      (moduleSectionValue_map N a σ).trans (moduleSectionValue_map N b σ).symm⟩)
    ⟨fun _ _ h => moduleSections_ext_of_isSurjective N hU (congrArg Subtype.val h),
      fun x => let ⟨σ, hσ⟩ := hglue x.1 x.2; ⟨σ, Subtype.ext hσ⟩⟩

/-- The presentation over a cover of the relation is evaluation at the chart. -/
theorem moduleSectionsEquivCoverEqualizer_apply {U W : SmallEtale B S hS Y.1}
    (hU : IsSurjective B S hS U.1.hom) (a b : W ⟶ U)
    (hglue : ∀ x : (moduleSetSheaf B S hS Y N).obj.obj (op U),
      (moduleSetSheaf B S hS Y N).obj.map a.op x = (moduleSetSheaf B S hS Y N).obj.map b.op x →
        ∃ σ : N.sections, σ.val (op U) = x) (σ : N.sections) :
    (moduleSectionsEquivCoverEqualizer N hU a b hglue σ).1 = moduleSectionValue N σ (op U) :=
  rfl

end Generic

namespace LimitSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)
  {U₀ W₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {g₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶ A.system.obj (op A.base)}
  {t v : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)
  (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
  (hg₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk g₀))
  (ht : t ≫ f₀ = g₀) (hv : v ≫ f₀ = g₀)

/-- **The restriction `ℱᵢ(Uᵢ) → ℱᵢ(Wᵢ)` along one of the two maps of charts** induced by a
morphism `τ : W₀ ⟶ U₀` over `X₀`. -/
noncomputable def chartStageCoverRestriction {τ : _} (hτ : τ ≫ f₀ = g₀) (i : A.Stages) :
    A.chartStageSections F₀ hf₀ i → A.chartStageSections F₀ hg₀ i :=
  (moduleSetSheaf B S hS (A.stage i.1) (A.stageModule F₀ i)).obj.map
    (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ hτ i).op

/-- **The restriction `ℱ(U) → ℱ(W)` at the limit along one of the two maps of limit charts**
induced by a morphism `τ : W₀ ⟶ U₀` over `X₀`. -/
noncomputable def chartLimitCoverRestriction (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) {τ : _} (hτ : τ ≫ f₀ = g₀) :
    A.chartLimitSections F₀ hf₀ hX hI → A.chartLimitSections F₀ hg₀ hX hI :=
  (moduleSetSheaf B S hS (A.limitSpace hX) (A.limitModule F₀ hX)).obj.map
    (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
      (A.chartSystem W₀ g₀) (A.chartLimitBridge W₀ g₀ hI) hf₀ hg₀ hτ).op

/-- **The stagewise presentation over a cover of the relation**:
`Γ(Xᵢ, ℱᵢ) ≃ {x : ℱᵢ(Uᵢ) // a^*x = b^*x}` for the two maps `a, b : Wᵢ ⟶ Uᵢ`, given the gluing
property `hglue` of `AlgebraicGeometry.Space.LimitSituation.exists_relationCover_stages_limit`. -/
noncomputable def stageSectionsEquivCoverEqualizer (hsurj : IsSurjective B S hS f₀)
    (hglue : ∀ (i : A.Stages) (N : Modules.{u, u} B S hS (A.stage i.1).obj (A.stage i.1).property)
      (x : (moduleSetSheaf B S hS (A.stage i.1) N).obj.obj
        (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i))),
      (moduleSetSheaf B S hS (A.stage i.1) N).obj.map
          (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ ht i).op x =
        (moduleSetSheaf B S hS (A.stage i.1) N).obj.map
          (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ hv i).op x →
      ∃ σ : N.sections, σ.val (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)) = x)
    (i : A.Stages) :
    A.stageSections F₀ i ≃ {x : A.chartStageSections F₀ hf₀ i //
      A.chartStageCoverRestriction F₀ hf₀ hg₀ ht i x
        = A.chartStageCoverRestriction F₀ hf₀ hg₀ hv i x} :=
  moduleSectionsEquivCoverEqualizer (A.stageModule F₀ i)
    (A.isSurjective_stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ hsurj i) _ _
    (hglue i (A.stageModule F₀ i))

/-- The stagewise presentation over a cover of the relation is evaluation at the chart. -/
theorem stageSectionsEquivCoverEqualizer_apply (hsurj : IsSurjective B S hS f₀)
    (hglue : ∀ (i : A.Stages) (N : Modules.{u, u} B S hS (A.stage i.1).obj (A.stage i.1).property)
      (x : (moduleSetSheaf B S hS (A.stage i.1) N).obj.obj
        (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i))),
      (moduleSetSheaf B S hS (A.stage i.1) N).obj.map
          (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ ht i).op x =
        (moduleSetSheaf B S hS (A.stage i.1) N).obj.map
          (A.stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀ (A.chartSystem W₀ g₀) hg₀ hv i).op x →
      ∃ σ : N.sections, σ.val (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)) = x)
    (i : A.Stages) (σ : A.stageSections F₀ i) :
    (A.stageSectionsEquivCoverEqualizer F₀ hf₀ hg₀ ht hv hsurj hglue i σ).1
      = moduleSectionValue (A.stageModule F₀ i) σ
          (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)) :=
  moduleSectionsEquivCoverEqualizer_apply _ _ _ _ _ σ

/-- **The presentation over a cover of the relation at the limit**:
`Γ(X, ℱ) ≃ {x : ℱ(U) // a^*x = b^*x}` for the two maps of limit charts `a, b : W ⟶ U`. -/
noncomputable def limitSectionsEquivCoverEqualizer (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) (hsurj : IsSurjective B S hS f₀)
    (hglue : ∀ (N : Modules.{u, u} B S hS (A.limitSpace hX).obj (A.limitSpace hX).property)
      (x : (moduleSetSheaf B S hS (A.limitSpace hX) N).obj.obj
        (op (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI) hf₀))),
      (moduleSetSheaf B S hS (A.limitSpace hX) N).obj.map
          (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
            (A.chartSystem W₀ g₀) (A.chartLimitBridge W₀ g₀ hI) hf₀ hg₀ ht).op x =
        (moduleSetSheaf B S hS (A.limitSpace hX) N).obj.map
          (A.limitEtaleChartMap (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI)
            (A.chartSystem W₀ g₀) (A.chartLimitBridge W₀ g₀ hI) hf₀ hg₀ hv).op x →
      ∃ σ : N.sections, σ.val (op (A.limitEtaleChart (A.chartSystem U₀ f₀)
        (A.chartLimitBridge U₀ f₀ hI) hf₀)) = x) :
    A.limitSections F₀ hX ≃ {x : A.chartLimitSections F₀ hf₀ hX hI //
      A.chartLimitCoverRestriction F₀ hf₀ hg₀ hX hI ht x
        = A.chartLimitCoverRestriction F₀ hf₀ hg₀ hX hI hv x} :=
  moduleSectionsEquivCoverEqualizer (A.limitModule F₀ hX)
    (A.isSurjective_limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI) hf₀
      hsurj) _ _ (hglue (A.limitModule F₀ hX))

/-- The presentation over a cover of the relation at the limit is evaluation at the chart. -/
theorem limitSectionsEquivCoverEqualizer_apply (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) (hsurj : IsSurjective B S hS f₀)
    (hglue : ∀ (N : Modules.{u, u} B S hS (A.limitSpace hX).obj (A.limitSpace hX).property)
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
    (σ : A.limitSections F₀ hX) :
    (A.limitSectionsEquivCoverEqualizer F₀ hf₀ hg₀ ht hv hX hI hsurj hglue σ).1
      = moduleSectionValue (A.limitModule F₀ hX) σ
          (op (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridge U₀ f₀ hI) hf₀)) :=
  moduleSectionsEquivCoverEqualizer_apply _ _ _ _ _ σ

/-- **Stacks 07SI for an arbitrary module, over a cover of the relation, with the equalizer
presentations and their naturality discharged.**  Let `U₀ ⟶ X₀` be an affine étale chart
surjective on points and `W₀ ⟶ X₀` an affine étale chart with two maps `t, v : W₀ ⟶ U₀` over
`X₀` along which sections glue at every stage and at the limit (`hglue`, `hglueX`), as produced
by `AlgebraicGeometry.Space.LimitSituation.exists_relationCover_stages_limit`.  If the
restrictions from the charts `Uᵢ` to the charts `Wᵢ` commute with the chart section maps
(`hpt`, `hqt`, `hpi`, `hqi`), and if the sections over the two chart systems are filtered
colimits (`hU`, `hW`), then `Γ(X, ℱ)` is the filtered colimit of the `Γ(Xᵢ, ℱᵢ)`.

This is `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_equalizerPresentation` with
the presentations
`AlgebraicGeometry.Space.LimitSituation.stageSectionsEquivCoverEqualizer` and
`.limitSectionsEquivCoverEqualizer`, and with its naturality hypotheses discharged by
`AlgebraicGeometry.Space.LimitSituation.moduleSectionValue_stageTransition` and
`.moduleSectionValue_stageProjection`.  It carries no tag: `hpt` to `hqi`, `hU` and `hW` are
hypotheses. -/
theorem isSectionsColimit_of_coverColimits (hX : IsAlgebraicSpace B S hS X)
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
    (hpt : ∀ (i j : A.Stages) (h : i ≤ j) (y : A.chartStageSections F₀ hf₀ i),
      A.chartStageCoverRestriction F₀ hf₀ hg₀ ht j
          (A.chartStageTransition (A.chartSystem U₀ f₀) hf₀ F₀ h y)
        = A.chartStageTransition (A.chartSystem W₀ g₀) hg₀ F₀ h
          (A.chartStageCoverRestriction F₀ hf₀ hg₀ ht i y))
    (hqt : ∀ (i j : A.Stages) (h : i ≤ j) (y : A.chartStageSections F₀ hf₀ i),
      A.chartStageCoverRestriction F₀ hf₀ hg₀ hv j
          (A.chartStageTransition (A.chartSystem U₀ f₀) hf₀ F₀ h y)
        = A.chartStageTransition (A.chartSystem W₀ g₀) hg₀ F₀ h
          (A.chartStageCoverRestriction F₀ hf₀ hg₀ hv i y))
    (hpi : ∀ (i : A.Stages) (y : A.chartStageSections F₀ hf₀ i),
      A.chartLimitCoverRestriction F₀ hf₀ hg₀ hX hI ht
          (A.chartLimitInclusion (A.chartSystem U₀ f₀) hf₀ F₀ (A.chartLimitBridge U₀ f₀ hI) hX i y)
        = A.chartLimitInclusion (A.chartSystem W₀ g₀) hg₀ F₀ (A.chartLimitBridge W₀ g₀ hI) hX i
          (A.chartStageCoverRestriction F₀ hf₀ hg₀ ht i y))
    (hqi : ∀ (i : A.Stages) (y : A.chartStageSections F₀ hf₀ i),
      A.chartLimitCoverRestriction F₀ hf₀ hg₀ hX hI hv
          (A.chartLimitInclusion (A.chartSystem U₀ f₀) hf₀ F₀ (A.chartLimitBridge U₀ f₀ hI) hX i y)
        = A.chartLimitInclusion (A.chartSystem W₀ g₀) hg₀ F₀ (A.chartLimitBridge W₀ g₀ hI) hX i
          (A.chartStageCoverRestriction F₀ hf₀ hg₀ hv i y))
    (hU : Stacks.IsStagesColimit
      (fun i j h => A.chartStageTransition (A.chartSystem U₀ f₀) hf₀ F₀ (i := i) (j := j) h)
      (fun i => A.chartLimitInclusion (A.chartSystem U₀ f₀) hf₀ F₀
        (A.chartLimitBridge U₀ f₀ hI) hX i))
    (hW : Stacks.IsStagesColimit
      (fun i j h => A.chartStageTransition (A.chartSystem W₀ g₀) hg₀ F₀ (i := i) (j := j) h)
      (fun i => A.chartLimitInclusion (A.chartSystem W₀ g₀) hg₀ F₀
        (A.chartLimitBridge W₀ g₀ hI) hX i)) :
    A.IsSectionsColimit F₀ hX :=
  A.isSectionsColimit_of_equalizerPresentation F₀ hX hpt hqt hpi hqi
    (A.stageSectionsEquivCoverEqualizer F₀ hf₀ hg₀ ht hv hsurj hglue)
    (A.limitSectionsEquivCoverEqualizer F₀ hf₀ hg₀ ht hv hX hI hsurj (hglueX))
    (fun i j h σ =>
      ((A.stageSectionsEquivCoverEqualizer_apply F₀ hf₀ hg₀ ht hv hsurj hglue j
            (A.stageTransition F₀ i j h σ)).trans
          (A.moduleSectionValue_stageTransition (A.chartSystem U₀ f₀) hf₀ F₀ h σ)).trans
        (congrArg (A.chartStageTransition (A.chartSystem U₀ f₀) hf₀ F₀ h)
          (A.stageSectionsEquivCoverEqualizer_apply F₀ hf₀ hg₀ ht hv hsurj hglue i σ).symm))
    (fun i σ =>
      ((A.limitSectionsEquivCoverEqualizer_apply F₀ hf₀ hg₀ ht hv hX hI hsurj hglueX
            (A.stageProjection F₀ hX i σ)).trans
          (A.moduleSectionValue_stageProjection (A.chartSystem U₀ f₀) hf₀ F₀
            (A.chartLimitBridge U₀ f₀ hI) hX i σ)).trans
        (congrArg (A.chartLimitInclusion (A.chartSystem U₀ f₀) hf₀ F₀
            (A.chartLimitBridge U₀ f₀ hI) hX i)
          (A.stageSectionsEquivCoverEqualizer_apply F₀ hf₀ hg₀ ht hv hsurj hglue i σ).symm))
    hU hW

end LimitSituation

end AlgebraicGeometry.Space

end
