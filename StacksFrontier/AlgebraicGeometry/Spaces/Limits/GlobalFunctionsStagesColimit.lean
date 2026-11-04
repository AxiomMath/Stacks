module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitEqualizerPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemEtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSystemMorphismChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StructureSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GlobalFunctionsAtlas

/-!
# The global functions of a morphism of algebraic spaces, over a chart

`AlgebraicGeometry.Space.globalFunctionsMap` is the pullback of global regular functions along a
morphism of algebraic spaces. It is defined through
`AlgebraicGeometry.Space.globalFunctionsChartEquiv`, the identification of global functions with
compatible families of regular functions on *all* scheme charts, where it is precomposition; so
its values at an étale chart are not immediate.

This file computes them: for a commuting square of charts over the morphism, the value of the
pullback at the chart of the source is the pullback of functions along the morphism of charts.
That is the identity which makes the equalizer presentation of Stacks 03M8 natural in a morphism
of algebraic spaces, and so the identity the proof of Stacks 07SI needs of its transition maps.

## Main results

* `AlgebraicGeometry.Space.globalFunctionsMap_val_of_yoneda_map_comp`: for `m` a morphism of
  charts over `f`, the value of `globalFunctionsMap f σ` at the source chart is the restriction of
  the value of `σ` at the target chart along `m`.

## Implementation notes

The proof reads both sides through `AlgebraicGeometry.Space.globalFunctionsChartEquiv`, whose
defining property `.2` says that restricting an all-chart family back to the étale charts
recovers the global function. On all charts the pullback is precomposition
(`AlgebraicGeometry.Space.chartFunctionsMap`), so the left-hand side becomes the value of the
all-chart family of `σ` at the scheme chart `(W, W.hom ≫ f)`; the compatibility of that family
along the morphism of charts `m` turns it into the right-hand side. No property of the
equivalence beyond `.2` is used, and the equivalence is never inverted.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The value of a global function at an étale chart is the value at that chart of the all-chart
family it corresponds to. This is the defining property of
`AlgebraicGeometry.Space.globalFunctionsChartEquiv`, read at one chart. -/
theorem val_app_globalFunctionsChartEquiv (U : AlgebraicSpaces B S hS)
    (σ : globalFunctions' B S hS U.1) (W : SmallEtale B S hS U.1) :
    σ.val (op W)
      = ((globalFunctionsChartEquiv B S hS U).val σ).val
          (op ((SmallEtale.inclusion B S hS U.1).obj W)) :=
  (congrArg (fun s : globalFunctions' B S hS U.1 => s.val (op W))
    ((globalFunctionsChartEquiv B S hS U).2 σ)).symm

/-- **The chart value of the pullback of a global regular function.** Let `f : V ⟶ U` be a
morphism of algebraic spaces, let `W` be an étale chart of `V` and `W'` one of `U`, and let `m` be
a morphism of the big fppf site over the square — a morphism of charts over `f`. Then the value at
`W` of the pullback of a global function `σ` of `U` is the restriction along `m` of the value of
`σ` at `W'`. -/
theorem globalFunctionsMap_val_of_yoneda_map_comp {U V : AlgebraicSpaces B S hS} (f : V ⟶ U)
    (σ : globalFunctions' B S hS U.1) (W : SmallEtale B S hS V.1)
    (W' : SmallEtale B S hS U.1) (m : W.1.left ⟶ W'.1.left)
    (hm : yoneda.map m ≫ W'.1.hom = W.1.hom ≫ f.hom) :
    (globalFunctionsMap B S hS f σ).val (op W)
      = ((BigFppfOver.toScheme B S hS).map m).appTop.hom (σ.val (op W')) := by
  let jW : CostructuredArrow yoneda U.1 := CostructuredArrow.mk (W.1.hom ≫ f.hom)
  let jW' : CostructuredArrow yoneda U.1 := CostructuredArrow.mk W'.1.hom
  let m' : jW ⟶ jW' := CostructuredArrow.homMk m hm
  set τ := (globalFunctionsChartEquiv B S hS U).val σ
  have hlhs : (globalFunctionsMap B S hS f σ).val (op W) = τ.val (op jW) := by
    refine (val_app_globalFunctionsChartEquiv B S hS V _ W).trans ?_
    exact congrArg (fun s : chartFunctions B S hS V.1 =>
        s.val (op ((SmallEtale.inclusion B S hS V.1).obj W)))
      (globalFunctionsMap_chart B S hS f σ)
  have hrhs : τ.val (op jW)
      = ((BigFppfOver.toScheme B S hS).map m).appTop.hom (τ.val (op jW')) :=
    (τ.property m'.op).symm
  refine hlhs.trans (hrhs.trans ?_)
  exact congrArg (fun z => ((BigFppfOver.toScheme B S hS).map m).appTop.hom z)
    (val_app_globalFunctionsChartEquiv B S hS U σ W').symm

/-! ### The global functions of the stages of a limit situation -/

namespace LimitSituation

variable {B S hS} {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X) {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀}

/-- **The ring of global functions on a stage is the equalizer of the two restrictions to the
relation**, for the chart system of an affine étale chart of the chosen stage and the chart system
of its relation.

This is Stacks 03M8 for the structure sheaf,
`AlgebraicGeometry.Space.structureSectionsEquivEqualizer`, at the chart of the stage the chart
system provides; the equalized pair is the pair of restriction maps of the two reindexed systems
of schemes on the nose. -/
noncomputable def stageGlobalFunctionsEquiv
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (i : A.Stages) :
    globalFunctions' B S hS (A.stage i.1).obj ≃
      {x : (Γ((A.chartStagesDiagram U₀ f₀).obj (op i), ⊤) : Type u) //
        A.chartStagesRestriction (τ := t) (f₀ := f₀) rfl i x
          = A.chartStagesRestriction (τ := yoneda.map s) hpb.w.symm i x} :=
  structureSectionsEquivEqualizer B S hS (A.stage i.1)
    (A.isSurjective_stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ hsurj i)
    (A.isPullback_comparisonFunctor_stagesEtaleChartMap (A.chartSystem U₀ f₀) hf₀
      (A.chartSystem R₀ (t ≫ f₀)) (isEtaleChart_comp_of_isPullback hf₀ hpb) rfl hpb.w.symm hpb i)

/-- The value of that bijection is the value of the global function at the chart of the stage. -/
theorem stageGlobalFunctionsEquiv_val
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (i : A.Stages) (σ : globalFunctions' B S hS (A.stage i.1).obj) :
    (A.stageGlobalFunctionsEquiv hf₀ hsurj hpb i σ).1
      = σ.val (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)) :=
  structureSectionsEquivEqualizer_apply_val B S hS (A.stage i.1) _ _ σ

/-- **The equalizer presentation of the global functions of a stage is natural in the stage.**
The two sides are the value of the pullback of a global function at the chart of the later stage
and the restriction of its value at the chart of the earlier one; they agree by
`AlgebraicGeometry.Space.globalFunctionsMap_val_of_yoneda_map_comp` at the chart-system
transition morphism, whose triangle over the two stages is
`AlgebraicGeometry.Space.AffineChartSystem.stageMap_naturality`. -/
theorem stageGlobalFunctionsEquiv_naturality
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (i j : A.Stages) (h : i ≤ j) (σ : globalFunctions' B S hS (A.stage i.1).obj) :
    (A.stageGlobalFunctionsEquiv hf₀ hsurj hpb j
        (globalFunctionsMap B S hS (A.transition (show i.1 ≤ j.1 from h)) σ)).1
      = ((A.chartStagesDiagram U₀ f₀).map (homOfLE h).op).appTop.hom
          (A.stageGlobalFunctionsEquiv hf₀ hsurj hpb i σ).1 := by
  rw [A.stageGlobalFunctionsEquiv_val hf₀ hsurj hpb j,
    A.stageGlobalFunctionsEquiv_val hf₀ hsurj hpb i]
  exact globalFunctionsMap_val_of_yoneda_map_comp B S hS (A.transition (show i.1 ≤ j.1 from h)) σ
    (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ j)
    (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)
    ((A.chartSystem U₀ f₀).siteDiagram.map
      ((stagesOverEquivalence A).functor.map (homOfLE h).op))
    ((A.chartSystem U₀ f₀).stageMap_naturality
      ((stagesOverEquivalence A).functor.map (homOfLE h).op))

/-- **The ring of global functions on the limit is the equalizer of the two restrictions to the
limit of the relation system.**  This is Stacks 03M8 for the structure sheaf at the limit chart,
with the equalized pair identified with the restriction maps at the limit by
`AlgebraicGeometry.Space.LimitSituation.appTopHomLimit_limitEtaleChartMap`. -/
noncomputable def limitGlobalFunctionsEquiv (hX : IsAlgebraicSpace B S hS X)
    (hI : A.ChartsBounded)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀) :
    globalFunctions' B S hS (A.limitSpace hX).obj ≃
      {x : (Γ((A.chartStagesConeOfChartsBounded U₀ f₀ hI).pt, ⊤) : Type u) //
        A.chartStagesRestrictionLimitOfChartsBounded (τ := t) (f₀ := f₀) rfl hI x
          = A.chartStagesRestrictionLimitOfChartsBounded (τ := yoneda.map s) hpb.w.symm hI x} :=
  (structureSectionsEquivEqualizer B S hS (A.limitSpace hX)
        (A.isSurjective_limitEtaleChart (A.chartSystem U₀ f₀)
          (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI) hf₀ hsurj)
        (A.isPullback_comparisonFunctor_limitEtaleChartMap (A.chartSystem U₀ f₀)
          (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI) (A.chartSystem R₀ (t ≫ f₀))
          (A.chartLimitBridgeOfChartsBounded R₀ (t ≫ f₀) hI) hf₀
          (isEtaleChart_comp_of_isPullback hf₀ hpb) hX rfl hpb.w.symm hpb)).trans
    (Equiv.subtypeEquivRight fun a => iff_of_eq (congrArg₂ Eq
      (A.appTopHomLimit_limitEtaleChartMap (A.chartSystem U₀ f₀)
        (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI) (A.chartSystem R₀ (t ≫ f₀))
        (A.chartLimitBridgeOfChartsBounded R₀ (t ≫ f₀) hI) hf₀
        (isEtaleChart_comp_of_isPullback hf₀ hpb) (τ := t) rfl a)
      (A.appTopHomLimit_limitEtaleChartMap (A.chartSystem U₀ f₀)
        (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI) (A.chartSystem R₀ (t ≫ f₀))
        (A.chartLimitBridgeOfChartsBounded R₀ (t ≫ f₀) hI) hf₀
        (isEtaleChart_comp_of_isPullback hf₀ hpb) (τ := yoneda.map s) hpb.w.symm a)))

/-- The value of the bijection at the limit is the value of the global function at the limit
chart. -/
theorem limitGlobalFunctionsEquiv_val (hX : IsAlgebraicSpace B S hS X)
    (hI : A.ChartsBounded)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (σ : globalFunctions' B S hS (A.limitSpace hX).obj) :
    (A.limitGlobalFunctionsEquiv hX hI hf₀ hsurj hpb σ).1
      = σ.val (op (A.limitEtaleChart (A.chartSystem U₀ f₀)
          (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI) hf₀)) :=
  structureSectionsEquivEqualizer_apply_val B S hS (A.limitSpace hX) _ _ σ

/-- **The triangle of the limit chart over a stage chart.**  The projection of the limiting cone
of the chart system, read into the limit algebraic space and the stage, commutes: it is
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.toLimit_comp_limitπ` with the categorical
limit of the system identified with `X` by
`AlgebraicGeometry.Space.LimitSituation.limitIso_hom_comp_π`. -/
theorem yoneda_map_chartLimit_π_comp_stageMap (hX : IsAlgebraicSpace B S hS X)
    (hI : A.ChartsBounded) (i : A.Stages) :
    yoneda.map ((A.chartLimitBridgeOfChartsBounded U₀ f₀ hI).cone.π.app
          ((stagesOverEquivalence A).functor.obj (op i))) ≫
        (A.chartSystem U₀ f₀).stageMap ((stagesOverEquivalence A).functor.obj (op i))
      = A.limitChartToSpace (A.chartSystem U₀ f₀) (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI) ≫
          (A.projection hX i.1).hom :=
  (((A.chartLimitBridgeOfChartsBounded U₀ f₀ hI).toLimit_comp_limitπ
          ((stagesOverEquivalence A).functor.obj (op i))).symm.trans
        (congrArg (fun z => (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI).toLimit ≫ z)
          (A.limitIso_hom_comp_π (op i.1)).symm)).trans
    (Category.assoc _ _ _).symm

/-- **The equalizer presentation of the global functions is natural in the passage to the
limit.** The presentation at the limit, applied to the pullback of a global function of a stage,
is the restriction of the stage's presentation along the projection of the limiting cone of the
chart system. -/
theorem limitGlobalFunctionsEquiv_naturality (hX : IsAlgebraicSpace B S hS X)
    (hI : A.ChartsBounded)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)
    (i : A.Stages) (σ : globalFunctions' B S hS (A.stage i.1).obj) :
    (A.limitGlobalFunctionsEquiv hX hI hf₀ hsurj hpb
        (globalFunctionsMap B S hS (A.projection hX i.1) σ)).1
      = ((A.chartStagesConeOfChartsBounded U₀ f₀ hI).π.app (op i)).appTop.hom
          (A.stageGlobalFunctionsEquiv hf₀ hsurj hpb i σ).1 := by
  rw [A.limitGlobalFunctionsEquiv_val hX hI hf₀ hsurj hpb,
    A.stageGlobalFunctionsEquiv_val hf₀ hsurj hpb i]
  exact globalFunctionsMap_val_of_yoneda_map_comp B S hS (A.projection hX i.1) σ
    (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI) hf₀)
    (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)
    ((A.chartLimitBridgeOfChartsBounded U₀ f₀ hI).cone.π.app
      ((stagesOverEquivalence A).functor.obj (op i)))
    (A.yoneda_map_chartLimit_π_comp_stageMap hX hI i)

/-- **Stacks 07SI for the structure sheaf: the ring of global regular functions on the limit of a
limit situation is the filtered colimit of the rings of global regular functions on the stages.**

The maps are the pullbacks of global functions along the transition morphisms and along the
projections of the limiting cone, and the colimit is asserted in the elementwise form
`Stacks.IsStagesColimit`: every global function on the limit comes from a stage, and two global
functions on a stage with the same image on the limit agree at a later stage.

The hypotheses are those of Stacks 07SF: an affine étale chart `U₀ ⟶ X₀` of the chosen stage,
surjective on points, whose relation `R₀ = U₀ ×_{X₀} U₀` is again affine — which it is at a
separated stage, by
`AlgebraicGeometry.Space.LimitSituation.exists_affine_relationChart_of_isAbsolutelySeparated` —
together with `hI`, boundedness of the charts of the system, which
`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfSizeBound` consumes through
`AlgebraicGeometry.Space.ChartsBounded.sizeBound` and which
`Stacks.Refute07SQ.not_statement07SQ` shows cannot be dropped.

The proof is the source's: `Γ(Xᵢ, 𝒪)` is the equalizer of the two restrictions
`Γ(Uᵢ, 𝒪) → Γ(Rᵢ, 𝒪)` by Stacks 03M8, the same holds at the limit, both presentations are natural
(`stageGlobalFunctionsEquiv_naturality` and `limitGlobalFunctionsEquiv_naturality`), the two
systems of charts are systems of affine schemes with affine transitions whose limits are the limit
charts, so Stacks 01Z0 in its affine case applies to each, and a filtered colimit commutes with
the equalizer (`Stacks.IsStagesColimit.equalizer`).

The coefficients are the structure sheaf, not an arbitrary quasi-coherent module, so this is the
case of Stacks 07SI that the proof of Stacks 07SQ consumes rather than the whole tag. -/
theorem isStagesColimit_globalFunctions_of_chartsBounded (hX : IsAlgebraicSpace B S hS X)
    (hI : A.ChartsBounded)
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀) :
    Stacks.IsStagesColimit
      (G := fun i : A.Stages => globalFunctions' B S hS (A.stage i.1).obj)
      (T := globalFunctions' B S hS (A.limitSpace hX).obj)
      (fun (i j : A.Stages) (h : i ≤ j) x =>
        globalFunctionsMap B S hS (A.transition (show i.1 ≤ j.1 from h)) x)
      (fun (i : A.Stages) x => globalFunctionsMap B S hS (A.projection hX i.1) x) := by
  have haffU : ∀ a, IsAffine ((A.chartStagesDiagram U₀ f₀).obj a) := fun a =>
    A.isAffine_chartStagesDiagram_obj U₀ f₀ a
  have haffR : ∀ a, IsAffine ((A.chartStagesDiagram R₀ (t ≫ f₀)).obj a) := fun a =>
    A.isAffine_chartStagesDiagram_obj R₀ (t ≫ f₀) a
  exact Stacks.IsStagesColimit.ofEquiv _ _
    (A.stageGlobalFunctionsEquiv hf₀ hsurj hpb)
    (A.limitGlobalFunctionsEquiv hX hI hf₀ hsurj hpb)
    (fun i j h σ => Subtype.ext
      (A.stageGlobalFunctionsEquiv_naturality hf₀ hsurj hpb i j h σ))
    (fun i σ => Subtype.ext
      (A.limitGlobalFunctionsEquiv_naturality hX hI hf₀ hsurj hpb i σ))
    (Stacks.IsStagesColimit.equalizer
      (A.chartStagesRestriction_map (τ := t) (f₀ := f₀) rfl)
      (A.chartStagesRestriction_map (τ := yoneda.map s) hpb.w.symm)
      (A.chartStagesRestrictionLimit_π_of_chartsBounded (τ := t) (f₀ := f₀) rfl hI)
      (A.chartStagesRestrictionLimit_π_of_chartsBounded (τ := yoneda.map s) hpb.w.symm hI)
      (isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed
        (A.chartStagesDiagram U₀ f₀) (A.chartStagesConeOfChartsBounded U₀ f₀ hI)
        (A.isLimit_chartStagesConeOfChartsBounded U₀ f₀ hI))
      (isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed
        (A.chartStagesDiagram R₀ (t ≫ f₀)) (A.chartStagesConeOfChartsBounded R₀ (t ≫ f₀) hI)
        (A.isLimit_chartStagesConeOfChartsBounded R₀ (t ≫ f₀) hI)))

end LimitSituation

end AlgebraicGeometry.Space

end

end
