module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartRingTensorColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartModuleEvaluationValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompIsoChartSection

/-!
# The chart section maps of Stacks 07SI compose

Let `ℱᵢ = f_{0i}^*ℱ₀` be the modules of Stacks 07SI and `Vᵢ` the charts of an affine chart system.
A section `m` of `ℱ₀` over the chart `V₀` of the chosen stage has a chart section
`φᵢ(m) ∈ ℱᵢ(Vᵢ)` along the chart diagram `Vᵢ → V₀` over `f_{0i}`.  The cocycle identity wanted
for Stacks 07SI is that the chart section map `ℱᵢ(Vᵢ) → ℱⱼ(Vⱼ)` carries `φᵢ(m)` to `φⱼ(m)`;
together with the base-change comparison `ℱᵢ(Vᵢ) ≅ 𝒪(Vᵢ) ⊗_{𝒪(V₀)} ℱ₀(V₀)` it identifies the
system of chart sections with the tensored system of chart rings.  This file proves it, at the
stages and at the limit, from a generic statement for an arbitrary composable pair of morphisms of
algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_hom_chartSection`: the comparison of Stacks 03LU
  between iterated and composed inverse images carries a chart section of a chart section to the
  chart section along the composite diagram, stated at an explicit chart diagram.
* `AlgebraicGeometry.Space.chartPullbackSectionMap_compComparison`: the same for the chart section
  map of `AlgebraicGeometry.Space.modulePullbackCompComparison`.
* `AlgebraicGeometry.Space.LimitSituation.baseChartDiagram_g_comp` and `.limitChartDiagram_g_comp`:
  the chart maps over the chosen stage compose, at the stages and from the limit.
* `AlgebraicGeometry.Space.LimitSituation.chartStageTransition_baseChartSection` and
  `.chartLimitInclusion_baseChartSection`: **the cocycle identities**
  `chartStageTransition h (φᵢ m) = φⱼ m` and `chartLimitInclusion i (φᵢ m) = φ(m)`.

## Implementation notes

*Why the comparisons are routed through `modulePullbackCompComparison`.*  The comparisons
`AlgebraicGeometry.Space.LimitSituation.stageTransitionComparison` and `.stageProjectionComparison`
are `modulePullbackCompIso ≫ eqToHom _`.  Written out inline, their bodies carry the auxiliary
proofs Lean abstracts out of definition bodies (`stageModule._proof_1` and the like, even in the
binder type of `ℱ₀` in the equation lemmas) wherever a restatement carries the projections they
abstract.  Comparing the two in the kernel does not settle argument by argument, because the heads
on the path are abbreviations (`AlgebraicGeometry.Space.Modules` and the small étale ringed site),
which the kernel unfolds instead of comparing arguments; every such comparison timed out, whether
by `rfl`, through the equation lemmas, or through a hypothesis `ψ = …`.  Both comparisons are
therefore defined as one application of the generic regular definition
`AlgebraicGeometry.Space.modulePullbackCompComparison`, whose arguments the kernel compares one by
one, and the cocycle identities are instances of a lemma about that definition, proved generically.
In the generic proof the `eqToHom` is removed by `subst` and `eqToHom_refl`, never by proof
irrelevance.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Comp

variable {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1} {W : SmallEtale B S hS Z.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (b : (SmallEtale.toOver B S hS Y.1).obj V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)

/-- The comparison of Stacks 03LU on a chart section of a chart section, at the composed chart
diagram `AlgebraicGeometry.Space.ChartDiagram.comp`, through
`AlgebraicGeometry.Space.modulePullbackChartSection`. -/
theorem modulePullbackCompIso_hom_chartSection_comp (s : M.val.obj (op W)) :
    ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U)
      (modulePullbackChartSection B S hS f ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
        (modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s)) =
      modulePullbackChartSection B S hS (f ≫ g) M (ChartDiagram.comp B S hS f g a b ha hb) s := by
  have h1 := modulePullbackCompIso_hom_val_app_modulePullbackUnitSection B S hS f g a b ha hb M s
  have e1 := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS f
    ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
    (modulePullbackUnitSection B S hS g M ⟨V, W, b, hb⟩ s)
  have e2 := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s
  have e3 := modulePullbackUnitSection_eq_modulePullbackChartSection B S hS (f ≫ g) M
    (ChartDiagram.comp B S hS f g a b ha hb) s
  refine (congrArg (fun x => ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U) x)
    ((congrArg (modulePullbackChartSection B S hS f ((modulePullback B S hS g).obj M)
      ⟨U, V, a, ha⟩) e2.symm).trans e1.symm)).trans ?_
  exact h1.trans e3

/-- The composed chart diagram is the chart diagram with the composite vertical morphism, on chart
sections.  Stated separately so that the kernel meets the two spellings only here. -/
theorem modulePullbackChartSection_comp_eq_mk
    (hk : U.1.hom ≫ (f ≫ g).hom = yoneda.map (a ≫ b) ≫ W.1.hom) (s : M.val.obj (op W)) :
    modulePullbackChartSection B S hS (f ≫ g) M (ChartDiagram.comp B S hS f g a b ha hb) s =
      modulePullbackChartSection B S hS (f ≫ g) M ⟨U, W, a ≫ b, hk⟩ s :=
  rfl

/-- **The comparison of Stacks 03LU carries a chart section of a chart section to the chart
section along the composite**, at an explicit chart diagram. -/
theorem modulePullbackCompIso_hom_chartSection
    (hk : U.1.hom ≫ (f ≫ g).hom = yoneda.map (a ≫ b) ≫ W.1.hom) (s : M.val.obj (op W)) :
    ((modulePullbackCompIso B S hS f g).hom.app M).val.app (op U)
      (modulePullbackChartSection B S hS f ((modulePullback B S hS g).obj M) ⟨U, V, a, ha⟩
        (modulePullbackChartSection B S hS g M ⟨V, W, b, hb⟩ s)) =
      modulePullbackChartSection B S hS (f ≫ g) M ⟨U, W, a ≫ b, hk⟩ s :=
  (modulePullbackCompIso_hom_chartSection_comp f g M a b ha hb s).trans
    (modulePullbackChartSection_comp_eq_mk f g M a b ha hb hk s)

end Comp

/-- **The chart section map along the comparison of iterated inverse images composes chart
sections.**  For `f ≫ g = k`, the chart section map of
`AlgebraicGeometry.Space.modulePullbackCompComparison` along a chart diagram `d` carries the chart
section along `b` of `s` to the chart section of `s` along any `c = d.g ≫ b`. -/
theorem chartPullbackSectionMap_compComparison {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (w : f ≫ g = k) (M : Modules.{u, u} B S hS Z.1 Z.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) {W : SmallEtale B S hS Z.1}
    (b : (SmallEtale.toOver B S hS Y.1).obj d.V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (hb : d.V.1.hom ≫ g.hom = yoneda.map b ≫ W.1.hom)
    (c : (SmallEtale.toOver B S hS X.1).obj d.U ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (hc : d.U.1.hom ≫ k.hom = yoneda.map c ≫ W.1.hom) (e : d.g ≫ b = c) (s : M.val.obj (op W)) :
    chartPullbackSectionMap B S hS f ((modulePullback B S hS g).obj M)
        ((modulePullback B S hS k).obj M) (modulePullbackCompComparison B S hS f g k w M) d
        (modulePullbackChartSection B S hS g M ⟨d.V, W, b, hb⟩ s) =
      modulePullbackChartSection B S hS k M ⟨d.U, W, c, hc⟩ s := by
  obtain ⟨U, V, a, ha⟩ := d
  subst e w
  unfold modulePullbackCompComparison chartPullbackSectionMap
  refine (Stacks.Sheaves.RingedToposModules.comp_val_app_apply _ _ (op U) _).trans ?_
  refine (congrArg (fun x => (eqToHom (congrArg (fun k => (modulePullback B S hS k).obj M)
    (rfl : f ≫ g = f ≫ g))).val.app (op U) x)
    (modulePullbackCompIso_hom_chartSection f g M a b ha hb hc s)).trans ?_
  exact (congrArg (fun e : (modulePullback B S hS (f ≫ g)).obj M ⟶
      (modulePullback B S hS (f ≫ g)).obj M => e.val.app (op U)
        (modulePullbackChartSection B S hS (f ≫ g) M ⟨U, W, a ≫ b, hc⟩ s))
      (eqToHom_refl _ _)).trans (id_val_app_apply' _ _ _)

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

/-- **The chart diagrams over the chosen stage compose**: the chart map `Vⱼ → Vᵢ` followed by
`Vᵢ → V₀` is `Vⱼ → V₀`, by functoriality of the chart system. -/
theorem baseChartDiagram_g_comp {i j : A.Stages} (h : i ≤ j) :
    (A.stagesChartDiagram C hf₀ h).g ≫ (A.baseChartDiagram C hf₀ i).g =
      (A.baseChartDiagram C hf₀ j).g := by
  exact (C.siteDiagram.map_comp _ _).symm.trans
    (congrArg C.siteDiagram.map
      ((Functor.map_comp _ _ _).symm.trans (congrArg _ (Subsingleton.elim _ _))))

/-- **The limit chart diagrams over the chosen stage compose**: the projection `V → Vᵢ` followed by
`Vᵢ → V₀` is `V → V₀`, by naturality of the limiting cone of the chart system. -/
theorem limitChartDiagram_g_comp (LC : AffineChartSystem.LimitBridge C)
    (hX : IsAlgebraicSpace B S hS X) (i : A.Stages) :
    (A.limitChartDiagram C hf₀ LC hX i).g ≫ (A.baseChartDiagram C hf₀ i).g =
      (A.limitChartDiagram C hf₀ LC hX (⟨A.base, le_rfl⟩ : A.Stages)).g :=
  LC.cone.w ((stagesOverEquivalence A).functor.map
    (homOfLE (show (⟨A.base, le_rfl⟩ : A.Stages) ≤ i from i.2)).op)

/-- **The cocycle identity at the limit**: the chart section map `ℱᵢ(Vᵢ) → ℱ(V)` carries the chart
section along `Vᵢ → V₀` of a section `m` of `ℱ₀` over `V₀` to its chart section along `V → V₀`. -/
theorem chartLimitInclusion_baseChartSection (LC : AffineChartSystem.LimitBridge C)
    (hX : IsAlgebraicSpace B S hS X) (i : A.Stages)
    (m : F₀.val.obj (op (A.stagesEtaleChart C hf₀ A.baseStage))) :
    A.chartLimitInclusion C hf₀ F₀ LC hX i
        (modulePullbackChartSection B S hS (A.transition i.2) F₀
          ⟨(A.limitChartDiagram C hf₀ LC hX i).V, A.stagesEtaleChart C hf₀ A.baseStage,
            (A.baseChartDiagram C hf₀ i).g, (A.baseChartDiagram C hf₀ i).comm⟩ m) =
      modulePullbackChartSection B S hS (A.projection hX A.base) F₀
          ⟨(A.limitChartDiagram C hf₀ LC hX i).U, A.stagesEtaleChart C hf₀ A.baseStage,
            (A.limitChartDiagram C hf₀ LC hX A.baseStage).g,
            (A.limitChartDiagram C hf₀ LC hX A.baseStage).comm⟩ m :=
  chartPullbackSectionMap_compComparison (A.projection hX i.1) (A.transition i.2)
    (A.projection hX A.base) (A.projection_comp_transition hX i.2) F₀
    (A.limitChartDiagram C hf₀ LC hX i)
    (A.baseChartDiagram C hf₀ i).g (A.baseChartDiagram C hf₀ i).comm
    (A.limitChartDiagram C hf₀ LC hX A.baseStage).g
    (A.limitChartDiagram C hf₀ LC hX A.baseStage).comm
    (A.limitChartDiagram_g_comp C hf₀ LC hX i) m

/-- **The cocycle identity of the chart section maps of Stacks 07SI**: the chart section map
`ℱᵢ(Vᵢ) → ℱⱼ(Vⱼ)` carries the chart section along `Vᵢ → V₀` of a section `m` of `ℱ₀` over `V₀`
to its chart section along `Vⱼ → V₀`. -/
theorem chartStageTransition_baseChartSection {i j : A.Stages} (h : i ≤ j)
    (m : F₀.val.obj (op (A.stagesEtaleChart C hf₀ A.baseStage))) :
    A.chartStageTransition C hf₀ F₀ h
        (modulePullbackChartSection B S hS (A.transition i.2) F₀
          ⟨(A.stagesChartDiagram C hf₀ h).V, A.stagesEtaleChart C hf₀ A.baseStage,
            (A.baseChartDiagram C hf₀ i).g, (A.baseChartDiagram C hf₀ i).comm⟩ m) =
      modulePullbackChartSection B S hS (A.transition j.2) F₀
          ⟨(A.stagesChartDiagram C hf₀ h).U, A.stagesEtaleChart C hf₀ A.baseStage,
            (A.baseChartDiagram C hf₀ j).g, (A.baseChartDiagram C hf₀ j).comm⟩ m :=
  chartPullbackSectionMap_compComparison (A.transition h) (A.transition i.2) (A.transition j.2)
    (A.transition_comp i.2 h j.2) F₀ (A.stagesChartDiagram C hf₀ h)
    (A.baseChartDiagram C hf₀ i).g (A.baseChartDiagram C hf₀ i).comm
    (A.baseChartDiagram C hf₀ j).g (A.baseChartDiagram C hf₀ j).comm
    (A.baseChartDiagram_g_comp C hf₀ h) m

end AlgebraicGeometry.Space.LimitSituation

end
