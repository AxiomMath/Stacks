module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSectionMapNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartSectionTransitionCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge

/-!
# The sections of a quasi-coherent module over an affine chart system are a filtered colimit

Let `E` be the chart system `Vᵢ = Xᵢ ×_{X₀} V₀` of an affine étale chart `V₀ ⟶ X₀` of the chosen
stage of a limit situation and `V = X ×_{X₀} V₀` its limit, and let `ℱ₀` be a quasi-coherent
module on `X₀`.  Over the affine charts, the sections of `ℱᵢ = f_{0i}^*ℱ₀` are the base change
`ℱᵢ(Vᵢ) = 𝒪(Vᵢ) ⊗_{𝒪(V₀)} ℱ₀(V₀)` (the chart bijectivity of Stacks 083K,
`AlgebraicGeometry.Space.bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite`), and
likewise `ℱ(V) = 𝒪(V) ⊗_{𝒪(V₀)} ℱ₀(V₀)`.  These identifications carry the chart section maps
of Stacks 07SI to the restriction maps of the chart rings tensored with `ℱ₀(V₀)`, which form a
filtered colimit by
`AlgebraicGeometry.Space.LimitSituation.isStagesColimit_chartRing_rTensor`.

## Main results

* `AlgebraicGeometry.Space.chartPullbackSectionMap_smul` and `.chartPullbackSectionMap_add`: the
  chart section map of a morphism out of an inverse image is additive and semilinear over the
  pullback of regular functions.
* `AlgebraicGeometry.Space.chartPullbackSectionMap_baseChange`: through the base-change
  comparisons, a chart section map which carries chart sections to chart sections is the
  restriction of regular functions tensored with the sections of the module.
* `AlgebraicGeometry.Space.LimitSituation.isStagesColimit_chartSections_of_isQuasicoherent`: for
  a quasi-coherent `ℱ₀`, the sections `ℱᵢ(Vᵢ)` along the chart section maps have `ℱ(V)` as their
  filtered colimit.  This is the hypothesis `hchart` of
  `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_chartSystemColimits`.
* `AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_isQuasicoherent`: the assertion
  of Stacks 07SI for a quasi-coherent `ℱ₀`, given that the limit is an algebraic space and the
  index set is below the cofinality of the cutoff of the site.  It carries no tag here.

The identifications at the stages use the cocycle identities
`AlgebraicGeometry.Space.LimitSituation.chartStageTransition_baseChartSection` and
`.chartLimitInclusion_baseChartSection`.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Generic

variable {Y Z : AlgebraicSpaces B S hS} (f : Y ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2)
  (N : Modules.{u, u} B S hS Y.1 Y.2) (ψ : (modulePullback B S hS f).obj M ⟶ N)
  (d : ChartDiagram B S hS Y.1 Z.1 f.hom)

/-- **The chart section map of a morphism out of an inverse image is additive.** -/
theorem chartPullbackSectionMap_add (y y' : M.val.obj (op d.V)) :
    chartPullbackSectionMap B S hS f M N ψ d (y + y')
      = chartPullbackSectionMap B S hS f M N ψ d y + chartPullbackSectionMap B S hS f M N ψ d y' :=
  (congrArg (ψ.val.app (op d.U)) (modulePullbackChartSection_add B S hS f M d y y')).trans
    (map_add (ψ.val.app (op d.U)).hom _ _)

/-- **The chart section map of a morphism out of an inverse image is semilinear** over the
pullback of regular functions along the chart diagram. -/
theorem chartPullbackSectionMap_smul (r : chartRing B S hS Z.1 Z.2 d.V)
    (y : M.val.obj (op d.V)) :
    chartPullbackSectionMap B S hS f M N ψ d (r • y)
      = chartDiagramRestrict B S hS f d r • chartPullbackSectionMap B S hS f M N ψ d y :=
  (congrArg (ψ.val.app (op d.U)) (modulePullbackChartSection_smul B S hS f M d r y)).trans
    (map_smul (ψ.val.app (op d.U)).hom _ _)

/-- The chart section map of a morphism out of an inverse image vanishes at zero. -/
theorem chartPullbackSectionMap_zero :
    chartPullbackSectionMap B S hS f M N ψ d 0 = 0 := by
  have h := chartPullbackSectionMap_add f M N ψ d 0 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

/-- **The chart section map of a comparison of inverse images, read through the base-change
comparisons.**  Let `g : X ⟶ Y`, `fY : Y ⟶ Z` and `fX : X ⟶ Z`, let `ψ : g^*(fY^*M) ⟶ fX^*M`, and
let `d` be a chart diagram over `g` whose charts lie over a chart `W` of `Z` along `b` and `c`.
If the chart section map of `ψ` carries the chart sections along `b` to the chart sections along
`c` (`hcoc`), then it carries the base-change comparison over `d.V` to the base-change comparison
over `d.U` after tensoring the restriction `ρ : 𝒪(d.V) → 𝒪(d.U)` with `M(W)`. -/
theorem chartPullbackSectionMap_baseChange {X Y Z : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (fY : Y ⟶ Z) (fX : X ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2)
    (ψ : (modulePullback B S hS g).obj ((modulePullback B S hS fY).obj M) ⟶
      (modulePullback B S hS fX).obj M)
    (d : ChartDiagram B S hS X.1 Y.1 g.hom) {W : SmallEtale B S hS Z.1}
    (b : (SmallEtale.toOver B S hS Y.1).obj d.V ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (hb : d.V.1.hom ≫ fY.hom = yoneda.map b ≫ W.1.hom)
    (c : (SmallEtale.toOver B S hS X.1).obj d.U ⟶ (SmallEtale.toOver B S hS Z.1).obj W)
    (hc : d.U.1.hom ≫ fX.hom = yoneda.map c ≫ W.1.hom)
    (hcoc : ∀ m : M.val.obj (op W),
      chartPullbackSectionMap B S hS g ((modulePullback B S hS fY).obj M)
          ((modulePullback B S hS fX).obj M) ψ d
          (modulePullbackChartSection B S hS fY M ⟨d.V, W, b, hb⟩ m) =
        modulePullbackChartSection B S hS fX M ⟨d.U, W, c, hc⟩ m)
    (ρL : letI := chartDiagramAlgebra B S hS fY ⟨d.V, W, b, hb⟩
      letI := chartDiagramAlgebra B S hS fX ⟨d.U, W, c, hc⟩
      chartRing B S hS Y.1 Y.2 d.V →ₗ[chartRing B S hS Z.1 Z.2 W] chartRing B S hS X.1 X.2 d.U)
    (hρ : ∀ a, ρL a = chartDiagramRestrict B S hS g d a)
    (t : letI := chartDiagramAlgebra B S hS fY ⟨d.V, W, b, hb⟩
      TensorProduct (chartRing B S hS Z.1 Z.2 W) (chartRing B S hS Y.1 Y.2 d.V)
        (M.val.obj (op W))) :
    letI := chartDiagramAlgebra B S hS fY ⟨d.V, W, b, hb⟩
    letI := chartDiagramAlgebra B S hS fX ⟨d.U, W, c, hc⟩
    chartPullbackSectionMap B S hS g ((modulePullback B S hS fY).obj M)
        ((modulePullback B S hS fX).obj M) ψ d
        (modulePullbackChartBaseChange B S hS fY M ⟨d.V, W, b, hb⟩ t) =
      modulePullbackChartBaseChange B S hS fX M ⟨d.U, W, c, hc⟩ (ρL.rTensor _ t) := by
  let := chartDiagramAlgebra B S hS fY ⟨d.V, W, b, hb⟩
  let := chartDiagramAlgebra B S hS fX ⟨d.U, W, c, hc⟩
  induction t using TensorProduct.inductionOn with
  | tmul a m =>
    rw [modulePullbackChartBaseChange_tmul, LinearMap.rTensor_tmul,
      modulePullbackChartBaseChange_tmul, chartPullbackSectionMap_smul, hcoc, hρ]
  | add x y hx hy =>
    rw [map_add, chartPullbackSectionMap_add, hx, hy, map_add, map_add]

end Generic

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)
  {V₀ : BigAffineFppf B S hS}
  {e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V₀) ⟶ A.system.obj (op A.base)}
  (E : AffineChartSystem B S hS (op A.base) A.system V₀ e₀)
  (he₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk e₀))
  (F₀ : Modules.{u, u} B S hS (A.stage A.base).obj (A.stage A.base).property)

/-- **The base-change comparison `𝒪(Vᵢ) ⊗_{𝒪(V₀)} ℱ₀(V₀) → ℱᵢ(Vᵢ)` at a stage.** -/
noncomputable abbrev stageChartBaseChange (i : A.Stages) :
    letI := A.chartStageAlgebra E he₀ i
    TensorProduct (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
          (A.stagesEtaleChart E he₀ A.baseStage))
        (chartRing B S hS (A.stage i.1).obj (A.stage i.1).property (A.stagesEtaleChart E he₀ i))
        (F₀.val.obj (op (A.stagesEtaleChart E he₀ A.baseStage))) →ₗ[chartRing B S hS
          (A.stage i.1).obj (A.stage i.1).property (A.stagesEtaleChart E he₀ i)]
      ((modulePullback B S hS (A.transition i.2)).obj F₀).val.obj
        (op (A.stagesEtaleChart E he₀ i)) :=
  modulePullbackChartBaseChange B S hS (A.transition i.2) F₀ (A.baseChartDiagram E he₀ i)

/-- **The base-change comparison `𝒪(V) ⊗_{𝒪(V₀)} ℱ₀(V₀) → ℱ(V)` at the limit.** -/
noncomputable abbrev limitChartBaseChange (LE : AffineChartSystem.LimitBridge E)
    (hX : IsAlgebraicSpace B S hS X) :
    letI := A.chartLimitAlgebra E he₀ LE hX
    TensorProduct (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
          (A.stagesEtaleChart E he₀ A.baseStage))
        (chartRing B S hS (A.limitSpace hX).obj (A.limitSpace hX).property
          (A.limitChartDiagram E he₀ LE hX A.baseStage).U)
        (F₀.val.obj (op (A.stagesEtaleChart E he₀ A.baseStage))) →ₗ[chartRing B S hS
          (A.limitSpace hX).obj (A.limitSpace hX).property
          (A.limitChartDiagram E he₀ LE hX A.baseStage).U]
      ((modulePullback B S hS (A.projection hX A.base)).obj F₀).val.obj
        (op (A.limitChartDiagram E he₀ LE hX A.baseStage).U) :=
  modulePullbackChartBaseChange B S hS (A.projection hX A.base) F₀
    (A.limitChartDiagram E he₀ LE hX A.baseStage)

/-- **The chart section maps between the stages, read through the base-change comparisons, are
the restrictions of the chart rings tensored with `ℱ₀(V₀)`.** -/
theorem chartStageTransition_stageChartBaseChange {i j : A.Stages} (h : i ≤ j)
    (t : letI := A.chartStageAlgebra E he₀ i
      TensorProduct (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
            (A.stagesEtaleChart E he₀ A.baseStage))
        (chartRing B S hS (A.stage i.1).obj (A.stage i.1).property (A.stagesEtaleChart E he₀ i))
        (F₀.val.obj (op (A.stagesEtaleChart E he₀ A.baseStage)))) :
    letI := A.chartStageAlgebra E he₀ i
    letI := A.chartStageAlgebra E he₀ j
    A.chartStageTransition E he₀ F₀ h (A.stageChartBaseChange E he₀ F₀ i t)
      = A.stageChartBaseChange E he₀ F₀ j
          ((A.chartStageRestrictLinear E he₀ h).rTensor
            (F₀.val.obj (op (A.stagesEtaleChart E he₀ A.baseStage))) t) :=
  chartPullbackSectionMap_baseChange (A.transition h) (A.transition i.2) (A.transition j.2) F₀
    (A.stageTransitionComparison F₀ i j h) (A.stagesChartDiagram E he₀ h)
    (A.baseChartDiagram E he₀ i).g (A.baseChartDiagram E he₀ i).comm
    (A.baseChartDiagram E he₀ j).g (A.baseChartDiagram E he₀ j).comm
    (fun m => A.chartStageTransition_baseChartSection E he₀ F₀ h m)
    (A.chartStageRestrictLinear E he₀ h) (fun _ => rfl) t

/-- **The chart section maps to the limit, read through the base-change comparisons, are the
restrictions of the chart rings tensored with `ℱ₀(V₀)`.** -/
theorem chartLimitInclusion_limitChartBaseChange (LE : AffineChartSystem.LimitBridge E)
    (hX : IsAlgebraicSpace B S hS X) (i : A.Stages)
    (t : letI := A.chartStageAlgebra E he₀ i
      TensorProduct (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
            (A.stagesEtaleChart E he₀ A.baseStage))
        (chartRing B S hS (A.stage i.1).obj (A.stage i.1).property (A.stagesEtaleChart E he₀ i))
        (F₀.val.obj (op (A.stagesEtaleChart E he₀ A.baseStage)))) :
    letI := A.chartStageAlgebra E he₀ i
    letI := A.chartLimitAlgebra E he₀ LE hX
    A.chartLimitInclusion E he₀ F₀ LE hX i (A.stageChartBaseChange E he₀ F₀ i t)
      = A.limitChartBaseChange E he₀ F₀ LE hX
          ((A.chartLimitRestrictLinear E he₀ LE hX i).rTensor
            (F₀.val.obj (op (A.stagesEtaleChart E he₀ A.baseStage))) t) :=
  chartPullbackSectionMap_baseChange (A.projection hX i.1) (A.transition i.2)
    (A.projection hX A.base) F₀ (A.stageProjectionComparison F₀ hX i)
    (A.limitChartDiagram E he₀ LE hX i)
    (A.baseChartDiagram E he₀ i).g (A.baseChartDiagram E he₀ i).comm
    (A.limitChartDiagram E he₀ LE hX A.baseStage).g
    (A.limitChartDiagram E he₀ LE hX A.baseStage).comm
    (fun m => A.chartLimitInclusion_baseChartSection E he₀ F₀ LE hX i m)
    (A.chartLimitRestrictLinear E he₀ LE hX i) (fun _ => rfl) t

/-- The base-change comparison at a stage is bijective for a quasi-coherent module: the charts
are affine. -/
theorem bijective_stageChartBaseChange (hF₀ : F₀.IsQuasicoherentOnSite) (i : A.Stages) :
    Function.Bijective (A.stageChartBaseChange E he₀ F₀ i) :=
  bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS (A.transition i.2) F₀
    hF₀ (A.baseChartDiagram E he₀ i) (isAffine_stagesSchemeDiagram_obj A E (op i))
    (isAffine_stagesSchemeDiagram_obj A E (op A.baseStage))

/-- The base-change comparison at the limit is bijective for a quasi-coherent module: the limit
chart is affine. -/
theorem bijective_limitChartBaseChange (hF₀ : F₀.IsQuasicoherentOnSite)
    (LE : AffineChartSystem.LimitBridge E) (hX : IsAlgebraicSpace B S hS X) :
    Function.Bijective (A.limitChartBaseChange E he₀ F₀ LE hX) :=
  bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS (A.projection hX A.base)
    F₀ hF₀ (A.limitChartDiagram E he₀ LE hX A.baseStage) LE.isAffine_pt
    (isAffine_stagesSchemeDiagram_obj A E (op A.baseStage))

/-- Inverting two bijections intertwines two maps that commute with them. -/
private theorem symm_ofBijective_comm {α β γ δ : Type*} {f : α → β} {g : γ → δ}
    (hf : f.Bijective) (hg : g.Bijective) {φ : β → δ} {ψ : α → γ}
    (h : ∀ a, φ (f a) = g (ψ a)) (b : β) :
    (Equiv.ofBijective g hg).symm (φ b) = ψ ((Equiv.ofBijective f hf).symm b) := by
  obtain ⟨a, rfl⟩ := hf.2 b
  simp only [h, Equiv.ofBijective_symm_apply_apply]

/-- **The sections of a quasi-coherent module over an affine chart system are a filtered
colimit.** -/
theorem isStagesColimit_chartSections_of_isQuasicoherent (hF₀ : F₀.IsQuasicoherentOnSite)
    (LE : AffineChartSystem.LimitBridge E) (hX : IsAlgebraicSpace B S hS X) :
    Stacks.IsStagesColimit
      (fun i j h => A.chartStageTransition E he₀ F₀ (i := i) (j := j) h)
      (fun i => A.chartLimitInclusion E he₀ F₀ LE hX i) := by
  let := fun i : A.Stages => A.chartStageAlgebra E he₀ i
  let := A.chartLimitAlgebra E he₀ LE hX
  let e := fun i : A.Stages =>
    (Equiv.ofBijective _ (A.bijective_stageChartBaseChange E he₀ F₀ hF₀ i)).symm
  let eT := (Equiv.ofBijective _ (A.bijective_limitChartBaseChange E he₀ F₀ hF₀ LE hX)).symm
  refine Stacks.IsStagesColimit.ofEquiv _ _ e eT (fun i j h s => ?_) (fun i s => ?_)
    (A.isStagesColimit_chartRing_rTensor E he₀ LE hX
      (F₀.val.obj (op (A.stagesEtaleChart E he₀ A.baseStage))))
  · exact symm_ofBijective_comm _ _ (A.chartStageTransition_stageChartBaseChange E he₀ F₀ h) s
  · exact symm_ofBijective_comm _ _
      (A.chartLimitInclusion_limitChartBaseChange E he₀ F₀ LE hX i) s

omit E he₀ in
/-- **The global sections of the inverse image of a quasi-coherent module to the limit are the
filtered colimit of its global sections at the stages** (the assertion of Stacks 07SI), given
that the limit is an algebraic space and the index set is below the cofinality of the cutoff. -/
theorem isSectionsColimit_of_isQuasicoherent (hX : IsAlgebraicSpace B S hS X)
    (hI : #A.I < B.cutoff.ord.cof) (hF₀ : F₀.IsQuasicoherentOnSite) :
    A.IsSectionsColimit F₀ hX :=
  A.isSectionsColimit_of_chartSystemColimits F₀ hX hI fun {V₀ e₀} he₀ =>
    A.isStagesColimit_chartSections_of_isQuasicoherent (A.chartSystem V₀ e₀) he₀ F₀ hF₀
      (A.chartLimitBridge V₀ e₀ hI) hX

end AlgebraicGeometry.Space.LimitSituation

end
