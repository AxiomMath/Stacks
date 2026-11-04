module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartModuleEvaluationNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportFlatPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.TensorColimit

/-!
# Extension of scalars along the rings of an affine chart system is a filtered colimit

Let `E` be the chart system `Vᵢ = Xᵢ ×_{X₀} V₀` of an affine étale chart `V₀ ⟶ X₀` of the chosen
stage of a limit situation, and `V = X ×_{X₀} V₀` its limit.  The rings `𝒪(Vᵢ)` and `𝒪(V)` are
algebras over `R = 𝒪(V₀)` by restriction along the charts over the chosen stage, and the
restriction maps between them are `R`-algebra maps.  This file proves that, for every
`R`-module `M`, the groups `𝒪(Vᵢ) ⊗_R M` have `𝒪(V) ⊗_R M` as their filtered colimit.

This is the algebraic half of the colimit assertion for the sections over an affine chart system
of the pullbacks of a quasi-coherent module, in the proof of Stacks 07SI: over affine charts those
sections are `𝒪(Vᵢ) ⊗_R ℱ₀(V₀)` by the chart bijectivity of Stacks 083K.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.baseChartDiagram`: the chart diagram of `Vᵢ` over `V₀`.
* `AlgebraicGeometry.Space.LimitSituation.chartStageAlgebra` and `.chartLimitAlgebra`: the
  `R`-algebra structures on `𝒪(Vᵢ)` and `𝒪(V)`.
* `AlgebraicGeometry.Space.LimitSituation.chartStageRestrictLinear` and
  `.chartLimitRestrictLinear`: the restriction maps `𝒪(Vᵢ) → 𝒪(Vⱼ)` and `𝒪(Vᵢ) → 𝒪(V)` as
  `R`-linear maps.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.chartStageRestrict_comp` and
  `.chartLimitRestrict_comp`: the restriction maps compose.
* `AlgebraicGeometry.Space.LimitSituation.isStagesColimit_chartRing_rTensor`: for every
  `R`-module `M`, `𝒪(V) ⊗_R M` is the filtered colimit of the `𝒪(Vᵢ) ⊗_R M`.  This is the affine
  case of Stacks 01Z0 for the structure sheaf,
  `AlgebraicGeometry.isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed`, tensored with
  `M` by `Stacks.LimitHomDescent.isStagesColimit_rTensor`.

## References

* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X)
  {V₀ : BigAffineFppf B S hS}
  {e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V₀) ⟶ A.system.obj (op A.base)}
  (E : AffineChartSystem B S hS (op A.base) A.system V₀ e₀)
  (he₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk e₀))

/-- Global sections of a composite, elementwise. -/
private theorem appTop_hom_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) {h : X ⟶ Z} (e : f ≫ g = h) (x : Γ(Z, ⊤)) :
    f.appTop.hom (g.appTop.hom x) = h.appTop.hom x := by
  subst e
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- The chosen index, as a stage. -/
abbrev baseStage : A.Stages := ⟨A.base, le_rfl⟩

/-- **The chart diagram of the chart `Vᵢ` over the chart `V₀` of the chosen stage.** -/
noncomputable abbrev baseChartDiagram (i : A.Stages) :
    ChartDiagram B S hS (A.stage i.1).obj (A.stage A.base).obj (A.transition i.2).hom :=
  A.stagesChartDiagram E he₀ (i := A.baseStage) (j := i) i.2

/-- **The `𝒪(V₀)`-algebra structure on `𝒪(Vᵢ)`**, by restriction along the chart diagram of `Vᵢ`
over `V₀`.  Not an instance. -/
noncomputable abbrev chartStageAlgebra (i : A.Stages) :
    Algebra (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
        (A.stagesEtaleChart E he₀ A.baseStage))
      (chartRing B S hS (A.stage i.1).obj (A.stage i.1).property (A.stagesEtaleChart E he₀ i)) :=
  chartDiagramAlgebra B S hS (A.transition i.2) (A.baseChartDiagram E he₀ i)

/-- **The `𝒪(V₀)`-algebra structure on `𝒪(V)`**, by restriction along the chart diagram of the
limit chart over `V₀`.  Not an instance. -/
noncomputable abbrev chartLimitAlgebra (LE : AffineChartSystem.LimitBridge E)
    (hX : IsAlgebraicSpace B S hS X) :
    Algebra (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
        (A.stagesEtaleChart E he₀ A.baseStage))
      (chartRing B S hS (A.limitSpace hX).obj (A.limitSpace hX).property
        (A.limitChartDiagram E he₀ LE hX A.baseStage).U) :=
  chartDiagramAlgebra B S hS (A.projection hX A.base) (A.limitChartDiagram E he₀ LE hX A.baseStage)

/-- **The restriction maps between the rings of the charts compose.** -/
theorem chartStageRestrict_comp {i j k : A.Stages} (h : i ≤ j) (h' : j ≤ k)
    (x : chartRing B S hS (A.stage i.1).obj (A.stage i.1).property (A.stagesEtaleChart E he₀ i)) :
    chartDiagramRestrict B S hS (A.transition h') (A.stagesChartDiagram E he₀ h')
        (chartDiagramRestrict B S hS (A.transition h) (A.stagesChartDiagram E he₀ h) x)
      = chartDiagramRestrict B S hS (A.transition (h.trans h'))
          (A.stagesChartDiagram E he₀ (h.trans h')) x := by
  exact appTop_hom_comp_apply _ _ ((stagesSchemeDiagram A E).map_comp _ _).symm x

/-- **The restriction to the limit chart after a restriction between charts is the restriction to
the limit chart.** -/
theorem chartLimitRestrict_comp (LE : AffineChartSystem.LimitBridge E)
    (hX : IsAlgebraicSpace B S hS X) {i j : A.Stages} (h : i ≤ j)
    (x : chartRing B S hS (A.stage i.1).obj (A.stage i.1).property (A.stagesEtaleChart E he₀ i)) :
    chartDiagramRestrict B S hS (A.projection hX j.1) (A.limitChartDiagram E he₀ LE hX j)
        (chartDiagramRestrict B S hS (A.transition h) (A.stagesChartDiagram E he₀ h) x)
      = chartDiagramRestrict B S hS (A.projection hX i.1)
          (A.limitChartDiagram E he₀ LE hX i) x :=
  appTop_hom_comp_apply _ _ ((stagesSchemeCone A E LE).w (homOfLE h).op) x

/-- **The restriction `𝒪(Vᵢ) → 𝒪(Vⱼ)` as an `𝒪(V₀)`-linear map.** -/
noncomputable def chartStageRestrictLinear {i j : A.Stages} (h : i ≤ j) :
    letI := A.chartStageAlgebra E he₀ i
    letI := A.chartStageAlgebra E he₀ j
    chartRing B S hS (A.stage i.1).obj (A.stage i.1).property (A.stagesEtaleChart E he₀ i) →ₗ[
      chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
        (A.stagesEtaleChart E he₀ A.baseStage)]
      chartRing B S hS (A.stage j.1).obj (A.stage j.1).property (A.stagesEtaleChart E he₀ j) :=
  letI := A.chartStageAlgebra E he₀ i
  letI := A.chartStageAlgebra E he₀ j
  AlgHom.toLinearMap
    { toRingHom := chartDiagramRestrict B S hS (A.transition h) (A.stagesChartDiagram E he₀ h)
      commutes' := fun r => A.chartStageRestrict_comp E he₀ i.2 h r }

/-- **The restriction `𝒪(Vᵢ) → 𝒪(V)` as an `𝒪(V₀)`-linear map.** -/
noncomputable def chartLimitRestrictLinear (LE : AffineChartSystem.LimitBridge E)
    (hX : IsAlgebraicSpace B S hS X) (i : A.Stages) :
    letI := A.chartStageAlgebra E he₀ i
    letI := A.chartLimitAlgebra E he₀ LE hX
    chartRing B S hS (A.stage i.1).obj (A.stage i.1).property (A.stagesEtaleChart E he₀ i) →ₗ[
      chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
        (A.stagesEtaleChart E he₀ A.baseStage)]
      chartRing B S hS (A.limitSpace hX).obj (A.limitSpace hX).property
        (A.limitChartDiagram E he₀ LE hX A.baseStage).U :=
  letI := A.chartStageAlgebra E he₀ i
  letI := A.chartLimitAlgebra E he₀ LE hX
  AlgHom.toLinearMap
    { toRingHom := chartDiagramRestrict B S hS (A.projection hX i.1)
        (A.limitChartDiagram E he₀ LE hX i)
      commutes' := fun r => A.chartLimitRestrict_comp E he₀ LE hX i.2 r }

/-- **Extension of scalars along the rings of an affine chart system is a filtered colimit.**  For
every `𝒪(V₀)`-module `M`, the groups `𝒪(Vᵢ) ⊗ M`, along the restriction maps tensored with `M`,
have `𝒪(V) ⊗ M` as their filtered colimit.

The rings form a filtered colimit by the affine case of Stacks 01Z0 for the structure sheaf,
`AlgebraicGeometry.isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed`, the charts being
affine and their limit a limiting cone of schemes
(`AlgebraicGeometry.Space.LimitSituation.isLimit_stagesSchemeCone`); the tensor product commutes
with filtered colimits, `Stacks.LimitHomDescent.isStagesColimit_rTensor`. -/
theorem isStagesColimit_chartRing_rTensor (LE : AffineChartSystem.LimitBridge E)
    (hX : IsAlgebraicSpace B S hS X) (M : Type u) [AddCommGroup M]
    [Module (chartRing B S hS (A.stage A.base).obj (A.stage A.base).property
      (A.stagesEtaleChart E he₀ A.baseStage)) M] :
    letI := fun i : A.Stages => A.chartStageAlgebra E he₀ i
    letI := A.chartLimitAlgebra E he₀ LE hX
    Stacks.IsStagesColimit
      (fun i j h x => (A.chartStageRestrictLinear E he₀ (i := i) (j := j) h).rTensor M x)
      (fun i x => (A.chartLimitRestrictLinear E he₀ LE hX i).rTensor M x) := by
  let := fun i : A.Stages => A.chartStageAlgebra E he₀ i
  let := A.chartLimitAlgebra E he₀ LE hX
  classical
  have := isAffine_stagesSchemeDiagram_obj A E
  have hG := isStagesColimit_appTop_of_isAffine_of_isLimit_of_directed (stagesSchemeDiagram A E)
    (stagesSchemeCone A E LE) (isLimit_stagesSchemeCone A E LE)
  exact Stacks.LimitHomDescent.isStagesColimit_rTensor
    (fun i j h => A.chartStageRestrictLinear E he₀ (i := i) (j := j) h)
    (fun i => A.chartLimitRestrictLinear E he₀ LE hX i)
    (fun i x => (congrArg (fun φ => (Scheme.Hom.appTop φ).hom x)
      ((stagesSchemeDiagram A E).map_id (op i))).trans rfl)
    (fun i j k h h' x => A.chartStageRestrict_comp E he₀ h h' x) hG M

end AlgebraicGeometry.Space.LimitSituation

end
