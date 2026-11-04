module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartAnnihilationTransport
public import StacksFrontier.AlgebraicGeometry.C1573Port.PullbackSections.AffineAdjointIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafDataComparison
public import StacksFrontier.RingTheory.C1573Port.IsBaseChangeRingEquiv

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The adjoints of the scheme maps `γ'_n` are isomorphisms

Over an affine étale chart `V` of `Y`, the adjoints `f_V^*(𝒢_n(V)~) ⟶ 𝓕|_U/ℐⁿ⁺¹` of the scheme
maps `γ'_n` (`AlgebraicGeometry.Space.C1573.chartGamma`) are isomorphisms
(`AlgebraicGeometry.Space.C1573.isIso_adjoint_chartGamma`). Over an affine open `W` of the chart
scheme of `U = V ×_Y X`, the map `𝒢_n(V) ⟶ (𝓕/𝓘ⁿ⁺¹𝓕)(W)`, `m ↦ γ_n(m)|_W`, is a base change,
because it is the composite of the base change `𝒢_n(V) ⟶ (f^*𝒢_n)(W)` of Stacks 083K with the
isomorphism `β_n`; transported to the scheme side it is the restriction of `γ'_n` to `W`, and the
criterion `AlgebraicGeometry.C1573.isIso_homEquiv_symm_of_isBaseChange` applies.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

open _root_.CategoryTheory.C1573
attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
  (J : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
  (F : Modules.{u, u} B S hS X.1 X.2)
  (G : CoherentAdicSystems B S hS Y.1 Y.2 J)
  (β : G.obj ⋙ modulePullback B S hS f ≅
    adicQuotientSystem B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F)
  (V : SmallEtale B S hS Y.1) [IsAffine (chartScheme V)]
  [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
  (hF : IsCoherent B S hS X.1 X.2 F)
  (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
  (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
    (chartSectionsIdeal B S hS Y J Q).FG)

/-- The functions on a Zariski open `W` of a chart scheme are the functions on the étale chart
which `W` cuts out. -/
def C1573.chartSectionsRingEquiv (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens) :
    Γ(chartScheme A, W) ≃+* chartRing B S hS X.1 X.2 (openChartOfComparison B S hS X A W) :=
  RingEquiv.ofRingHom (chartSectionsRingHom B S hS X A W) (openChartTopRingHom B S hS X A W)
    (RingHom.ext fun y => chartSectionsRingHom_openChartTopRingHom B S hS X A W y)
    (RingHom.ext fun r => openChartTopRingHom_chartSectionsRingHom B S hS X A W r)

/-- `chartSectionsRingEquiv` is given by `chartSectionsRingHom`. -/
theorem C1573.chartSectionsRingEquiv_apply (A : SmallEtale B S hS X.1) (W : (chartScheme A).Opens)
    (r : Γ(chartScheme A, W)) :
    chartSectionsRingEquiv B S hS A W r = chartSectionsRingHom B S hS X A W r :=
  rfl

omit [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))] in
/-- **Stacks 083K on the chart cut out by an affine open of the chart scheme of `U`**: the chart
component of the unit is a base change. -/
theorem C1573.isBaseChange_modulePullbackChartSectionLinear_openChartDiagram
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).affineOpens) :
    letI := chartDiagramAlgebra B S hS f (baseChangeOpenChartDiagram B S hS f hf V W.1)
    letI := modulePullbackChartSectionModule B S hS f M
      (baseChangeOpenChartDiagram B S hS f hf V W.1)
    haveI := modulePullbackChart_isScalarTower B S hS f M
      (baseChangeOpenChartDiagram B S hS f hf V W.1)
    IsBaseChange (chartRing B S hS X.1 X.2 (baseChangeOpenChartDiagram B S hS f hf V W.1).U)
      (modulePullbackChartSectionLinear B S hS f M
        (baseChangeOpenChartDiagram B S hS f hf V W.1)) := by
  let := chartDiagramAlgebra B S hS f (baseChangeOpenChartDiagram B S hS f hf V W.1)
  let := modulePullbackChartSectionModule B S hS f M (baseChangeOpenChartDiagram B S hS f hf V W.1)
  have := modulePullbackChart_isScalarTower B S hS f M
    (baseChangeOpenChartDiagram B S hS f hf V W.1)
  have hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj
      (baseChangeOpenChartDiagram B S hS f hf V W.1).U) := W.2
  have hV : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj
      (baseChangeOpenChartDiagram B S hS f hf V W.1).V) :=
    inferInstanceAs (IsAffine (chartScheme V))
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _
    (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS f M hM
      (baseChangeOpenChartDiagram B S hS f hf V W.1) hU hV)) fun s =>
      (modulePullbackChartBaseChange_tmul B S hS f M _ 1 s).trans (one_smul _ _)

variable [IsNoetherianRing Γ(chartScheme V, ⊤)] (hJqc : J.toSheafOfModules.IsQuasicoherentOnSite)

/-- **The restriction of `γ'_n` to a Zariski open `W`, read on the chart cut out by `W`, is `β_n`
on the chart component of the unit.** -/
theorem C1573.chartAdicQuotientHom_app_restrict_chartGamma (n : ℕ)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (m : (G.obj.obj (op n)).val.obj (op V)) :
    (chartAdicQuotientHom B S hS f hf V J F hF hJ n).app W
        ((((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)).presheaf.map
            (homOfLE (le_top : W ≤ (chartBaseChangeSchemeHom B S hS f hf V) ⁻¹ᵁ ⊤)).op
          (Scheme.Modules.Hom.app ((chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc).app (op n)) ⊤
            ((Stacks.Coherent.affineTildeSectionsIso (chartScheme V)
              ((chartSectionsTop B S hS V).obj (G.obj.obj (op n)))).hom.hom m))) =
      (β.hom.app (op n)).val.app (op (baseChangeOpenChartDiagram B S hS f hf V W).U)
        (modulePullbackChartSection B S hS f (G.obj.obj (op n))
          (baseChangeOpenChartDiagram B S hS f hf V W) m) := by
  rw [chartGamma_app_top]
  exact (chartAdicQuotientHom_app_restrict B S hS f hf V J F hF hJ hJfg n W _).trans
    (β_modulePullbackChartSection B S hS f hf J F G β n
      (baseChangeOpenChartDiagram B S hS f hf V W) m).symm

/-- The functions on a Zariski open `W` of the chart scheme of `U` are the functions on the
étale chart of the chart diagram of `W`. -/
abbrev C1573.openChartDiagramRingEquiv
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) :
    Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W) ≃+*
      chartRing B S hS X.1 X.2 (baseChangeOpenChartDiagram B S hS f hf V W).U :=
  chartSectionsRingEquiv B S hS ((smallBaseChange B S hS f hf).obj V) W

/-- `β_n` on the sections over the chart cut out by `W`. -/
def C1573.chartPullbackSectionsEquiv (n : ℕ)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) :=
  ((SheafOfModules.evaluation.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      (op (baseChangeOpenChartDiagram B S hS f hf V W).U)).mapIso (β.app (op n))).toLinearEquiv

/-- **The sections of `𝓕|_U/ℐⁿ⁺¹` over `W` are the sections of `f^*𝒢_n` over the chart cut out by
`W`**, through the chart identification and `β_n`. -/
def C1573.chartAdicQuotientPullbackEquiv (n : ℕ)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) :
    Γ((((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W) ≃+
      ((modulePullback B S hS f).obj (G.obj.obj (op n))).val.obj
        (op (baseChangeOpenChartDiagram B S hS f hf V W).U) :=
  (((Scheme.Modules.toPresheaf _).mapIso
    (chartAdicQuotientIso B S hS f hf V J F hF hJ hJfg n)).app
      (op W)).addCommGroupIsoToAddEquiv.trans
      (chartPullbackSectionsEquiv B S hS f hf J F G β V n W).symm.toAddEquiv

omit [IsNoetherianRing Γ(chartScheme V, ⊤)] in
/-- `chartAdicQuotientPullbackEquiv` sends a section `x` over `W` to the inverse of `β_n` applied
to the image of `x` under `chartAdicQuotientHom`. -/
theorem C1573.chartAdicQuotientPullbackEquiv_apply (n : ℕ)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (x : Γ((((Stacks.Algebraization.completionFunctor _
          (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W)) :
    chartAdicQuotientPullbackEquiv B S hS f hf J F G β V hF hJ hJfg n W x =
      (chartPullbackSectionsEquiv B S hS f hf J F G β V n W).symm
        ((chartAdicQuotientHom B S hS f hf V J F hF hJ n).app W x) :=
  rfl

omit [IsNoetherianRing Γ(chartScheme V, ⊤)] in
/-- `chartAdicQuotientPullbackEquiv` is semilinear along `openChartDiagramRingEquiv`. -/
theorem C1573.chartAdicQuotientPullbackEquiv_smul (n : ℕ)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (s : Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W))
    (x : Γ((((Stacks.Algebraization.completionFunctor _
          (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W)) :
    chartAdicQuotientPullbackEquiv B S hS f hf J F G β V hF hJ hJfg n W (s • x) =
      openChartDiagramRingEquiv B S hS f hf V W s •
        chartAdicQuotientPullbackEquiv B S hS f hf J F G β V hF hJ hJfg n W x := by
  rw [chartAdicQuotientPullbackEquiv_apply, chartAdicQuotientPullbackEquiv_apply,
    Scheme.Modules.Hom.app_smul]
  exact (chartPullbackSectionsEquiv B S hS f hf J F G β V n W).symm.map_smul _ _

/-- **The restriction of `γ'_n` to `W` is the chart component of the unit of `f^*`**, through
`AlgebraicGeometry.Space.C1573.chartAdicQuotientPullbackEquiv`. -/
theorem C1573.chartAdicQuotientPullbackEquiv_restrict_chartGamma (n : ℕ)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (m : (G.obj.obj (op n)).val.obj (op V)) :
    chartAdicQuotientPullbackEquiv B S hS f hf J F G β V hF hJ hJfg n W
        ((((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)).presheaf.map
          (homOfLE (le_top : W ≤ (chartBaseChangeSchemeHom B S hS f hf V) ⁻¹ᵁ ⊤)).op
          (Scheme.Modules.Hom.app ((chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc).app (op n)) ⊤
            ((Stacks.Coherent.affineTildeSectionsIso (chartScheme V)
              ((chartSectionsTop B S hS V).obj (G.obj.obj (op n)))).hom.hom m))) =
      modulePullbackChartSection B S hS f (G.obj.obj (op n))
        (baseChangeOpenChartDiagram B S hS f hf V W) m := by
  rw [chartAdicQuotientPullbackEquiv_apply,
    chartAdicQuotientHom_app_restrict_chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc n W m]
  exact (chartPullbackSectionsEquiv B S hS f hf J F G β V n W).symm_apply_apply _

/-- **Over an affine open `W` of the chart scheme of `U`, `m ↦ γ'_n(m)|_W` is a base change.**
Through `AlgebraicGeometry.Space.C1573.chartAdicQuotientPullbackEquiv` it is the chart component
of the unit of `f^*`, a base change by Stacks 083K. -/
theorem C1573.exists_isBaseChange_restrict_chartGamma (n : ℕ)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).affineOpens) :
    letI := ((chartBaseChangeSchemeHom B S hS f hf V).appLE ⊤ W.1 le_top).hom.toAlgebra
    letI : Module Γ(chartScheme V, ⊤)
        (ModuleCat.of Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
          Γ((((Stacks.Algebraization.completionFunctor _
            (chartBaseChangeIdeal B S hS f hf V J)).obj
            (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W.1)) :=
      Module.compHom _ ((chartBaseChangeSchemeHom B S hS f hf V).appLE ⊤ W.1 le_top).hom
    haveI : IsScalarTower Γ(chartScheme V, ⊤)
        Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
        (ModuleCat.of Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
          Γ((((Stacks.Algebraization.completionFunctor _
            (chartBaseChangeIdeal B S hS f hf V J)).obj
            (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W.1)) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∃ ξ : ModuleCat.of Γ(chartScheme V, ⊤) Γ((Stacks.Coherent.affineTilde (chartScheme V)).obj
          ((chartSectionsTop B S hS V).obj (G.obj.obj (op n))), ⊤) →ₗ[Γ(chartScheme V, ⊤)]
        ModuleCat.of Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
          Γ((((Stacks.Algebraization.completionFunctor _
            (chartBaseChangeIdeal B S hS f hf V J)).obj
            (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W.1),
      (∀ s, ξ s = (((Stacks.Algebraization.completionFunctor _
          (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)).presheaf.map
            (homOfLE (le_top : W.1 ≤ (chartBaseChangeSchemeHom B S hS f hf V) ⁻¹ᵁ ⊤)).op
        (Scheme.Modules.Hom.app ((chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc).app (op n)) ⊤
          s)) ∧
      IsBaseChange Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1) ξ := by
  let := ((chartBaseChangeSchemeHom B S hS f hf V).appLE ⊤ W.1 le_top).hom.toAlgebra
  let : Module Γ(chartScheme V, ⊤)
      (ModuleCat.of Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
        Γ((((Stacks.Algebraization.completionFunctor _
          (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W.1)) :=
    Module.compHom _ ((chartBaseChangeSchemeHom B S hS f hf V).appLE ⊤ W.1 le_top).hom
  have : IsScalarTower Γ(chartScheme V, ⊤)
      Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
      (ModuleCat.of Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
        Γ((((Stacks.Algebraization.completionFunctor _
          (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W.1)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Algebra Γ(chartScheme V, ⊤)
      (chartRing B S hS X.1 X.2 (baseChangeOpenChartDiagram B S hS f hf V W.1).U) :=
    (chartDiagramRestrict B S hS f (baseChangeOpenChartDiagram B S hS f hf V W.1)).toAlgebra
  let : Module Γ(chartScheme V, ⊤) (((modulePullback B S hS f).obj (G.obj.obj (op n))).val.obj
      (op (baseChangeOpenChartDiagram B S hS f hf V W.1).U)) :=
    Module.compHom _ (chartDiagramRestrict B S hS f (baseChangeOpenChartDiagram B S hS f hf V W.1))
  have : IsScalarTower Γ(chartScheme V, ⊤)
      (chartRing B S hS X.1 X.2 (baseChangeOpenChartDiagram B S hS f hf V W.1).U)
      (((modulePullback B S hS f).obj (G.obj.obj (op n))).val.obj
        (op (baseChangeOpenChartDiagram B S hS f hf V W.1).U)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let φ : (chartSectionsTop B S hS V).obj (G.obj.obj (op n)) →ₗ[Γ(chartScheme V, ⊤)]
      ((modulePullback B S hS f).obj (G.obj.obj (op n))).val.obj
        (op (baseChangeOpenChartDiagram B S hS f hf V W.1).U) :=
    { toFun := modulePullbackChartSection B S hS f (G.obj.obj (op n))
        (baseChangeOpenChartDiagram B S hS f hf V W.1)
      map_add' := modulePullbackChartSection_add B S hS f _
        (baseChangeOpenChartDiagram B S hS f hf V W.1)
      map_smul' := modulePullbackChartSection_smul B S hS f _
        (baseChangeOpenChartDiagram B S hS f hf V W.1) }
  have hb : IsBaseChange
      (chartRing B S hS X.1 X.2 (baseChangeOpenChartDiagram B S hS f hf V W.1).U) φ :=
    isBaseChange_modulePullbackChartSectionLinear_openChartDiagram B S hS f hf V
      (G.obj.obj (op n)) (G.property.1 n).toIsQuasicoherentOnSite W
  let σ : Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1) ≃+*
      chartRing B S hS X.1 X.2 (baseChangeOpenChartDiagram B S hS f hf V W.1).U :=
    chartSectionsRingEquiv B S hS ((smallBaseChange B S hS f hf).obj V) W.1
  have hσ : ∀ r : Γ(chartScheme V, ⊤),
      σ (algebraMap Γ(chartScheme V, ⊤)
          Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1) r) =
        algebraMap Γ(chartScheme V, ⊤)
          (chartRing B S hS X.1 X.2 (baseChangeOpenChartDiagram B S hS f hf V W.1).U) r :=
    fun r => chartSectionsRingHom_appLE B S hS f hf V W.1 r
  let eM : ModuleCat.of Γ(chartScheme V, ⊤) Γ((Stacks.Coherent.affineTilde (chartScheme V)).obj
        ((chartSectionsTop B S hS V).obj (G.obj.obj (op n))), ⊤) ≃ₗ[Γ(chartScheme V, ⊤)]
      (chartSectionsTop B S hS V).obj (G.obj.obj (op n)) :=
    (Stacks.Coherent.affineTildeSectionsIso (chartScheme V)
      ((chartSectionsTop B S hS V).obj (G.obj.obj (op n)))).toLinearEquiv.symm
  let eN : ModuleCat.of Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
        Γ((((Stacks.Algebraization.completionFunctor _
          (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W.1) ≃+
      ((modulePullback B S hS f).obj (G.obj.obj (op n))).val.obj
        (op (baseChangeOpenChartDiagram B S hS f hf V W.1).U) :=
    chartAdicQuotientPullbackEquiv B S hS f hf J F G β V hF hJ hJfg n W.1
  have heN : ∀ (s : Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1))
      (x : ModuleCat.of Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
        Γ((((Stacks.Algebraization.completionFunctor _
          (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W.1)),
      eN (s • x) = σ s • eN x :=
    chartAdicQuotientPullbackEquiv_smul B S hS f hf J F G β V hF hJ hJfg n W.1
  have key := IsBaseChange.C1573.exists_of_ringEquiv (R := Γ(chartScheme V, ⊤))
    (S := Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1))
    (S' := chartRing B S hS X.1 X.2 (baseChangeOpenChartDiagram B S hS f hf V W.1).U)
    (M := ModuleCat.of Γ(chartScheme V, ⊤) Γ((Stacks.Coherent.affineTilde (chartScheme V)).obj
        ((chartSectionsTop B S hS V).obj (G.obj.obj (op n))), ⊤))
    (M' := (chartSectionsTop B S hS V).obj (G.obj.obj (op n)))
    (N := ModuleCat.of Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
      Γ((((Stacks.Algebraization.completionFunctor _
        (chartBaseChangeIdeal B S hS f hf V J)).obj
        (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)), W.1))
    (N' := ((modulePullback B S hS f).obj (G.obj.obj (op n))).val.obj
      (op (baseChangeOpenChartDiagram B S hS f hf V W.1).U))
    σ hσ eM eN heN φ hb
  refine ⟨key.choose, fun s => (key.choose_spec.1 s).trans ((AddEquiv.symm_apply_eq eN).2 ?_),
    key.choose_spec.2⟩
  have h2 := chartAdicQuotientPullbackEquiv_restrict_chartGamma B S hS f hf J F G β V hF hJ hJfg
    hJqc n W.1 (eM s)
  refine h2.symm.trans ?_
  erw [eM.symm_apply_apply s]

/-- **The adjoints `f_V^*(𝒢_n(V)~) ⟶ 𝓕|_U/ℐⁿ⁺¹` of the scheme maps `γ'_n` are isomorphisms.**
Over an affine open `W` of the chart scheme of `U`, the map `m ↦ γ'_n(m)|_W` is, through the
identification of `(𝓕|_U/ℐⁿ⁺¹)(W)` with the sections of `𝓕/𝓘ⁿ⁺¹𝓕` over the chart cut out by `W`
and the isomorphism `β_n`, the chart component of the unit of `f^*`, a base change by Stacks
083K. -/
theorem C1573.isIso_adjoint_chartGamma (n : ℕ) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction
        (chartBaseChangeSchemeHom B S hS f hf V)).homEquiv _ _).symm
        ((chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc).app (op n))) :=
  isIso_homEquiv_symm_of_isBaseChange (chartBaseChangeSchemeHom B S hS f hf V)
    ((chartSectionsTop B S hS V).obj (G.obj.obj (op n))) _
    ((chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc).app (op n))
    (exists_isBaseChange_restrict_chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc n)

end AlgebraicGeometry.Space

end
