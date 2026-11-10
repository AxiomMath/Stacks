module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartFormalFunctionsTransport

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The chart restriction of `𝓕 / 𝓘ⁿ⁺¹𝓕`, for an arbitrary chart

For an étale chart `A` of an algebraic space `X`, a sheaf of ideals `𝓘 ⊆ 𝒪_X` cartesian on affine
charts and an ideal sheaf `K` on the chart scheme with `K(W) 𝒪_X(W) = 𝓘(W)` over the affine opens
`W` of the chart scheme, the chart restriction of `𝓕 / 𝓘ⁿ⁺¹𝓕` is `𝓕|_A / Kⁿ⁺¹ 𝓕|_A`
(`AlgebraicGeometry.Space.C1573.chartAdicQuotientGenIso`), compatibly with the projections and the
transition maps. This generalizes `AlgebraicGeometry.Space.C1573.chartAdicQuotientIso`, the case of
a base-change chart.
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
  {X : AlgebraicSpaces B S hS} (A : SmallEtale B S hS X.1)
  (𝓘 : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
  (K : (chartScheme A).IdealSheafData)
  (hK : ∀ (W : (chartScheme A).Opens) (hW : IsAffineOpen W),
    Ideal.map (chartSectionsRingHom B S hS X A W) (K.ideal ⟨W, hW⟩) =
      chartSectionIdeal B S hS X.1 X.2 𝓘 (openChartOfComparison B S hS X A W))
  [IsLocallyNoetherian (chartScheme A)]
  (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
  (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)

/-- The chart restriction of a coherent module, as a coherent module on the chart scheme. -/
abbrev C1573.chartCoherentModuleOf :
    AlgebraicGeometry.SheafOfModules.CoherentModules (chartScheme A).ringCatSheaf :=
  ⟨(chartZariskiModule B S hS X A).obj F,
    isCoherent_chartZariskiModule B S hS X F hF _ inferInstance⟩

/-- The chart restriction of a module annihilated by `𝓘ᵐ` is annihilated by `Kᵐ`. The chart `A`
is rebound so that the unused `IsLocallyNoetherian` variable is not pulled in. -/
private theorem chartZariskiModule_affine_annihilated_aux {A : SmallEtale B S hS X.1}
    {K : (chartScheme A).IdealSheafData}
    (hK : ∀ (W : (chartScheme A).Opens) (hW : IsAffineOpen W),
      Ideal.map (chartSectionsRingHom B S hS X A W) (K.ideal ⟨W, hW⟩) =
        chartSectionIdeal B S hS X.1 X.2 𝓘 (openChartOfComparison B S hS X A W))
    (m : ℕ) (N : Modules.{u, u} B S hS X.1 X.2) (hN : IsPowAnnihilated B S hS X.1 X.2 𝓘 m N)
    (W : (chartScheme A).affineOpens) :
    K.ideal W ^ m • (⊤ : Submodule Γ(chartScheme A, W.1)
      Γ((chartZariskiModule B S hS X A).obj N, W.1)) = ⊥ := by
  obtain ⟨W, hW⟩ := W
  refine le_antisymm (Submodule.smul_le.2 fun r hr x _ => ?_) bot_le
  let g : Γ(chartScheme A, W) →+* chartRing B S hS X.1 X.2 (openChartOfComparison B S hS X A W) :=
    chartSectionsRingHom B S hS X _ W
  have hmem := (Ideal.map_pow g _ m).le (Ideal.mem_map_of_mem g hr)
  rw [show Ideal.map g (K.ideal ⟨W, hW⟩) =
    chartIdeal B S hS X 𝓘 (openChartOfComparison B S hS X A W) from hK W hW] at hmem
  exact hN _ _ hmem x

omit [IsLocallyNoetherian (chartScheme A)] in
include hK in
/-- The chart restriction of `𝓕 / 𝓘ⁿ⁺¹𝓕` is annihilated by `ℐⁿ⁺¹` on every affine open. -/
theorem C1573.chartAdicQuotientGen_annihilated (n : ℕ)
    (W : (chartScheme (A)).affineOpens) :
    (K).ideal W ^ (n + 1) •
      (⊤ : Submodule Γ(chartScheme (A), W.1)
        Γ((chartZariskiModule B S hS X (A)).obj
          (smallEtaleAdicQuotient B S hS X.1 X.2 (𝓘) (n + 1) F),
          W.1)) = ⊥ :=
  chartZariskiModule_affine_annihilated_aux B S hS 𝓘 hK (n + 1) _
    (isPowAnnihilated_smallEtaleAdicQuotient B S hS X.1 X.2 𝓘 (n + 1) F) W

/-- **The comparison `𝓕|_U / ℐⁿ⁺¹ 𝓕|_U ⟶ (𝓕 / 𝓘ⁿ⁺¹𝓕)|_U`**, induced by the chart restriction of
the projection `𝓕 ⟶ 𝓕 / 𝓘ⁿ⁺¹𝓕`. -/
def C1573.chartAdicQuotientGenHom (n : ℕ) :
    ((Stacks.Algebraization.completionFunctor _ (K)).obj
        ((chartCoherentModuleOf B S hS A F hF))).obj.obj (op n) ⟶
      (chartZariskiModule B S hS X (A)).obj
        (smallEtaleAdicQuotient B S hS X.1 X.2 (𝓘) (n + 1) F) :=
  eqToHom (Stacks.Algebraization.completionFunctor_obj _ _ _ n) ≫
    cokernel.desc (C := (chartScheme (A)).Modules) _
      ((chartZariskiModule B S hS X (A)).map
        (smallEtaleAdicQuotientProjection B S hS X.1 X.2 (𝓘)
          (n + 1) F))
      (Stacks.Algebraization.C1573.ι_comp_eq_zero_of_le_kernelSubmodule _ _
        (Stacks.Coherent.idealPowerMultiple_le_kernelSubmodule _ (n + 1) _
          (chartAdicQuotientGen_annihilated B S hS A 𝓘 K hK F n)))

/-- The comparison carries the projection of the chart restriction to the chart restriction of
the projection. -/
theorem C1573.completionProjection_comp_chartAdicQuotientGenHom (n : ℕ) :
    Stacks.Algebraization.completionProjection _ (K)
        ((chartCoherentModuleOf B S hS A F hF)) n ≫
        chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF n =
      (chartZariskiModule B S hS X (A)).map
        (smallEtaleAdicQuotientProjection B S hS X.1 X.2 (𝓘)
          (n + 1) F) := by
  rw [Stacks.Algebraization.completionProjection, chartAdicQuotientGenHom]
  refine (Category.assoc (obj := (chartScheme (A)).Modules)
    _ _ _).trans ?_
  have key : ∀ {C : Type (u + 1)} [Category.{u} C] {A P P' D : C} (π : A ⟶ P) (h : P' = P)
      (d : P ⟶ D), π ≫ eqToHom h.symm ≫ eqToHom h ≫ d = π ≫ d := by
    simp
  exact (key _ _ _).trans
    (cokernel.π_desc (C := (chartScheme (A)).Modules) _ _ _)

include hK hIcart in
/-- **The comparison `𝓕|_U / ℐⁿ⁺¹ 𝓕|_U ⟶ (𝓕 / 𝓘ⁿ⁺¹𝓕)|_U` is an isomorphism**, for `𝒥` cartesian
on affine charts with finitely generated ideals of sections over the affine charts: over an
affine open `W` both sides are the quotient of the sections of `𝓕` over the chart `W` cuts out by
the `(n+1)`-st power of one ideal. -/
theorem C1573.isIso_chartAdicQuotientGenHom (n : ℕ) :
    IsIso (chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF n) := by
  have hFcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 F
    hF.toIsQuasicoherentOnSite
  refine Scheme.Modules.C1573.isIso_of_bijective_app_affineOpens _ fun ⟨W, hW⟩ => ?_
  have hWc : IsAffine (chartScheme (openChartOfComparison B S hS X A W)) := hW
  have hcomp := congrArg (fun k => k.val.app (op W))
    (completionProjection_comp_chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF n)
  have hp : Function.Surjective ((Stacks.Algebraization.completionProjection _ K
      (chartCoherentModuleOf B S hS A F hF) n).val.app (op W)) :=
    Stacks.Algebraization.completionProjection_app_surjective _ K
      (chartCoherentModuleOf B S hS A F hF) n ⟨W, hW⟩
  have hpk : LinearMap.ker ((Stacks.Algebraization.completionProjection _ K
      (chartCoherentModuleOf B S hS A F hF) n).val.app (op W)).hom =
      K.ideal ⟨W, hW⟩ ^ (n + 1) • (⊤ : Submodule Γ(chartScheme A, W)
        Γ((chartCoherentModuleOf B S hS A F hF).obj, W)) :=
    Stacks.Algebraization.completionProjection_app_ker _ K
      (chartCoherentModuleOf B S hS A F hF) n ⟨W, hW⟩
  have hπ := surjective_val_app_idealPowerQuotient_π B S hS X.1 X.2 𝓘 hIcart F hFcart (n + 1) hWc
  have hπk := ker_val_app_idealPowerQuotient_π B S hS X.1 X.2 𝓘 hIcart F hFcart (n + 1) hWc
  have hx : ∀ x : Γ((chartZariskiModule B S hS X A).obj F, W),
      (chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF n).app W
        ((Stacks.Algebraization.completionProjection _ K
          (chartCoherentModuleOf B S hS A F hF) n).val.app (op W) x) =
      (cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) F).ι).val.app
        (op (openChartOfComparison B S hS X A W)) x :=
    fun x => ConcreteCategory.congr_hom hcomp x
  change Function.Bijective ((chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF n).app W)
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun z => ?_⟩
  · obtain ⟨x, rfl⟩ := hp y
    replace hy := (hx x).symm.trans hy
    let g : Γ(chartScheme A, W) →+* chartRing B S hS X.1 X.2 (openChartOfComparison B S hS X A W) :=
      chartSectionsRingHom B S hS X _ W
    have hg : Ideal.map g (K.ideal ⟨W, hW⟩) =
        chartSectionIdeal B S hS X.1 X.2 𝓘 (openChartOfComparison B S hS X A W) :=
      hK W hW
    have hmem : x ∈ Ideal.map g (K.ideal ⟨W, hW⟩) ^ (n + 1) •
        (⊤ : Submodule (chartRing B S hS X.1 X.2 (openChartOfComparison B S hS X A W))
          (F.val.obj (op (openChartOfComparison B S hS X A W)))) := by
      rwa [hg, ← hπk]
    have hmem' := Stacks.Submodule.mem_pow_smul_top_of_mem_map_pow_smul_top g
      (surjective_chartSectionsRingHom B S hS X _ W)
      (show Γ((chartZariskiModule B S hS X A).obj F, W) ≃+
        F.val.obj (op (openChartOfComparison B S hS X A W)) from AddEquiv.refl _)
      (fun _ _ => rfl) _ (n + 1) hmem
    rwa [← hpk] at hmem'
  · obtain ⟨x, rfl⟩ := hπ z
    exact ⟨_, hx x⟩

/-- **The chart restriction of `𝓕 / 𝓘ⁿ⁺¹𝓕` is `𝓕|_U / ℐⁿ⁺¹ 𝓕|_U`.** -/
def C1573.chartAdicQuotientGenIso (n : ℕ) :
    ((Stacks.Algebraization.completionFunctor _ (K)).obj
        ((chartCoherentModuleOf B S hS A F hF))).obj.obj (op n) ≅
      (chartZariskiModule B S hS X (A)).obj
        (smallEtaleAdicQuotient B S hS X.1 X.2 (𝓘) (n + 1) F) :=
  haveI := isIso_chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF hIcart n
  asIso (chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF n)

/-- The comparison `𝓕|_U / ℐⁿ⁺¹ ⟶ (𝓕/𝓘ⁿ⁺¹𝓕)|_U` is compatible with the transition maps. -/
theorem C1573.chartAdicQuotientGenHom_transition (n : ℕ) :
    chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF (n + 1) ≫
        (chartZariskiModule B S hS X (A)).map
          (smallEtaleAdicQuotientTransition B S hS X.1 X.2 (𝓘)
            (n + 1) F) =
      ((Stacks.Algebraization.completionFunctor _ (K)).obj
          ((chartCoherentModuleOf B S hS A F hF))).obj.map (homOfLE (Nat.le_succ n)).op ≫
        chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF n := by
  have := Stacks.Algebraization.epi_completionProjection _ (K)
    ((chartCoherentModuleOf B S hS A F hF)) (n + 1)
  refine (cancel_epi (C := (chartScheme (A)).Modules)
    (Stacks.Algebraization.completionProjection _ (K)
      ((chartCoherentModuleOf B S hS A F hF)) (n + 1))).1 ?_
  refine CategoryTheory.C1573.comp_comp_eq_of_three_squares
    (completionProjection_comp_chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF (n + 1))
    (Stacks.Algebraization.completionProjection_transition _ _ _ n) ?_
  refine (Functor.map_comp _ _ _).symm.trans ?_
  exact (congrArg (chartZariskiModule B S hS X (A)).map
    (smallEtaleAdicQuotientProjection_comp_transition B S hS X.1 X.2
      (𝓘) (n + 1) F)).trans
    (completionProjection_comp_chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF n).symm

omit [IsLocallyNoetherian (chartScheme A)] in
include hK in
/-- **The chart restriction of a module annihilated by `𝓘ᵐ` is annihilated by `Kᵐ`.** -/
theorem C1573.chartZariskiModule_affine_annihilated (m : ℕ) (N : Modules.{u, u} B S hS X.1 X.2)
    (hN : IsPowAnnihilated B S hS X.1 X.2 𝓘 m N) (W : (chartScheme A).affineOpens) :
    K.ideal W ^ m • (⊤ : Submodule Γ(chartScheme A, W.1)
      Γ((chartZariskiModule B S hS X A).obj N, W.1)) = ⊥ :=
  chartZariskiModule_affine_annihilated_aux B S hS 𝓘 hK m N hN W

include hK hIcart in
/-- **The chart restriction of a coherent adic system along `𝓘` is a coherent adic system along
`K`.** -/
theorem C1573.isCoherentAdicSystem_chartZariskiModule
    (G : CoherentAdicSystems B S hS X.1 X.2 𝓘) :
    Stacks.Coherent.IsCoherentAdicSystem K (G.obj ⋙ chartZariskiModule B S hS X A) := by
  refine ⟨fun n => isCoherent_chartZariskiModule B S hS X _ (G.property.1 n) A inferInstance,
    fun n => ?_, fun n => ?_⟩
  · exact (Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_smul_top K (n + 1) _).2
      (chartZariskiModule_affine_annihilated B S hS A 𝓘 K hK (n + 1) _
        ((idealPowerMultiple_eq_bot_iff B S hS X.1 X.2 𝓘 (n + 1) _).1 (G.property.2.1 n)))
  · obtain ⟨e, he⟩ := G.property.2.2 n
    let M := G.obj.obj (op (n + 1))
    have hM : IsCoherent B S hS X.1 X.2 M := G.property.1 (n + 1)
    refine ⟨eqToIso (Stacks.Algebraization.completionFunctor_obj _ K
        (chartCoherentModuleOf B S hS A M hM) n).symm ≪≫
      chartAdicQuotientGenIso B S hS A 𝓘 K hK M hM hIcart n ≪≫
      (chartZariskiModule B S hS X A).mapIso e, ?_⟩
    have h2 : (Stacks.Algebraization.completionProjection _ K
        (chartCoherentModuleOf B S hS A M hM) n ≫ chartAdicQuotientGenHom B S hS A 𝓘 K hK M hM n) ≫
          (chartZariskiModule B S hS X A).map e.hom =
        (chartZariskiModule B S hS X A).map (G.obj.map (homOfLE (Nat.le_succ n)).op) := by
      rw [completionProjection_comp_chartAdicQuotientGenHom B S hS A 𝓘 K hK M hM n]
      exact ((chartZariskiModule B S hS X A).map_comp _ _).symm.trans
        (congrArg (chartZariskiModule B S hS X A).map he)
    refine Eq.trans ?_ h2
    rw [Stacks.Algebraization.completionProjection]
    simp only [Iso.trans_hom, eqToIso.hom]
    rfl

/-- The comparison of the completion of the chart restriction with the chart restriction of the
completion, as a morphism of inverse systems. -/
def C1573.chartCompletionHom :
    ((Stacks.Algebraization.completionFunctor _ K).obj (chartCoherentModuleOf B S hS A F hF)).obj ⟶
      adicQuotientSystem B S hS X.1 X.2 𝓘 F ⋙ chartZariskiModule B S hS X A :=
  NatTrans.ofOpSequence (fun n => chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF n) (fun n => by
    change _ = chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF (n + 1) ≫
      (chartZariskiModule B S hS X A).map
        ((adicQuotientSystem B S hS X.1 X.2 𝓘 F).map (homOfLE (Nat.le_add_right n 1)).op)
    rw [adicQuotientSystem_map_succ]
    exact (chartAdicQuotientGenHom_transition B S hS A 𝓘 K hK F hF n).symm)

/-- The component of `chartCompletionHom` at `n` is `chartAdicQuotientGenHom` at `n`. -/
theorem C1573.chartCompletionHom_app (n : ℕ) :
    (chartCompletionHom B S hS A 𝓘 K hK F hF).app (op n) =
      chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF n :=
  rfl

include hIcart in
/-- The comparison of the completion of the chart restriction with the chart restriction of the
completion is an isomorphism of inverse systems. -/
theorem C1573.isIso_chartCompletionHom : IsIso (chartCompletionHom B S hS A 𝓘 K hK F hF) := by
  have : ∀ n : ℕᵒᵖ, IsIso ((chartCompletionHom B S hS A 𝓘 K hK F hF).app n) := fun n =>
    isIso_chartAdicQuotientGenHom B S hS A 𝓘 K hK F hF hIcart n.unop
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.Space

end
