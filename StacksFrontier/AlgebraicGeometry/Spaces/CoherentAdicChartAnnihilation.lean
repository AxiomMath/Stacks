module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartBeta
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenInterchange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSupportUnitLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealComplementChartOpen

/-!
# Stacks 08BD on an affine chart: the scheme lemma 088B on the chart's scheme

Let `f : X ⟶ Y` be a representable proper morphism of algebraic spaces and `V` a Noetherian affine
étale chart of `Y`, with base-change morphism `g : V ×_Y X ⟶ V` of chart schemes.  This file
assembles, on the chart's scheme of `V`, the data of the scheme lemma Stacks 088B
(`Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_isNoetherian`) out of the data of
Stacks 08BD, and reads its conclusion back on the sections over `V`.

## Main results

* `AlgebraicGeometry.Space.isIso_chartBaseChangeMorphism_restrict` — if `f` is an isomorphism
  over `Y ∖ V(𝓚)`, then `g` is an isomorphism over the complement of the support of the
  chartwise ideal of `𝓚`.
* `AlgebraicGeometry.Space.chartBetaIso` — the scheme-side `β` as an isomorphism of coherent adic
  systems.
* `AlgebraicGeometry.Space.chartTildeMap_comp_pushforwardCompletionComparison` — the scheme-side
  `α` satisfies the defining equation `α ≫ c = γ` of Stacks 088B.
* `AlgebraicGeometry.Space.exists_pow_smul_chart_kernel_cokernel` — **one power of `𝓚(V)` kills
  the kernels of the maps `α_k` on the sections over `V` and carries the sections of their targets
  into their images, for all `k` at once.**

## References

* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

section Restrict

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)

/-- **A representable morphism which is an isomorphism over `Y ∖ V(𝓚)` has, on every étale chart
`V` of `Y`, base-change morphism an isomorphism over the complement of the support of the
chartwise ideal of `𝓚`.** -/
theorem isIso_chartBaseChangeMorphism_restrict
    (K : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule)
    (hK : IsCartesianOnAffineCharts K.toSheafOfModules)
    (hiso : IsIso ((idealComplementSubfunctor B S hS Y K).fromPreimage f.hom))
    (V : SmallEtale B S hS Y.1) :
    IsIso (chartBaseChangeMorphism B S hS f hf V ∣_
      (idealSheafDataOfChart B S hS Y K hK V).support.compl) := by
  set O := (idealSheafDataOfChart B S hS Y K hK V).support.compl
  obtain ⟨gO, hgO⟩ := exists_hom_comp_idealComplementι_eq B S hS Y K hK V (le_refl O)
  have hA := (Subfunctor.isPullback_fromPreimage (idealComplementSubfunctor B S hS Y K) f.hom).flip
  have hB := hf.isPullback (openChart B S hS Y.1 V O).obj.hom
  have hw : hf.fst (openChart B S hS Y.1 V O).obj.hom ≫ f.hom =
      (yoneda.map (hf.snd (openChart B S hS Y.1 V O).obj.hom) ≫ gO) ≫
        (idealComplementSubfunctor B S hS Y K).ι := by
    refine hB.w.trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg _ hgO.symm
  let t := hA.lift _ _ hw
  have hbig : IsPullback (t ≫ ((idealComplementSubfunctor B S hS Y K).preimage f.hom).ι)
      (yoneda.map (hf.snd (openChart B S hS Y.1 V O).obj.hom)) f.hom
      (gO ≫ (idealComplementSubfunctor B S hS Y K).ι) := by
    have e1 : t ≫ ((idealComplementSubfunctor B S hS Y K).preimage f.hom).ι =
        hf.fst (openChart B S hS Y.1 V O).obj.hom := hA.lift_fst _ _ hw
    have e2 : gO ≫ (idealComplementSubfunctor B S hS Y K).ι = (openChart B S hS Y.1 V O).obj.hom :=
      hgO
    exact e1 ▸ e2 ▸ hB
  have hC := IsPullback.of_right hbig (hA.lift_snd _ _ hw) hA
  have := hC.isIso_snd_of_isIso hiso
  have : IsIso (hf.snd (openChart B S hS Y.1 V O).obj.hom) :=
    isIso_of_fully_faithful yoneda _
  have h1 := openChartBaseChangeIso_hom_comp_projection B S hS f hf V O
  have : IsIso (openChartSmallBaseChangeProjection B S hS f hf V O) := by
    have : IsIso ((openChartBaseChangeIso B S hS f hf V O).hom ≫
        openChartSmallBaseChangeProjection B S hS f hf V O) := h1 ▸ inferInstance
    exact IsIso.of_isIso_comp_left (openChartBaseChangeIso B S hS f hf V O).hom _
  exact (inferInstance : IsIso ((BigFppfOver.toScheme B S hS).map
    (openChartSmallBaseChangeProjection B S hS f hf V O)))

end Restrict

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (J : (SheafOfModules.unit.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (V : SmallEtale B S hS Y.1) [hV : IsAffine (chartScheme V)]
    (G : CoherentAdicSystems B S hS Y.1 Y.2 J)
    (hIcart : IsCartesianOnAffineCharts (hF := X.2)
      (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules)
    [hXloc : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hIq : (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules.IsQuasicoherentOnSite)
    [hWN : IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (β : G.obj ⋙ modulePullback B S hS f ≅
      ((completionFunctor B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J) hIq).obj
        ⟨F, hF⟩).obj)
    [hVN : IsNoetherianRing Γ(chartScheme V, ⊤)]

include hJ in
/-- **The scheme-side `β` as an isomorphism of coherent adic systems.** -/
def chartBetaIso
    [_root_.AlgebraicGeometry.IsNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
    [_root_.AlgebraicGeometry.IsNoetherian (chartScheme V)] :
    (Stacks.Coherent.coherentAdicPullback (chartBaseChangeMorphism B S hS f hf V)
        (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))).obj
        (chartTildeSystem B S hS J hJ V G) ≅
      (Stacks.Algebraization.completionFunctor (chartScheme ((smallBaseChange B S hS f hf).obj V))
        (chartBaseChangeIdeal B S hS f hf J V)).obj
        (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V)) :=
  have hiso : ∀ n, IsIso ((chartBetaSystem B S hS J hJ V G f hf hIcart hIq F hF β).app n) :=
    fun n =>
      haveI : ((chartTildeSystem B S hS J hJ V G).obj.obj (op n.unop)).IsQuasicoherent :=
        Stacks.Coherent.affineTilde_quasicoherent (chartScheme V) _
      Stacks.Algebraization.isIso_of_affine_sections_bijective _
        (bijective_chartBetaSystem_app B S hS f hf J hJ V G hIcart hIq F hF β n.unop)
  ObjectProperty.isoMk _ (@asIso _ _ _ _ (chartBetaSystem B S hS J hJ V G f hf hIcart hIq F hF β)
    (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hiso))

variable [hVL : IsLocallyNoetherian (chartScheme V)]
    [hgp : _root_.AlgebraicGeometry.IsProper (chartBaseChangeMorphism B S hS f hf V)]
    [hYloc : Fact (HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hJq : J.toSheafOfModules.IsQuasicoherentOnSite)
    (hFF : IsCoherent B S hS Y.1 Y.2 ((baseChangeDirectImage B S hS f hf).obj F))

omit hVN in
include hJ in
/-- The sections over `V` of `α`, read in the base tower and followed by the comparison of
Stacks 088B on the chart, are the sections over `V` of `γ`, read in the completion tower. -/
theorem chartTower_comp_eq_chartGammaTower
    (α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJq).obj ⟨_, hFF⟩)
    (hα : α.hom ≫ directImageCompletionComparison B S hS f hf J hJq hIq ⟨F, hF⟩ hFF =
      directImageChartComparison B S hS f hf (pullbackIdealSubsheaf B S hS f hf J) hIq G.obj
        ⟨F, hF⟩ β) :
    (Functor.whiskerRight α.hom (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)) ≫
      (completionDirectImageTowerIso B S hS f hf J hJ V F hF hJq hFF).hom) ≫
        chartPushforwardCompletionComparisonTower B S hS f hf J V F hF =
      chartGammaTower B S hS J hJ V G f hf hIcart hIq F hF β := by
  rw [Category.assoc, ← directImageCompletionComparisonTower_comp_iso B S hS f hf J hJ hIcart hIq V
    F hF hJq hFF, ← Category.assoc]
  refine congrArg (· ≫ _) ?_
  exact (Functor.whiskerRight_comp _ _ _).symm.trans
    (congrArg (fun φ => Functor.whiskerRight φ _) hα)

include hJ in
/-- **The defining equation of the scheme-side `α`**: the transpose along `affineTilde` of the
sections over `V` of `α`, followed by the comparison `c` of Stacks 088B on the chart, is the map
`γ` of Stacks 088B attached to the scheme-side `β`. -/
theorem chartTildeMap_comp_pushforwardCompletionComparison
    [_root_.AlgebraicGeometry.IsNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
    [_root_.AlgebraicGeometry.IsNoetherian (chartScheme V)]
    (α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJq).obj ⟨_, hFF⟩)
    (hα : α.hom ≫ directImageCompletionComparison B S hS f hf J hJq hIq ⟨F, hF⟩ hFF =
      directImageChartComparison B S hS f hf (pullbackIdealSubsheaf B S hS f hf J) hIq G.obj
        ⟨F, hF⟩ β) :
    (chartTildeMap B S hS J hJ V G f hf F hF hJq hFF α).hom ≫
        @Stacks.Coherent.pushforwardCompletionComparison _ _ hWN hVL
          (chartBaseChangeMorphism B S hS f hf V)
          (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
          (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V))
          (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V)).property
          (chartDirectImageCoherent B S hS f hf V F hF).property =
      Stacks.Coherent.directImageComparison (chartBaseChangeMorphism B S hS f hf V)
        (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
        (chartTildeSystem B S hS J hJ V G)
        (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V))
        (chartBetaIso B S hS f hf J hJ V G hIcart hIq F hF β) := by
  refine NatTrans.ext (funext fun n => ?_)
  apply ((affineTildeChartGlobalSectionsAdjunction B S hS V).homEquiv _ _).injective
  refine ((affineTildeChartGlobalSectionsAdjunction B S hS V).homEquiv_naturality_right
    _ _).trans ?_
  refine (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)).trans ?_
  refine (congrArg (fun φ => NatTrans.app φ n) (chartTower_comp_eq_chartGammaTower B S hS f hf J hJ
    V G hIcart hIq F hF β hJq hFF α hα)).trans ?_
  refine Eq.trans ?_ (congrArg ((affineTildeChartGlobalSectionsAdjunction B S hS V).homEquiv _ _)
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (chartBaseChangeMorphism B S hS f hf V)).homEquiv_unit _ _ _))
  refine Eq.trans ?_ (congrArg ((affineTildeChartGlobalSectionsAdjunction B S hS V).homEquiv _ _)
    (Equiv.apply_symm_apply _ _).symm)
  exact (Equiv.apply_symm_apply _ _).symm

/-- The terms of the completion of a coherent module on a locally Noetherian scheme are
quasi-coherent. -/
theorem _root_.Stacks.Algebraization.isQuasicoherent_completionFunctor_obj_obj {T : Scheme.{u}}
    [IsLocallyNoetherian T] (I : T.IdealSheafData)
    (M : SheafOfModules.CoherentModules T.ringCatSheaf) (k : ℕᵒᵖ) :
    (((Stacks.Algebraization.completionFunctor T I).obj M).obj.obj k).IsQuasicoherent :=
  have := ((Stacks.Algebraization.completionFunctor T I).obj M).property.1 k.unop
  isQuasicoherent_of_isCoherent _

omit hXloc in
include hJ in
/-- The unit of `affineTilde ⊣ Γ` carries the sections over `V` of `α_k` to the global sections of
the scheme-side `α_k`, read through the base tower isomorphism. -/
theorem chartTildeMap_app_unit
    (α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJq).obj ⟨_, hFF⟩) (k : ℕ)
    (x : (G.obj.obj (op k)).val.obj (op V)) :
    ((chartTildeMap B S hS J hJ V G f hf F hF hJq hFF α).hom.app (op k)).val.app (op ⊤)
        (((affineTildeChartGlobalSectionsAdjunction B S hS V).unit.app
          ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op k))) x) =
      completionDirectImageTowerEquiv B S hS f hf J hJ V F hF hJq hFF k
        ((α.hom.app (op k)).val.app (op V) x) :=
  congrArg (fun φ => φ.hom x)
    ((affineTildeChartGlobalSectionsAdjunction B S hS V).unit_comp_map_homEquiv_symm
    ((Functor.whiskerRight α.hom (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)) ≫
      (completionDirectImageTowerIso B S hS f hf J hJ V F hF hJq hFF).hom).app (op k)))

include hJ in
omit hXloc in
/-- A power of an ideal killing the kernel of the scheme-side `α_k` kills the kernel of `α_k` on
the sections over `V`. -/
theorem smul_eq_zero_of_chartTildeMap_kernel
    (α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJq).obj ⟨_, hFF⟩) (k t : ℕ)
    (Kb : (chartScheme V).IdealSheafData)
    (hker : Stacks.Algebraization.idealPowerMultiple Kb t
      (kernel ((chartTildeMap B S hS J hJ V G f hf F hF hJq hFF α).hom.app (op k))) = ⊥)
    {r : chartRing B S hS Y.1 Y.2 V}
    (hr : r ∈ Kb.ideal ⟨⊤, isAffineOpen_top (chartScheme V)⟩ ^ t)
    {x : (G.obj.obj (op k)).val.obj (op V)} (hx : (α.hom.app (op k)).val.app (op V) x = 0) :
    r • x = 0 := by
  have e1 : ((chartTildeMap B S hS J hJ V G f hf F hF hJq hFF α).hom.app (op k)).val.app (op ⊤)
      (((affineTildeChartGlobalSectionsAdjunction B S hS V).unit.app
        ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op k))) x) = 0 :=
    (chartTildeMap_app_unit B S hS f hf J hJ V G F hF hJq hFF α k x).trans
      ((congrArg _ hx).trans (map_zero _))
  refine (bijective_chartTildeAdjunction_unit_app B S hS J V G k).1 ?_
  refine ((((affineTildeChartGlobalSectionsAdjunction B S hS V).unit.app
    ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op k))).hom.map_smul r x).trans ?_)
  exact (Stacks.Coherent.smul_eq_zero_of_app_eq_zero_affine
    ((chartTildeMap B S hS J hJ V G f hf F hF hJq hFF α).hom.app (op k)) hker
    ⟨⊤, isAffineOpen_top (chartScheme V)⟩ hr e1).trans (map_zero _).symm

include hJ hVL in
omit hXloc in
/-- A power of an ideal killing the cokernel of the scheme-side `α_k` carries the sections over
`V` of the target into the image of `α_k`. -/
theorem exists_eq_smul_of_chartTildeMap_cokernel
    (α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJq).obj ⟨_, hFF⟩) (k t : ℕ)
    (Kb : (chartScheme V).IdealSheafData)
    (hcok : Stacks.Algebraization.idealPowerMultiple Kb t
      (cokernel ((chartTildeMap B S hS J hJ V G f hf F hF hJq hFF α).hom.app (op k))) = ⊥)
    {r : chartRing B S hS Y.1 Y.2 V}
    (hr : r ∈ Kb.ideal ⟨⊤, isAffineOpen_top (chartScheme V)⟩ ^ t)
    (y : (((completionFunctor B S hS Y.1 Y.2 J hJq).obj ⟨_, hFF⟩).obj.obj (op k)).val.obj
      (op V)) :
    ∃ x, (α.hom.app (op k)).val.app (op V) x = r • y := by
  have : ((chartTildeSystem B S hS J hJ V G).obj.obj (op k)).IsQuasicoherent :=
    Stacks.Coherent.affineTilde_quasicoherent (chartScheme V) _
  have := @Stacks.Algebraization.isQuasicoherent_completionFunctor_obj_obj (chartScheme V) hVL
    (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
    (chartDirectImageCoherent B S hS f hf V F hF) (op k)
  obtain ⟨x', hx'⟩ := Stacks.Coherent.smul_mem_range_of_cokernel_eq_bot_affine
    ((chartTildeMap B S hS J hJ V G f hf F hF hJq hFF α).hom.app (op k)) hcok
    ⟨⊤, isAffineOpen_top (chartScheme V)⟩ hr
    (completionDirectImageTowerEquiv B S hS f hf J hJ V F hF hJq hFF k y)
  obtain ⟨x, rfl⟩ := (bijective_chartTildeAdjunction_unit_app B S hS J V G k).2 x'
  refine ⟨x, (completionDirectImageTowerEquiv B S hS f hf J hJ V F hF hJq hFF k).injective ?_⟩
  refine (chartTildeMap_app_unit B S hS f hf J hJ V G F hF hJq hFF α k x).symm.trans ?_
  exact hx'.trans ((completionDirectImageTowerEquiv B S hS f hf J hJ V F hF hJq hFF k).map_smul
    r y).symm

include hJ hIcart in
/-- **The kernel–cokernel bound of Stacks 08BD on the sections over an affine chart.**  Over a
Noetherian affine chart `V` of `Y`, the scheme lemma Stacks 088B applied on the chart's scheme
gives one exponent `t` with `𝓚(V) ^ t` killing the kernel of `α_k` on the sections over `V` and
carrying the sections of the target into the image of `α_k`, for every `k`. -/
theorem exists_pow_smul_chart_kernel_cokernel
    (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hK : IsCartesianOnAffineCharts K.toSheafOfModules)
    (hiso : IsIso ((idealComplementSubfunctor B S hS Y K).fromPreimage f.hom))
    (α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJq).obj ⟨_, hFF⟩)
    (hα : α.hom ≫ directImageCompletionComparison B S hS f hf J hJq hIq ⟨F, hF⟩ hFF =
      directImageChartComparison B S hS f hf (pullbackIdealSubsheaf B S hS f hf J) hIq G.obj
        ⟨F, hF⟩ β) :
    ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
      (∀ r ∈ chartSectionIdeal B S hS Y.1 Y.2 K V ^ t, ∀ x : (G.obj.obj (op k)).val.obj (op V),
        (α.hom.app (op k)).val.app (op V) x = 0 → r • x = 0) ∧
      (∀ r ∈ chartSectionIdeal B S hS Y.1 Y.2 K V ^ t,
        ∀ y : (((completionFunctor B S hS Y.1 Y.2 J hJq).obj ⟨_, hFF⟩).obj.obj (op k)).val.obj
          (op V), ∃ x, (α.hom.app (op k)).val.app (op V) x = r • y) := by
  have : _root_.AlgebraicGeometry.IsNoetherian (chartScheme V) :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have : _root_.AlgebraicGeometry.IsNoetherian
      (chartScheme ((smallBaseChange B S hS f hf).obj V)) :=
    { toIsLocallyNoetherian := inferInstance,
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (chartBaseChangeMorphism B S hS f hf V) }
  have : (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V)).IsCoherent :=
    (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V)).property
  obtain ⟨t, ht, h⟩ := Stacks.Coherent.isKernelCokernelAnnihilatedByPower_of_isNoetherian
    (X := chartScheme ((smallBaseChange B S hS f hf).obj V)) (Y := chartScheme V)
    (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
    (idealSheafDataOfChart B S hS Y K hK V) (chartBaseChangeMorphism B S hS f hf V)
    (isIso_chartBaseChangeMorphism_restrict B S hS f hf K hK hiso V)
    (chartTildeSystem B S hS J hJ V G)
    (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V))
    (chartBetaIso B S hS f hf J hJ V G hIcart hIq F hF β)
    (chartTildeMap B S hS J hJ V G f hf F hF hJq hFF α)
    (chartTildeMap_comp_pushforwardCompletionComparison B S hS f hf J hJ V G hIcart hIq F hF β
      hJq hFF α hα)
  have hT : (idealSheafDataOfChart B S hS Y K hK V).ideal ⟨⊤, isAffineOpen_top (chartScheme V)⟩ =
      chartSectionIdeal B S hS Y.1 Y.2 K V :=
    (Scheme.IdealSheafData.ker_subschemeι_app _ ⟨⊤, isAffineOpen_top (chartScheme V)⟩).symm.trans
      (ker_appTop_subschemeι_idealSheafDataOfChart B S hS Y K hK V hV)
  refine ⟨t, ht, fun k => ⟨fun r hr x hx => ?_, fun r hr y => ?_⟩⟩
  · exact smul_eq_zero_of_chartTildeMap_kernel B S hS f hf J hJ V G F hF hJq hFF α k t _ (h k).1
      (hT ▸ hr) hx
  · exact exists_eq_smul_of_chartTildeMap_cokernel B S hS f hf J hJ V G F hF hJq hFF α k t _
      (h k).2 (hT ▸ hr) y

end AlgebraicGeometry.Space
