module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartRestrictionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealAffineChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestrictionOver
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.RelativeSerreVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperRepresentableDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMap
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicDirectImageChartMap
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicLimitMap
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictToChartSchemeSectionsTransport

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraComparison

/-!
# The comparison map of Stacks 08BD on the limit of the sections over an affine chart

Let `f : X ⟶ Y` be a representable proper morphism of algebraic spaces, let `𝓙 ⊆ 𝒪_Y` be a
quasi-coherent sheaf of ideals with inverse image `𝓘 = f⁻¹𝓙 · 𝒪_X`, and let `𝓕` be a coherent
`𝒪_X`-module.  This file proves that the comparison

`c_n : f_*𝓕 / 𝓙 ⁿ⁺¹ f_*𝓕 ⟶ f_*(𝓕 / 𝓘 ⁿ⁺¹ 𝓕)`

of `AlgebraicGeometry.Space.directImageCompletionComparison` becomes an isomorphism on the limit
of the sections over every affine étale chart `V` of `Y`: this is the theorem on formal
functions, read on a chart.

The proof transports the statement to the chart's schemes.  The base change `V ×_Y X` of `V` is
an étale chart of `X` whose scheme is proper over the scheme of `V`
(`AlgebraicGeometry.Space.chartBaseChangeMorphism`).  The chart restriction of `𝓕` to it is a
coherent module whose global sections are the sections of `𝓕` over `V ×_Y X`, the Zariski ideal
`𝓙(V) 𝒪_{V ×_Y X}` generates `𝓘` on every affine open
(`AlgebraicGeometry.Space.map_topIso_inv_ideal_comap_ofIdealTop`), so the completion of the chart
restriction is the chart restriction of the completion
(`AlgebraicGeometry.Space.chartRestrictionCompletionIso`).  Across the resulting isomorphisms of
towers of sections (`AlgebraicGeometry.Space.directImageCompletionTowerIso`,
`AlgebraicGeometry.Space.completionDirectImageTowerIso`) the comparison `c` is the comparison of
Stacks 088B for the proper morphism of schemes
(`AlgebraicGeometry.Space.directImageCompletionComparisonTower_comp_iso`), which is an isomorphism
on limits of global sections by the scheme-level theorem on formal functions.

## Main results

* `AlgebraicGeometry.Space.map_topIso_inv_ideal_comap_ofIdealTop` — the inverse-image ideal over
  the affine opens of the base-changed chart.
* `AlgebraicGeometry.Space.isCoherent_chartRestrictionSheaf` — the chart restriction of a coherent
  module to a chart with locally Noetherian scheme is coherent.
* `AlgebraicGeometry.Space.chartRestrictionCompletionIso` — the completion of the chart
  restriction is the chart restriction of the completion.
* `AlgebraicGeometry.Space.isIso_limMap_directImageCompletionComparisonTower` — **the theorem on
  formal functions on the sections over an affine chart.**

## References

* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)

/-- The cartesian projection `V ×_Y X ⟶ V` of the base change of a chart, on chart schemes. -/
abbrev chartBaseChangeMorphism (V : SmallEtale B S hS Y.1) :
    chartScheme ((smallBaseChange B S hS f hf).obj V) ⟶ chartScheme V :=
  (BigFppfOver.toScheme B S hS).map ((smallBaseChangeProjection B S hS f hf).app V)

/-- For `g : Z ⟶ T` and an open `O` of `Z`, the map `Γ(T, ⊤) ⟶ Γ(O, ⊤)` induced by `g.appLE ⊤ O`
agrees with the composite of `g.appTop` and the global sections of the inclusion `O.ι`. -/
theorem appLE_top_comp_topIso_inv {Z T : Scheme.{u}} (g : Z ⟶ T) (O : Z.Opens)
    (e : O ≤ g ⁻¹ᵁ ⊤) :
    O.topIso.inv.hom.comp (g.appLE ⊤ O e).hom = O.ι.appTop.hom.comp g.appTop.hom := by
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop]
  exact (Category.assoc _ _ _).trans (congrArg (g.app ⊤ ≫ ·)
    ((Z.presheaf.map_comp _ _).symm.trans (congrArg Z.presheaf.map (Subsingleton.elim _ _))))

variable (J : (SheafOfModules.unit (smallEtaleRingSheaf B S hS Y.1 Y.2)).Submodule)

/-- **The Zariski ideal which the base-changed chart inherits from `𝓙` generates the inverse-image
ideal `f⁻¹𝓙 · 𝒪_X` over every affine open.** -/
theorem map_topIso_inv_ideal_comap_ofIdealTop
    (hJ : IsCartesianOnAffineCharts (hF := Y.2) J.toSheafOfModules)
    (V : SmallEtale B S hS Y.1) (hV : IsAffine (chartScheme V))
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).affineOpens) :
    Ideal.map O.1.topIso.inv.hom
        (((Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V)).comap
          (chartBaseChangeMorphism B S hS f hf V)).ideal O) =
      (pullbackIdealSubsheaf B S hS f hf J).obj
        (op ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O.1)) := by
  have e : (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) ≤
      chartBaseChangeMorphism B S hS f hf V ⁻¹ᵁ ⊤ := le_top
  have h1 := Stacks.IdealSheaf.ideal_comap_appLE
    (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
    (chartBaseChangeMorphism B S hS f hf V) ⟨⊤, isAffineOpen_top (chartScheme V)⟩ O e
  refine (congrArg (Ideal.map O.1.topIso.inv.hom) (h1.trans (congrArg _
    (Stacks.Coherent.ofIdealTop_ideal_top (chartScheme V) _)))).trans ?_
  refine (Ideal.map_map _ _).trans ?_
  refine (congrArg (fun φ => Ideal.map φ (chartSectionsIdeal B S hS Y J V))
    (appLE_top_comp_topIso_inv (chartBaseChangeMorphism B S hS f hf V) O.1 e)).trans ?_
  refine Eq.trans ?_ (pullbackIdealSubsheaf_obj_eq_map_of_isAffine B S hS f hf J hJ V hV _
      (chartOpensHom B S hS X _ O.1) O.2).symm
  exact (Ideal.map_map _ _).symm

/-! ### The chart restriction of a coherent module -/

section Coherent

variable (Z : AlgebraicSpaces B S hS)

/-- The chart restriction is functorial. -/
theorem chartRestrictionSheafMap_comp {M N P : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N)
    (ψ : N ⟶ P) (A : SmallEtale B S hS Z.1) :
    chartRestrictionSheafMap B S hS Z (φ ≫ ψ) A =
      chartRestrictionSheafMap B S hS Z φ A ≫ chartRestrictionSheafMap B S hS Z ψ A := rfl

/-- **The chart restriction of a coherent module to a chart with locally Noetherian scheme is
coherent.**  It is isomorphic to the chart transport `AlgebraicGeometry.Space.chartSchemeModule`,
which is. -/
theorem isCoherent_chartRestrictionSheaf (M : Modules.{u, u} B S hS Z.1 Z.2)
    (hM : IsCoherent B S hS Z.1 Z.2 M) (A : SmallEtale B S hS Z.1)
    (hA : IsLocallyNoetherian (chartScheme A)) :
    (chartRestrictionSheaf B S hS Z M A).IsCoherent :=
  Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso
    ((restrictToChartIsoChartSchemeModule B S hS Z M hM.toIsQuasicoherentOnSite A).symm ≪≫
      restrictToChartIsoChartRestrictionSheaf B S hS Z M A)
    (isCoherent_chartSchemeModule_of_isLocallyNoetherian B S hS Z M hM A hA)

/-- The sections over `⊤` of the chart restriction are natural in the module. -/
theorem chartRestrictionSheafTopEquiv_naturality {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N)
    (A : SmallEtale B S hS Z.1) (x : M.val.obj (op A)) :
    chartRestrictionSheafTopEquiv B S hS Z N A (φ.val.app (op A) x) =
      (chartRestrictionSheafMap B S hS Z φ A).val.app (op ⊤)
        (chartRestrictionSheafTopEquiv B S hS Z M A x) :=
  congrArg ULift.up (congrArg (fun ψ => ψ.hom x) (φ.val.naturality (chartOpensTopHom B S hS Z
      A).op)).symm

end Coherent

/-! ### The completion of the chart restriction -/

section ChartCompletion

variable (Z : AlgebraicSpaces B S hS)
    (𝓘 : (SheafOfModules.unit.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))).Submodule)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (hM : IsCoherent B S hS Z.1 Z.2 M)
    (A : SmallEtale B S hS Z.1) [IsLocallyNoetherian (chartScheme A)]
    (Ibar : (chartScheme A).IdealSheafData)
    (hIbar : ∀ O : (chartScheme A).affineOpens,
      Ideal.map O.1.topIso.inv.hom (Ibar.ideal O) =
        chartSectionIdeal B S hS Z.1 Z.2 𝓘 ((chartOpens B S hS A).obj O.1))

/-- The chart restriction of a coherent module, as a coherent module on the chart's scheme. -/
abbrev chartRestrictionCoherent : SheafOfModules.CoherentModules (chartScheme A).ringCatSheaf :=
  ⟨chartRestrictionSheaf B S hS Z M A,
    isCoherent_chartRestrictionSheaf B S hS Z M hM A inferInstance⟩

/-- **The `n`-th term of the completion of the chart restriction is the chart restriction of
`M / 𝓘 ⁿ⁺¹ M`.** -/
def chartRestrictionCompletionIso (n : ℕ) :
    chartRestrictionSheaf B S hS Z (idealPowerQuotient B S hS Z.1 Z.2 𝓘 (n + 1) M) A ≅
      ((Stacks.Algebraization.completionFunctor (chartScheme A) Ibar).obj
        (chartRestrictionCoherent B S hS Z M hM A)).obj.obj (op n) :=
  haveI := isIso_chartRestrictionQuotientHom B S hS Z 𝓘 M A Ibar hIbar (n + 1) hIcart
    hM.toIsQuasicoherentOnSite
  (asIso (chartRestrictionQuotientHom B S hS Z 𝓘 M A Ibar hIbar (n + 1))).symm ≪≫
    eqToIso (Stacks.Algebraization.completionFunctor_obj (chartScheme A) Ibar
      (chartRestrictionCoherent B S hS Z M hM A) n).symm

/-- The chart restriction of the projection onto `M / 𝓘 ⁿ⁺¹ M`, read in the completion of the
chart restriction, is the projection onto the `n`-th term of that completion. -/
theorem chartRestrictionSheafMap_π_comp_chartRestrictionCompletionIso_hom (n : ℕ) :
    chartRestrictionSheafMap B S hS Z
        (cokernel.π (idealPowerMultiple B S hS Z.1 Z.2 𝓘 (n + 1) M).ι) A ≫
      (chartRestrictionCompletionIso B S hS Z 𝓘 hIcart M hM A Ibar hIbar n).hom =
    Stacks.Algebraization.completionProjection (chartScheme A) Ibar
      (chartRestrictionCoherent B S hS Z M hM A) n := by
  have hiso := isIso_chartRestrictionQuotientHom B S hS Z 𝓘 M A Ibar hIbar (n + 1) hIcart
    hM.toIsQuasicoherentOnSite
  change _ ≫ inv (chartRestrictionQuotientHom B S hS Z 𝓘 M A Ibar hIbar (n + 1)) ≫ _ = _
  have h := π_comp_chartRestrictionQuotientHom B S hS Z 𝓘 M A Ibar hIbar (n + 1)
  refine (congrArg (· ≫ _) h.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (@IsIso.hom_inv_id_assoc _ _ _ _ _ hiso _ _)).trans ?_
  rfl

include hIcart hM hIbar in
/-- **The comparison of completions is compatible with the transition maps.** -/
theorem chartRestrictionCompletionIso_naturality {m n : ℕ} (h : m ≤ n) :
    chartRestrictionSheafMap B S hS Z
        (idealPowerQuotientMapOfLE B S hS Z.1 Z.2 𝓘 (Nat.add_le_add_right h 1) M) A ≫
      (chartRestrictionCompletionIso B S hS Z 𝓘 hIcart M hM A Ibar hIbar m).hom =
    (chartRestrictionCompletionIso B S hS Z 𝓘 hIcart M hM A Ibar hIbar n).hom ≫
      ((Stacks.Algebraization.completionFunctor (chartScheme A) Ibar).obj
        (chartRestrictionCoherent B S hS Z M hM A)).obj.map (homOfLE h).op := by
  have hep : Epi (Stacks.Algebraization.completionProjection (chartScheme A) Ibar
      (chartRestrictionCoherent B S hS Z M hM A) n) :=
    Stacks.Algebraization.epi_completionProjection _ _ _ n
  have hn := chartRestrictionSheafMap_π_comp_chartRestrictionCompletionIso_hom B S hS Z 𝓘 hIcart M
    hM A Ibar hIbar n
  have hm := chartRestrictionSheafMap_π_comp_chartRestrictionCompletionIso_hom B S hS Z 𝓘 hIcart M
    hM A Ibar hIbar m
  set e := chartRestrictionCompletionIso B S hS Z 𝓘 hIcart M hM A Ibar hIbar n
  have hinv : Stacks.Algebraization.completionProjection (chartScheme A) Ibar
      (chartRestrictionCoherent B S hS Z M hM A) n ≫ e.inv =
      chartRestrictionSheafMap B S hS Z
        (cokernel.π (idealPowerMultiple B S hS Z.1 Z.2 𝓘 (n + 1) M).ι) A :=
    (congrArg (· ≫ e.inv) hn.symm).trans ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      e.hom_inv_id).trans (Category.comp_id _)))
  have key : e.inv ≫ chartRestrictionSheafMap B S hS Z
        (idealPowerQuotientMapOfLE B S hS Z.1 Z.2 𝓘 (Nat.add_le_add_right h 1) M) A ≫
      (chartRestrictionCompletionIso B S hS Z 𝓘 hIcart M hM A Ibar hIbar m).hom =
      ((Stacks.Algebraization.completionFunctor (chartScheme A) Ibar).obj
        (chartRestrictionCoherent B S hS Z M hM A)).obj.map (homOfLE h).op := by
    refine (@cancel_epi _ _ _ _ _ _ hep _ _).mp ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) hinv).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (chartRestrictionSheafMap_comp B S hS Z _ _ A).symm).trans ?_
    refine (congrArg (fun φ => chartRestrictionSheafMap B S hS Z φ A ≫ _)
      (π_comp_idealPowerQuotientMapOfLE B S hS Z.1 Z.2 𝓘 (Nat.add_le_add_right h 1) M)).trans ?_
    refine hm.trans ?_
    exact (Stacks.Algebraization.completionProjection_naturality_le _ _ _ h).symm
  refine Eq.trans ?_ (congrArg (e.hom ≫ ·) key)
  exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e.hom_inv_id).trans
    (Category.id_comp _))).symm

end ChartCompletion


/-- The chart restriction of a coherent module to the base change of a chart is coherent. -/
private theorem isCoherent_chartRestrictionSheaf_baseChange (V : SmallEtale B S hS Y.1)
    [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) :
    (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V)).IsCoherent :=
  (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V)).property

/-! ### The towers of sections over an affine chart of the target -/

section Towers

variable (J : (SheafOfModules.unit.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (hIcart : IsCartesianOnAffineCharts (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules)
    [hXloc : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hIq : (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS Y.1) [hV : IsAffine (chartScheme V)]
    [hWN : IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)

/-- The Zariski ideal of the chart's scheme of `V ×_Y X` which `𝓙` induces through `V`. -/
abbrev chartBaseChangeIdeal :
    (chartScheme ((smallBaseChange B S hS f hf).obj V)).IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V)).comap
    (chartBaseChangeMorphism B S hS f hf V)

omit hXloc hWN in
include hJ hV in
/-- Over every affine open `O` of the chart's scheme of `V ×_Y X`, the ideal of
`chartBaseChangeIdeal` maps to the ideal of sections of `pullbackIdealSubsheaf` over `O`. -/
theorem map_topIso_inv_chartBaseChangeIdeal
    (O : (chartScheme ((smallBaseChange B S hS f hf).obj V)).affineOpens) :
    Ideal.map O.1.topIso.inv.hom ((chartBaseChangeIdeal B S hS f hf J V).ideal O) =
      chartSectionIdeal B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J)
        ((chartOpens B S hS ((smallBaseChange B S hS f hf).obj V)).obj O.1) :=
  map_topIso_inv_ideal_comap_ofIdealTop B S hS f hf J hJ V hV O

/-- The completion of the chart restriction of `𝓕` over the chart's scheme of `V ×_Y X`, read
through the direct image to the chart's scheme of `V` and its global sections, as a tower. -/
abbrev chartCompletionTower : ℕᵒᵖ ⥤ ModuleCat.{u} (chartRing B S hS Y.1 Y.2 V) :=
  ((Stacks.Algebraization.completionFunctor (chartScheme ((smallBaseChange B S hS f hf).obj V))
      (chartBaseChangeIdeal B S hS f hf J V)).obj
      (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V))).obj ⋙
    Scheme.Modules.pushforward (chartBaseChangeMorphism B S hS f hf V) ⋙
      Stacks.Algebraization.affineSectionFunctor ⟨⊤, isAffineOpen_top (chartScheme V)⟩

/-- The tower of sections over `V` of the direct image of the completion of `𝓕`. -/
abbrev directImageCompletionTower : ℕᵒᵖ ⥤ ModuleCat.{u} (chartRing B S hS Y.1 Y.2 V) :=
  ((completionFunctor B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J) hIq).obj
      ⟨F, hF⟩).obj ⋙
    baseChangeDirectImage B S hS f hf ⋙
      SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)

/-- The comparison of completions of `chartRestrictionCompletionIso` at `V ×_Y X`. -/
abbrev chartBaseChangeCompletionIso (n : ℕ) :=
  chartRestrictionCompletionIso B S hS X (pullbackIdealSubsheaf B S hS f hf J) hIcart F hF
    ((smallBaseChange B S hS f hf).obj V) (chartBaseChangeIdeal B S hS f hf J V)
    (map_topIso_inv_chartBaseChangeIdeal B S hS f hf J hJ V) n

include hJ hIcart in
/-- The global sections of the comparison of completions, composed with the identification of
the sections over the chart with the global sections of the chart restriction. -/
def chartBaseChangeTowerEquiv (n : ℕ) :
    ((idealPowerQuotient B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J) (n + 1) F).val.obj
      (op ((smallBaseChange B S hS f hf).obj V)) : Type u) ≃ₗ[Γ(chartScheme
        ((smallBaseChange B S hS f hf).obj V), ⊤)]
      Γ(((Stacks.Algebraization.completionFunctor (chartScheme ((smallBaseChange B S hS f hf).obj
          V))
        (chartBaseChangeIdeal B S hS f hf J V)).obj
        (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V))).obj.obj
          (op n), ⊤) :=
  (chartRestrictionSheafTopEquiv B S hS X
    (idealPowerQuotient B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J) (n + 1) F)
    ((smallBaseChange B S hS f hf).obj V)).trans
    (Scheme.Modules.sectionsLinearEquiv
      (chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n) ⊤)

/-- **The term at level `n` of the two towers agree**: the sections of `𝓕 / 𝓘 ⁿ⁺¹ 𝓕` over
`V ×_Y X` are the global sections of the `n`-th term of the completion of the chart
restriction. -/
def directImageCompletionTowerEquiv (n : ℕ) :
    (directImageCompletionTower B S hS f hf J hIq V F hF).obj (op n) ≃ₗ[chartRing B S hS Y.1 Y.2 V]
      (chartCompletionTower B S hS f hf J V F hF).obj (op n) where
  toFun x := chartBaseChangeTowerEquiv B S hS f hf J hJ hIcart V F hF n x
  invFun y := (chartBaseChangeTowerEquiv B S hS f hf J hJ hIcart V F hF n).symm y
  map_add' x y := map_add _ x y
  map_smul' r x := (chartBaseChangeTowerEquiv B S hS f hf J hJ hIcart V F hF n).map_smul
    ((chartBaseChangeMorphism B S hS f hf V).appTop r) x
  left_inv x := (chartBaseChangeTowerEquiv B S hS f hf J hJ hIcart V F hF n).symm_apply_apply x
  right_inv y := (chartBaseChangeTowerEquiv B S hS f hf J hJ hIcart V F hF n).apply_symm_apply y

omit hXloc in
/-- The level equivalences are natural in the level. -/
theorem chartBaseChangeTowerEquiv_naturality {m n : ℕ} (h : m ≤ n)
    (x : ((idealPowerQuotient B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J) (n + 1)
        F).val.obj
      (op ((smallBaseChange B S hS f hf).obj V)) : Type u)) :
    chartBaseChangeTowerEquiv B S hS f hf J hJ hIcart V F hF m
        ((idealPowerQuotientMapOfLE B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J)
          (Nat.add_le_add_right h 1) F).val.app (op ((smallBaseChange B S hS f hf).obj V)) x) =
      (((Stacks.Algebraization.completionFunctor (chartScheme ((smallBaseChange B S hS f hf).obj V))
        (chartBaseChangeIdeal B S hS f hf J V)).obj
        (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V))).obj.map
          (homOfLE h).op).val.app (op ⊤)
        (chartBaseChangeTowerEquiv B S hS f hf J hJ hIcart V F hF n x) := by
  have h1 := chartRestrictionSheafTopEquiv_naturality B S hS X
    (idealPowerQuotientMapOfLE B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J)
      (Nat.add_le_add_right h 1) F) ((smallBaseChange B S hS f hf).obj V) x
  have h2 := congrArg (fun φ => φ.val.app (op ⊤) (chartRestrictionSheafTopEquiv B S hS X _
      ((smallBaseChange B S hS f hf).obj V) x))
    (chartRestrictionCompletionIso_naturality B S hS X (pullbackIdealSubsheaf B S hS f hf J)
      hIcart F hF ((smallBaseChange B S hS f hf).obj V) (chartBaseChangeIdeal B S hS f hf J V)
      (map_topIso_inv_chartBaseChangeIdeal B S hS f hf J hJ V) h)
  exact (congrArg ((chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF m).hom.val.app
    (op ⊤)) h1).trans h2

/-- **The tower of sections over `V` of the direct image of the completion of `𝓕` is the tower of
global sections of the completion of the chart restriction of `𝓕` over `V ×_Y X`.** -/
def directImageCompletionTowerIso :
    directImageCompletionTower B S hS f hf J hIq V F hF ≅
      chartCompletionTower B S hS f hf J V F hF :=
  NatIso.ofComponents
    (fun n => (directImageCompletionTowerEquiv B S hS f hf J hJ hIcart hIq V F hF
        n.unop).toModuleIso)
    fun {n m} g => by
      have h : m.unop ≤ n.unop := leOfHom g.unop
      obtain rfl : g = (homOfLE h).op := Subsingleton.elim _ _
      ext x
      exact chartBaseChangeTowerEquiv_naturality B S hS f hf J hJ hIcart V F hF h x

/-- The components of the tower isomorphism. -/
theorem directImageCompletionTowerIso_hom_app (n : ℕ)
    (x : (directImageCompletionTower B S hS f hf J hIq V F hF).obj (op n)) :
    (directImageCompletionTowerIso B S hS f hf J hJ hIcart hIq V F hF).hom.app (op n) x =
      chartBaseChangeTowerEquiv B S hS f hf J hJ hIcart V F hF n x := rfl

section BaseTower

variable [hVN : IsLocallyNoetherian (chartScheme V)]
    [hgp : _root_.AlgebraicGeometry.IsProper (chartBaseChangeMorphism B S hS f hf V)]
    [hYloc : Fact (HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hJq : J.toSheafOfModules.IsQuasicoherentOnSite)
    (hFF : IsCoherent B S hS Y.1 Y.2 ((baseChangeDirectImage B S hS f hf).obj F))

/-- The direct image of the chart restriction of `𝓕` to the chart's scheme of `V`, as a coherent
module. -/
abbrev chartDirectImageCoherent : SheafOfModules.CoherentModules (chartScheme V).ringCatSheaf :=
  haveI : (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V)).IsCoherent :=
    isCoherent_chartRestrictionSheaf B S hS X F hF _ inferInstance
  ⟨(Scheme.Modules.pushforward (chartBaseChangeMorphism B S hS f hf V)).obj
    (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V)),
    AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward _ _⟩

/-- The completion of the direct image of the chart restriction, as a tower of global sections. -/
abbrev chartDirectImageCompletionTower : ℕᵒᵖ ⥤ ModuleCat.{u} (chartRing B S hS Y.1 Y.2 V) :=
  ((Stacks.Algebraization.completionFunctor (chartScheme V)
      (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))).obj
      (chartDirectImageCoherent B S hS f hf V F hF)).obj ⋙
    Stacks.Algebraization.affineSectionFunctor ⟨⊤, isAffineOpen_top (chartScheme V)⟩

/-- The tower of sections over `V` of the completion of `f_*𝓕`. -/
abbrev completionDirectImageTower : ℕᵒᵖ ⥤ ModuleCat.{u} (chartRing B S hS Y.1 Y.2 V) :=
  ((completionFunctor B S hS Y.1 Y.2 J hJq).obj ⟨_, hFF⟩).obj ⋙
    SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)

/-- Global sections over the chart's scheme of `V`, read as modules over the functions on the
chart `V`. -/
abbrev chartGlobalSections : (chartScheme V).Modules ⥤ ModuleCat.{u} (chartRing B S hS Y.1 Y.2 V) :=
  Stacks.Algebraization.affineSectionFunctor ⟨⊤, isAffineOpen_top (chartScheme V)⟩

/-- The global sections over the chart's scheme of `V` of a direct image from the chart's scheme of
`V ×_Y X` are the global sections there, additively. -/
def chartGlobalSectionsPushforwardAddEquiv
    (N : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Modules) :
    (chartGlobalSections B S hS V).obj
        ((Scheme.Modules.pushforward (chartBaseChangeMorphism B S hS f hf V)).obj N) ≃+
      (Γ(N, ⊤) : Type u) :=
  AddEquiv.refl _

omit hXloc hWN hVN hgp hYloc in
/-- `chartGlobalSectionsPushforwardAddEquiv` carries the action of `r` to the action of its image
under the global sections of `chartBaseChangeMorphism`. -/
theorem chartGlobalSectionsPushforwardAddEquiv_smul
    (N : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Modules)
    (r : chartRing B S hS Y.1 Y.2 V)
    (y : (chartGlobalSections B S hS V).obj
        ((Scheme.Modules.pushforward (chartBaseChangeMorphism B S hS f hf V)).obj N)) :
    chartGlobalSectionsPushforwardAddEquiv B S hS f hf V N (r • y) =
      (chartBaseChangeMorphism B S hS f hf V).appTop r •
        chartGlobalSectionsPushforwardAddEquiv B S hS f hf V N y := rfl

/-- The sections over `V` of `f_*𝓕` are the global sections of the direct image of the chart
restriction of `𝓕`. -/
def chartDirectImageSectionsEquiv :
    ((baseChangeDirectImage B S hS f hf).obj F).val.obj (op V) ≃ₗ[chartRing B S hS Y.1 Y.2 V]
      (chartGlobalSections B S hS V).obj (chartDirectImageCoherent B S hS f hf V F hF).obj :=
  let e := chartRestrictionSheafTopEquiv B S hS X F ((smallBaseChange B S hS f hf).obj V)
  let p := chartGlobalSectionsPushforwardAddEquiv B S hS f hf V
    (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V))
  { toFun x := p.symm (e x)
    invFun y := e.symm (p y)
    map_add' x y := (congrArg p.symm (e.map_add x y)).trans (p.symm.map_add _ _)
    map_smul' r x := (congrArg p.symm (e.map_smul ((chartBaseChangeMorphism B S hS f hf V).appTop r)
      x)).trans rfl
    left_inv x := (congrArg e.symm (p.apply_symm_apply (e x))).trans (e.symm_apply_apply x)
    right_inv y := (congrArg p.symm (e.apply_symm_apply (p y))).trans (p.symm_apply_apply y) }

include hJ in
/-- The `n`-th term of the tower of sections over `V` of the completion of `f_*𝓕` is the quotient
of the sections of `f_*𝓕` over `V` by `𝓙(V) ⁿ⁺¹`. -/
def completionDirectImageTowerQuotientEquiv (n : ℕ) :
    (((baseChangeDirectImage B S hS f hf).obj F).val.obj (op V) ⧸
        chartSectionIdeal B S hS Y.1 Y.2 J V ^ (n + 1) •
          (⊤ : Submodule (chartRing B S hS Y.1 Y.2 V)
            (((baseChangeDirectImage B S hS f hf).obj F).val.obj (op V)))) ≃ₗ[chartRing B S hS Y.1
                Y.2 V]
      (completionDirectImageTower B S hS f hf J V F hJq hFF).obj (op n) :=
  (Submodule.quotEquivOfEq _ _ (ker_val_app_idealPowerQuotient_π B S hS Y.1 Y.2 J hJ _
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _
        hFF.toIsQuasicoherentOnSite) (n + 1) hV).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_val_app_idealPowerQuotient_π B S hS Y.1 Y.2
        J hJ _
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _
        hFF.toIsQuasicoherentOnSite) (n + 1) hV))

/-- The projection of the global sections of the direct image of the chart restriction onto the
`n`-th term of their completion, as a linear map over the functions on `V`. -/
abbrev chartDirectImageProjection (n : ℕ) :
    (chartGlobalSections B S hS V).obj (chartDirectImageCoherent B S hS f hf V F hF).obj →ₗ[
      chartRing B S hS Y.1 Y.2 V]
      (chartDirectImageCompletionTower B S hS f hf J V F hF).obj (op n) :=
  ((chartGlobalSections B S hS V).map (Stacks.Algebraization.completionProjection (chartScheme V)
    (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
    (chartDirectImageCoherent B S hS f hf V F hF) n)).hom

/-- The `n`-th term of the scheme-side base tower is the quotient of the global sections of the
direct image of the chart restriction by `𝓙(V) ⁿ⁺¹`. -/
def chartDirectImageTowerQuotientEquiv (n : ℕ) :
    ((chartGlobalSections B S hS V).obj (chartDirectImageCoherent B S hS f hf V F hF).obj ⧸
        chartSectionIdeal B S hS Y.1 Y.2 J V ^ (n + 1) •
          (⊤ : Submodule (chartRing B S hS Y.1 Y.2 V)
            ((chartGlobalSections B S hS V).obj (chartDirectImageCoherent B S hS f hf V F hF).obj)))
      ≃ₗ[chartRing B S hS Y.1 Y.2 V]
      (chartDirectImageCompletionTower B S hS f hf J V F hF).obj (op n) :=
  have hker : chartSectionIdeal B S hS Y.1 Y.2 J V ^ (n + 1) •
      (⊤ : Submodule (chartRing B S hS Y.1 Y.2 V)
        ((chartGlobalSections B S hS V).obj (chartDirectImageCoherent B S hS f hf V F hF).obj)) =
      LinearMap.ker (chartDirectImageProjection B S hS f hf J V F hF n) := by
    have h := Stacks.Algebraization.completionProjection_app_ker (chartScheme V)
      (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
      (chartDirectImageCoherent B S hS f hf V F hF) n ⟨⊤, isAffineOpen_top (chartScheme V)⟩
    have h0 : (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V)).ideal
        ⟨⊤, isAffineOpen_top (chartScheme V)⟩ = chartSectionsIdeal B S hS Y J V :=
      Stacks.Coherent.ofIdealTop_ideal_top (chartScheme V) _
    exact (h.trans (congrArg (fun I : Ideal Γ(chartScheme V, ⊤) =>
      I ^ (n + 1) • (⊤ : Submodule Γ(chartScheme V, ⊤) _)) h0)).symm
  (Submodule.quotEquivOfEq _ _ hker).trans
    (LinearMap.quotKerEquivOfSurjective _
      (Stacks.Algebraization.completionProjection_app_surjective (chartScheme V)
        (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
        (chartDirectImageCoherent B S hS f hf V F hF) n ⟨⊤, isAffineOpen_top (chartScheme V)⟩))

include hJ in
/-- **The two base towers agree levelwise**: both are the quotient of the sections of `f_*𝓕`
over `V` by `𝓙(V) ⁿ⁺¹`. -/
def completionDirectImageTowerEquiv (n : ℕ) :
    (completionDirectImageTower B S hS f hf J V F hJq hFF).obj (op n) ≃ₗ[chartRing B S hS Y.1 Y.2 V]
      (chartDirectImageCompletionTower B S hS f hf J V F hF).obj (op n) :=
  let P : Submodule (chartRing B S hS Y.1 Y.2 V)
      (((baseChangeDirectImage B S hS f hf).obj F).val.obj (op V)) :=
    chartSectionIdeal B S hS Y.1 Y.2 J V ^ (n + 1) • ⊤
  let Q : Submodule (chartRing B S hS Y.1 Y.2 V)
      ((chartGlobalSections B S hS V).obj (chartDirectImageCoherent B S hS f hf V F hF).obj) :=
    chartSectionIdeal B S hS Y.1 Y.2 J V ^ (n + 1) • ⊤
  have hmap : P.map (chartDirectImageSectionsEquiv B S hS f hf V F hF).toLinearMap = Q := by
    simp only [P, Q, Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  (completionDirectImageTowerQuotientEquiv B S hS f hf J hJ V F hJq hFF n).symm.trans
    ((Submodule.Quotient.equiv P Q (chartDirectImageSectionsEquiv B S hS f hf V F hF) hmap).trans
      (chartDirectImageTowerQuotientEquiv B S hS f hf J V F hF n))

omit hXloc in
/-- The base tower equivalence on the class of a section of `f_*𝓕`. -/
theorem completionDirectImageTowerEquiv_π (n : ℕ)
    (x : ((baseChangeDirectImage B S hS f hf).obj F).val.obj (op V)) :
    completionDirectImageTowerEquiv B S hS f hf J hJ V F hF hJq hFF n
        ((cokernel.π (idealPowerMultiple B S hS Y.1 Y.2 J (n + 1)
          ((baseChangeDirectImage B S hS f hf).obj F)).ι).val.app (op V) x) =
      chartDirectImageProjection B S hS f hf J V F hF n
        (chartDirectImageSectionsEquiv B S hS f hf V F hF x) := by
  have h1 : (completionDirectImageTowerQuotientEquiv B S hS f hf J hJ V F hJq hFF n)
      (Submodule.Quotient.mk x) =
      (cokernel.π (idealPowerMultiple B S hS Y.1 Y.2 J (n + 1)
          ((baseChangeDirectImage B S hS f hf).obj F)).ι).val.app (op V) x := rfl
  have h2 := (completionDirectImageTowerQuotientEquiv B S hS f hf J hJ V F hJq hFF
      n).symm_apply_apply
    (Submodule.Quotient.mk x)
  rw [h1] at h2
  exact congrArg (fun q => (chartDirectImageTowerQuotientEquiv B S hS f hf J V F hF n)
    ((Submodule.Quotient.equiv _ _ (chartDirectImageSectionsEquiv B S hS f hf V F hF) (by
      simp only [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])) q)) h2

/-- **The two base towers are isomorphic.** -/
def completionDirectImageTowerIso :
    completionDirectImageTower B S hS f hf J V F hJq hFF ≅
      chartDirectImageCompletionTower B S hS f hf J V F hF :=
  NatIso.ofComponents
    (fun n => (completionDirectImageTowerEquiv B S hS f hf J hJ V F hF hJq hFF n.unop).toModuleIso)
    fun {n m} g => by
      have h : m.unop ≤ n.unop := leOfHom g.unop
      obtain rfl : g = (homOfLE h).op := Subsingleton.elim _ _
      ext y
      obtain ⟨x, rfl⟩ := surjective_val_app_idealPowerQuotient_π B S hS Y.1 Y.2 J hJ _
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _
          hFF.toIsQuasicoherentOnSite) (n.unop + 1) hV y
      have e1 : (completionDirectImageTower B S hS f hf J V F hJq hFF).map (homOfLE h).op
          ((cokernel.π (idealPowerMultiple B S hS Y.1 Y.2 J (n.unop + 1)
            ((baseChangeDirectImage B S hS f hf).obj F)).ι).val.app (op V) x) =
          (cokernel.π (idealPowerMultiple B S hS Y.1 Y.2 J (m.unop + 1)
            ((baseChangeDirectImage B S hS f hf).obj F)).ι).val.app (op V) x :=
        congrArg (fun φ => φ.val.app (op V) x)
          (π_comp_idealPowerQuotientMapOfLE B S hS Y.1 Y.2 J (Nat.add_le_add_right h 1) _)
      have e2 := congrArg
          (fun φ => φ.val.app (op ⊤) (chartDirectImageSectionsEquiv B S hS f hf V F hF x))
        (Stacks.Algebraization.completionProjection_naturality_le (chartScheme V)
          (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
          (chartDirectImageCoherent B S hS f hf V F hF) h)
      exact ((congrArg (completionDirectImageTowerEquiv B S hS f hf J hJ V F hF hJq hFF m.unop)
          e1).trans
        (completionDirectImageTowerEquiv_π B S hS f hf J hJ V F hF hJq hFF m.unop x)).trans
        (e2.symm.trans (congrArg ((chartDirectImageCompletionTower B S hS f hf J V F hF).map
          (homOfLE h).op) (completionDirectImageTowerEquiv_π B S hS f hf J hJ V F hF hJq hFF
            n.unop x).symm))

/-- The comparison `c` of Stacks 08BD on the sections over `V`. -/
abbrev directImageCompletionComparisonTower :
    completionDirectImageTower B S hS f hf J V F hJq hFF ⟶
      directImageCompletionTower B S hS f hf J hIq V F hF :=
  Functor.whiskerRight (directImageCompletionComparison B S hS f hf J hJq hIq ⟨F, hF⟩ hFF)
    (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V))

/-- The comparison of Stacks 088B on the chart's scheme of `V`, on global sections. -/
abbrev chartPushforwardCompletionComparisonTower :
    chartDirectImageCompletionTower B S hS f hf J V F hF ⟶ chartCompletionTower B S hS f hf J V F
        hF :=
  haveI : (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V)).IsCoherent :=
    (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V)).property
  haveI : ((Scheme.Modules.pushforward (chartBaseChangeMorphism B S hS f hf V)).obj
      (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V))).IsCoherent :=
    (chartDirectImageCoherent B S hS f hf V F hF).property
  Functor.whiskerRight (Stacks.Coherent.pushforwardCompletionComparison
    (chartBaseChangeMorphism B S hS f hf V)
    (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
    (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V)))
    (chartGlobalSections B S hS V)

/-- **The comparison of Stacks 08BD on the sections over an affine chart is the comparison of
Stacks 088B on the chart's scheme**, across the two tower isomorphisms. -/
theorem directImageCompletionComparisonTower_comp_iso :
    directImageCompletionComparisonTower B S hS f hf J hIq V F hF hJq hFF ≫
        (directImageCompletionTowerIso B S hS f hf J hJ hIcart hIq V F hF).hom =
      (completionDirectImageTowerIso B S hS f hf J hJ V F hF hJq hFF).hom ≫
        chartPushforwardCompletionComparisonTower B S hS f hf J V F hF := by
  ext n y
  obtain ⟨x, rfl⟩ := surjective_val_app_idealPowerQuotient_π B S hS Y.1 Y.2 J hJ _
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _
      hFF.toIsQuasicoherentOnSite) (n.unop + 1) hV y
  have := isCoherent_chartRestrictionSheaf_baseChange B S hS f hf V F hF
  have : ((Scheme.Modules.pushforward (chartBaseChangeMorphism B S hS f hf V)).obj
      (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V))).IsCoherent :=
    (chartDirectImageCoherent B S hS f hf V F hF).property
  have hc : ((directImageCompletionComparison B S hS f hf J hJq hIq ⟨F, hF⟩ hFF).app n).val.app
      (op V) ((cokernel.π (idealPowerMultiple B S hS Y.1 Y.2 J (n.unop + 1)
        ((baseChangeDirectImage B S hS f hf).obj F)).ι).val.app (op V) x) =
      (cokernel.π (idealPowerMultiple B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J)
        (n.unop + 1) F).ι).val.app (op ((smallBaseChange B S hS f hf).obj V)) x :=
    congrArg (fun φ => φ.val.app (op V) x)
      (π_comp_directImageCompletionComparison_app B S hS f hf J hJq hIq ⟨F, hF⟩ hFF n.unop)
  have hD := chartRestrictionSheafTopEquiv_naturality B S hS X
    (cokernel.π (idealPowerMultiple B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J)
      (n.unop + 1) F).ι) ((smallBaseChange B S hS f hf).obj V) x
  have hQ := congrArg (fun φ => φ.val.app (op ⊤)
      (chartRestrictionSheafTopEquiv B S hS X F ((smallBaseChange B S hS f hf).obj V) x))
    (chartRestrictionSheafMap_π_comp_chartRestrictionCompletionIso_hom B S hS X
      (pullbackIdealSubsheaf B S hS f hf J) hIcart F hF ((smallBaseChange B S hS f hf).obj V)
      (chartBaseChangeIdeal B S hS f hf J V) (map_topIso_inv_chartBaseChangeIdeal B S hS f hf J hJ
          V)
      n.unop)
  have hS' := congrArg
      (fun φ => φ.val.app (op ⊤) (chartDirectImageSectionsEquiv B S hS f hf V F hF x))
    (Stacks.Coherent.pushforwardCompletionComponent_π (chartBaseChangeMorphism B S hS f hf V)
      (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
      (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V)) n.unop)
  refine ((congrArg (chartBaseChangeTowerEquiv B S hS f hf J hJ hIcart V F hF n.unop) hc).trans
    ((congrArg ((chartBaseChangeCompletionIso B S hS f hf J hJ hIcart V F hF n.unop).hom.val.app
      (op ⊤)) hD).trans hQ)).trans ?_
  refine hS'.symm.trans ?_
  exact congrArg (((Stacks.Coherent.pushforwardCompletionComparison
      (chartBaseChangeMorphism B S hS f hf V)
      (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
      (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V))).app n).val.app
        (op ⊤))
    (completionDirectImageTowerEquiv_π B S hS f hf J hJ V F hF hJq hFF n.unop x).symm

/-- **The theorem on formal functions on the sections over an affine chart**: the comparison `c`
of Stacks 08BD becomes an isomorphism on the limit of the sections over an affine chart `V`. -/
theorem isIso_limMap_directImageCompletionComparisonTower
    (hJ' : IsCartesianOnAffineCharts J.toSheafOfModules)
    (hIcart' : IsCartesianOnAffineCharts (hF := X.2)
      (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules) :
    IsIso (limMap (directImageCompletionComparisonTower B S hS f hf J hIq V F hF hJq hFF)) := by
  have : _root_.AlgebraicGeometry.IsNoetherian (chartScheme V) :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have := isCoherent_chartRestrictionSheaf_baseChange B S hS f hf V F hF
  have : IsIso (limMap (chartPushforwardCompletionComparisonTower B S hS f hf J V F hF)) :=
    Stacks.Coherent.isIso_limMap_affineSections_pushforwardCompletionComparison
      (chartBaseChangeMorphism B S hS f hf V)
      (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))
      (chartRestrictionSheaf B S hS X F ((smallBaseChange B S hS f hf).obj V))
  have h : directImageCompletionComparisonTower B S hS f hf J hIq V F hF hJq hFF =
      (completionDirectImageTowerIso B S hS f hf J hJ' V F hF hJq hFF).hom ≫
        chartPushforwardCompletionComparisonTower B S hS f hf J V F hF ≫
          (directImageCompletionTowerIso B S hS f hf J hJ' hIcart' hIq V F hF).inv := by
    rw [← Category.assoc, ← directImageCompletionComparisonTower_comp_iso B S hS f hf J hJ' hIcart'
      hIq V F hF hJq hFF, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, limMap_eq, lim.map_comp, lim.map_comp, ← limMap_eq
    (chartPushforwardCompletionComparisonTower B S hS f hf J V F hF)]
  infer_instance

end BaseTower






end Towers

end AlgebraicGeometry.Space

end
