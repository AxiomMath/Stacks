module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartDirectImageTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionCoherent
public import StacksFrontier.AlgebraicGeometry.C1573Port.PullbackSections.AffineAdjointIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Filtration
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAffineQuotientSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AdicQuotientAffineSections
public import StacksFrontier.AlgebraicGeometry.C1573Port.FormalGeometry.CompletionFunctor.AffineSectionProjection
public import StacksFrontier.AlgebraicGeometry.C1573Port.FormalGeometry.CompletionProper.ExceptionalComparisonMapAdjoint

namespace Stacks.Submodule.C1573
end Stacks.Submodule.C1573
namespace Stacks.Algebraization.C1573
end Stacks.Algebraization.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The adic quotients of a module, read on the chart scheme of a base change

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces, `V` an affine étale chart of
`Y`, `U = V ×_Y X` the base-changed chart and `f_V : U ⟶ V` the morphism of chart schemes.  For a
sheaf of ideals `𝒥 ⊆ 𝒪_Y` cartesian on affine charts let `𝓘 = f⁻¹𝒥 · 𝒪_X` and let `ℐ` be the
inverse image along `f_V` of the ideal sheaf `𝒥(V)~` of the affine scheme `V`.  For a coherent
`𝒪_X`-module `𝓕` with chart restriction `𝓕|_U`, the chart restriction of `𝓕 / 𝓘ⁿ⁺¹𝓕` is
`𝓕|_U / ℐⁿ⁺¹ 𝓕|_U`, compatibly with the projections
(`AlgebraicGeometry.Space.C1573.chartAdicQuotientIso`).

## Main definitions

* `AlgebraicGeometry.Space.C1573.chartBaseChangeIdeal`: the ideal sheaf `ℐ` on the chart scheme
  of `U`.
* `AlgebraicGeometry.Space.C1573.chartAdicQuotientIso`: the identification of the chart
  restriction of `𝓕 / 𝓘ⁿ⁺¹𝓕` with `𝓕|_U / ℐⁿ⁺¹ 𝓕|_U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

/-- The preimage of `I • ⊤` under a linear equivalence is `I • ⊤`. -/
theorem Stacks.Submodule.C1573.comap_equiv_smul_top {A M N : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (I : Ideal A) :
    Submodule.comap e.toLinearMap (I • (⊤ : Submodule A N)) = I • ⊤ := by
  rw [Submodule.comap_equiv_eq_map_symm, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr e.symm.surjective]

/-- A subsheaf contained in the kernel submodule of a morphism of `𝒪_X`-modules is killed by
it. -/
theorem Stacks.Algebraization.C1573.ι_comp_eq_zero_of_le_kernelSubmodule
    {T : AlgebraicGeometry.Scheme.{u}}
    {M N : T.Modules} (h : M ⟶ N) (P : M.Submodule)
    (hP : P ≤ Stacks.Algebraization.kernelSubmodule h) :
    (P.ι : (P.toSheafOfModules : T.Modules) ⟶ M) ≫ h =
      (HasZeroMorphisms.zero (C := T.Modules) (P.toSheafOfModules : T.Modules) N).zero := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  have hx := hP (op U) x.property
  rwa [Stacks.Algebraization.kernelSubmodule_toSubmodule_obj] at hx

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chart restriction of a coherent module to a locally Noetherian chart scheme is
coherent.** -/
theorem C1573.isCoherent_chartZariskiModule (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : IsCoherent B S hS X.1 X.2 M)
    (A : SmallEtale B S hS X.1) (hA : IsLocallyNoetherian (chartScheme A)) :
    SheafOfModules.IsCoherent ((chartZariskiModule B S hS X A).obj M) :=
  Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso'
    ((restrictToChartSchemeIsoChartComparisonPushforward B S hS X A M).symm ≪≫
      restrictToChartSchemeIsoChartSchemeModule B S hS X M hM.toIsQuasicoherentOnSite A)
    (isCoherent_chartSchemeModule_of_isLocallyNoetherian B S hS X M hM A hA)

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
  (V : SmallEtale B S hS Y.1) [IsAffine (chartScheme V)]
  (J : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)

/-- The inverse image along `f_V` of the ideal sheaf `𝒥(V)~` of the affine scheme `V`. -/
abbrev C1573.chartBaseChangeIdeal :
    (chartScheme ((smallBaseChange B S hS f hf).obj V)).IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J)).comap
    (chartBaseChangeSchemeHom B S hS f hf V)

variable [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
  (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)

/-- The chart restriction of a coherent module, as a coherent module on the chart scheme. -/
abbrev C1573.chartCoherentModule :
    AlgebraicGeometry.SheafOfModules.CoherentModules
      (chartScheme ((smallBaseChange B S hS f hf).obj V)).ringCatSheaf :=
  ⟨(chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F,
    isCoherent_chartZariskiModule B S hS X F hF _ inferInstance⟩

omit [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))] in
/-- The chart restriction of `𝓕 / 𝓘ⁿ⁺¹𝓕` is annihilated by `ℐⁿ⁺¹` on every affine open. -/
theorem C1573.chartAdicQuotient_annihilated (n : ℕ)
    (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).affineOpens) :
    (chartBaseChangeIdeal B S hS f hf V J).ideal W ^ (n + 1) •
      (⊤ : Submodule Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W.1)
        Γ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj
          (smallEtaleAdicQuotient B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1) F),
          W.1)) = ⊥ := by
  obtain ⟨W, hW⟩ := W
  refine le_antisymm (Submodule.smul_le.2 fun r hr x _ => ?_) bot_le
  let g : Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W) →+*
      chartRing B S hS X.1 X.2
        (openChartOfComparison B S hS X ((smallBaseChange B S hS f hf).obj V) W) :=
    chartSectionsRingHom B S hS X _ W
  have hmem := (Ideal.map_pow g _ (n + 1)).le (Ideal.mem_map_of_mem g hr)
  rw [show Ideal.map g ((chartBaseChangeIdeal B S hS f hf V J).ideal ⟨W, hW⟩) =
    chartIdeal B S hS X (inverseImageIdeal B S hS f hf J)
      (openChartOfComparison B S hS X ((smallBaseChange B S hS f hf).obj V) W) from
    map_chartSectionsRingHom_ideal_comap B S hS f hf V J hJ W hW] at hmem
  exact isPowAnnihilated_smallEtaleAdicQuotient B S hS X.1 X.2
    (inverseImageIdeal B S hS f hf J) (n + 1) F _ _ hmem x

/-- **The comparison `𝓕|_U / ℐⁿ⁺¹ 𝓕|_U ⟶ (𝓕 / 𝓘ⁿ⁺¹𝓕)|_U`**, induced by the chart restriction of
the projection `𝓕 ⟶ 𝓕 / 𝓘ⁿ⁺¹𝓕`. -/
def C1573.chartAdicQuotientHom (hJ : IsCartesianOnAffineCharts J.toSheafOfModules) (n : ℕ) :
    ((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
        (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n) ⟶
      (chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj
        (smallEtaleAdicQuotient B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1) F) :=
  eqToHom (Stacks.Algebraization.completionFunctor_obj _ _ _ n) ≫
    cokernel.desc (C := (chartScheme ((smallBaseChange B S hS f hf).obj V)).Modules) _
      ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).map
        (smallEtaleAdicQuotientProjection B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J)
          (n + 1) F))
      (Stacks.Algebraization.C1573.ι_comp_eq_zero_of_le_kernelSubmodule _ _
        (Stacks.Coherent.idealPowerMultiple_le_kernelSubmodule _ (n + 1) _
          (chartAdicQuotient_annihilated B S hS f hf V J F n hJ)))

/-- The comparison carries the projection of the chart restriction to the chart restriction of
the projection. -/
theorem C1573.completionProjection_comp_chartAdicQuotientHom
    (hJ : IsCartesianOnAffineCharts J.toSheafOfModules) (n : ℕ) :
    Stacks.Algebraization.completionProjection _ (chartBaseChangeIdeal B S hS f hf V J)
        (chartCoherentModule B S hS f hf V F hF) n ≫
        chartAdicQuotientHom B S hS f hf V J F hF hJ n =
      (chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).map
        (smallEtaleAdicQuotientProjection B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J)
          (n + 1) F) := by
  rw [Stacks.Algebraization.completionProjection, chartAdicQuotientHom]
  refine (Category.assoc (obj := (chartScheme ((smallBaseChange B S hS f hf).obj V)).Modules)
    _ _ _).trans ?_
  have key : ∀ {C : Type (u + 1)} [Category.{u} C] {A P P' D : C} (π : A ⟶ P) (h : P' = P)
      (d : P ⟶ D), π ≫ eqToHom h.symm ≫ eqToHom h ≫ d = π ≫ d := by
    intros
    simp
  exact (key _ _ _).trans
    (cokernel.π_desc (C := (chartScheme ((smallBaseChange B S hS f hf).obj V)).Modules) _ _ _)

/-- **The comparison `𝓕|_U / ℐⁿ⁺¹ 𝓕|_U ⟶ (𝓕 / 𝓘ⁿ⁺¹𝓕)|_U` is an isomorphism**, for `𝒥` cartesian
on affine charts with finitely generated ideals of sections over the affine charts: over an
affine open `W` both sides are the quotient of the sections of `𝓕` over the chart `W` cuts out by
the `(n+1)`-st power of one ideal. -/
theorem C1573.isIso_chartAdicQuotientHom (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS Y J Q).FG) (n : ℕ) :
    IsIso (chartAdicQuotientHom B S hS f hf V J F hF hJ n) := by
  have hIcart := isCartesianOnAffineCharts_pullbackIdealSubsheaf B S hS f hf J hJ hJfg
  have hFcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 F
    hF.toIsQuasicoherentOnSite
  refine Scheme.Modules.C1573.isIso_of_bijective_app_affineOpens _ fun ⟨W, hW⟩ => ?_
  have hWc : IsAffine (chartScheme
      (openChartOfComparison B S hS X ((smallBaseChange B S hS f hf).obj V) W)) := hW
  have hcomp := congrArg (fun k => k.val.app (op W))
    (completionProjection_comp_chartAdicQuotientHom B S hS f hf V J F hF hJ n)
  have hπ := surjective_val_app_idealPowerQuotient_π B S hS X.1 X.2
    (inverseImageIdeal B S hS f hf J) hIcart F hFcart (n + 1) hWc
  have hπk := ker_val_app_idealPowerQuotient_π B S hS X.1 X.2
    (inverseImageIdeal B S hS f hf J) hIcart F hFcart (n + 1) hWc
  have hx : ∀ x : Γ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F, W),
      (chartAdicQuotientHom B S hS f hf V J F hF hJ n).app W
        ((Stacks.Algebraization.completionProjection _ (chartBaseChangeIdeal B S hS f hf V J)
          (chartCoherentModule B S hS f hf V F hF) n).val.app (op W) x) =
      (cokernel.π (idealPowerMultiple B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1)
        F).ι).val.app (op (openChartOfComparison B S hS X ((smallBaseChange B S hS f hf).obj V) W))
          x :=
    fun x => ConcreteCategory.congr_hom hcomp x
  show Function.Bijective ((chartAdicQuotientHom B S hS f hf V J F hF hJ n).app W)
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun z => ?_⟩
  · obtain ⟨x, rfl⟩ := Stacks.Algebraization.completionProjection_app_surjective _
      (chartBaseChangeIdeal B S hS f hf V J) (chartCoherentModule B S hS f hf V F hF) n ⟨W, hW⟩ y
    replace hy := (hx x).symm.trans hy
    let g : Γ(chartScheme ((smallBaseChange B S hS f hf).obj V), W) →+*
        chartRing B S hS X.1 X.2
          (openChartOfComparison B S hS X ((smallBaseChange B S hS f hf).obj V) W) :=
      chartSectionsRingHom B S hS X _ W
    have hg : Ideal.map g ((chartBaseChangeIdeal B S hS f hf V J).ideal ⟨W, hW⟩) =
        chartSectionIdeal B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J)
          (openChartOfComparison B S hS X ((smallBaseChange B S hS f hf).obj V) W) :=
      map_chartSectionsRingHom_ideal_comap B S hS f hf V J hJ W hW
    have hmem : x ∈ (Ideal.map g ((chartBaseChangeIdeal B S hS f hf V J).ideal ⟨W, hW⟩)) ^ (n + 1) •
          (⊤ : Submodule (chartRing B S hS X.1 X.2 (openChartOfComparison B S hS X
            ((smallBaseChange B S hS f hf).obj V) W)) (F.val.obj (op (openChartOfComparison B S hS X
            ((smallBaseChange B S hS f hf).obj V) W)))) := by
      rwa [hg, ← hπk]
    have hmem' := Stacks.Submodule.mem_pow_smul_top_of_mem_map_pow_smul_top g
      (surjective_chartSectionsRingHom B S hS X _ W)
      (show Γ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj
        F, W) ≃+ F.val.obj (op (openChartOfComparison B S hS X
          ((smallBaseChange B S hS f hf).obj V) W)) from AddEquiv.refl _)
      (fun _ _ => rfl) _ (n + 1) hmem
    exact (Stacks.Algebraization.completionProjection_app_ker _
      (chartBaseChangeIdeal B S hS f hf V J) (chartCoherentModule B S hS f hf V F hF) n
        ⟨W, hW⟩).ge hmem'
  · obtain ⟨x, rfl⟩ := hπ z
    exact ⟨_, hx x⟩

/-- **The chart restriction of `𝓕 / 𝓘ⁿ⁺¹𝓕` is `𝓕|_U / ℐⁿ⁺¹ 𝓕|_U`.** -/
def C1573.chartAdicQuotientIso (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS Y J Q).FG) (n : ℕ) :
    ((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
        (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n) ≅
      (chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj
        (smallEtaleAdicQuotient B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1) F) :=
  haveI := isIso_chartAdicQuotientHom B S hS f hf V J F hF hJ hJfg n
  asIso (chartAdicQuotientHom B S hS f hf V J F hF hJ n)

/-- **The sections over `V` of the direct image of `𝓕 / 𝓘ⁿ⁺¹𝓕` are the global sections of
`𝓕|_U / ℐⁿ⁺¹ 𝓕|_U`**, linearly over `Γ(V, 𝒪_V)`. -/
def C1573.chartDirectImageAdicQuotientIso (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS Y J Q).FG) (n : ℕ) :
    (chartSectionsTop B S hS V).obj ((modulePushforward B S hS f).obj
        (smallEtaleAdicQuotient B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1) F)) ≅
      (Stacks.Algebraization.affineSectionFunctor ⟨⊤, isAffineOpen_top (chartScheme V)⟩).obj
        ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).obj
          (((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
            (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n))) :=
  (chartBaseChangeSectionsEquiv B S hS f hf V _).toModuleIso ≪≫
    (Stacks.Algebraization.affineSectionFunctor ⟨⊤, isAffineOpen_top (chartScheme V)⟩).mapIso
      ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).mapIso
        (chartAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).symm)

/-- The identification `chartDirectImageAdicQuotientIso` sends a section `y` of the direct image
of `𝓕 / 𝓘ⁿ⁺¹𝓕` over `V` to the image under the inverse of `chartAdicQuotientIso` of its section
over the chart scheme of `U`. -/
theorem C1573.chartDirectImageAdicQuotientIso_hom_apply
    (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS Y J Q).FG) (n : ℕ)
    (y : ((modulePushforward B S hS f).obj (smallEtaleAdicQuotient B S hS X.1 X.2
      (inverseImageIdeal B S hS f hf J) (n + 1) F)).val.obj (op V)) :
    (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom y =
      (chartAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).inv.app _
        (chartBaseChangeSectionsMap B S hS f hf V _ y) :=
  rfl

/-- Equal morphisms of `𝒪_T`-modules agree on sections. -/
private theorem hom_app_apply_congr {T : AlgebraicGeometry.Scheme.{u}} {M N : T.Modules}
    {a b : M ⟶ N} (h : a = b) (W : T.Opens) (x : Γ(M, W)) :
    Scheme.Modules.Hom.app a W x = Scheme.Modules.Hom.app b W x :=
  h ▸ rfl

/-- The identification of the sections of the direct image of `𝓕 / 𝓘ⁿ⁺¹𝓕` carries the direct
image of the projection to the projection of the chart restriction. -/
theorem C1573.chartDirectImageAdicQuotientIso_hom_projection
    (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS Y J Q).FG) (n : ℕ)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom
        (((modulePushforward B S hS f).map (smallEtaleAdicQuotientProjection B S hS X.1 X.2
          (inverseImageIdeal B S hS f hf J) (n + 1) F)).val.app (op V) x) =
      ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).map
        (Stacks.Algebraization.completionProjection _ (chartBaseChangeIdeal B S hS f hf V J)
          (chartCoherentModule B S hS f hf V F hF) n)).app ⊤
        (chartBaseChangeSectionsMap B S hS f hf V F x) := by
  rw [chartDirectImageAdicQuotientIso_hom_apply, chartBaseChangeSectionsMap_naturality]
  have h2 : (chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).map
      (smallEtaleAdicQuotientProjection B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1)
        F) ≫
      (chartAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).inv =
      Stacks.Algebraization.completionProjection _ (chartBaseChangeIdeal B S hS f hf V J)
        (chartCoherentModule B S hS f hf V F hF) n := by
    rw [← completionProjection_comp_chartAdicQuotientHom B S hS f hf V J F hF hJ n]
    exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      (chartAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom_inv_id) |>.trans
      (Category.comp_id _)
  exact hom_app_apply_congr h2 _ _

omit [IsAffine (chartScheme V)]
  [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))] in
/-- The chart cut out by an open, mapped into the chart cut out by `⊤`, is the chart of the
open. -/
theorem C1573.openChartOfComparisonHom_comp_toChart
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens) :
    openChartOfComparisonHom B S hS X ((smallBaseChange B S hS f hf).obj V) (le_top : W ≤ ⊤) ≫
        openChartOfComparisonToChart B S hS X _ ⊤ =
      openChartOfComparisonToChart B S hS X _ W := by
  refine hom_ext_of_toScheme_map_eq B S hS ?_
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_openChartOfComparisonToChart,
    toScheme_map_openChartOfComparisonToChart, toScheme_map_toOver_map_openChartOfComparisonHom]
  exact Scheme.homOfLE_ι _ _

/-- **The comparison `𝓕|_U / ℐⁿ⁺¹ ≅ (𝓕/𝓘ⁿ⁺¹𝓕)|_U`, at an open `W` of the chart scheme, carries
the restriction to `W` of the image of a section of `f_*(𝓕/𝓘ⁿ⁺¹𝓕)` over `V` to the canonical map
of sections at the chart diagram of `W`.** -/
theorem C1573.chartAdicQuotientHom_app_restrict (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS Y J Q).FG) (n : ℕ)
    (W : (chartScheme ((smallBaseChange B S hS f hf).obj V)).Opens)
    (y : ((modulePushforward B S hS f).obj (smallEtaleAdicQuotient B S hS X.1 X.2
      (inverseImageIdeal B S hS f hf J) (n + 1) F)).val.obj (op V)) :
    (chartAdicQuotientHom B S hS f hf V J F hF hJ n).app W
        ((((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n)).presheaf.map
            (homOfLE (le_top : W ≤ ⊤)).op
          ((chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom y)) =
      modulePushforwardCounitApp B S hS f _ (baseChangeOpenChartDiagram B S hS f hf V W) y := by
  rw [chartDirectImageAdicQuotientIso_hom_apply]
  have h1 := ConcreteCategory.congr_hom
    ((chartAdicQuotientHom B S hS f hf V J F hF hJ n).mapPresheaf.naturality
      (homOfLE (le_top : W ≤ ⊤)).op)
    ((chartAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).inv.app ⊤
      (chartBaseChangeSectionsMap B S hS f hf V _ y))
  refine h1.trans ?_
  have h2 := hom_app_apply_congr (chartAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).inv_hom_id
    ⊤ (chartBaseChangeSectionsMap B S hS f hf V _ y)
  refine (congrArg (fun z =>
    ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj
      (smallEtaleAdicQuotient B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1)
        F)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op z) h2).trans ?_
  have hcond : (SmallEtale.toOver B S hS X.1).map (openChartOfComparisonToChart B S hS X _ W) ≫
      (baseChangeChartDiagram B S hS f hf V).g =
      (baseChangeOpenChartDiagram B S hS f hf V W).g ≫ (SmallEtale.toOver B S hS Y.1).map (𝟙 V) :=
    (Category.comp_id _).symm.trans
      (congrArg (fun k => (baseChangeOpenChartDiagram B S hS f hf V W).g ≫ k)
        ((SmallEtale.toOver B S hS Y.1).map_id V).symm)
  have h3 := modulePushforwardCounitApp_naturality B S hS f
    (smallEtaleAdicQuotient B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1) F)
    (baseChangeChartDiagram B S hS f hf V) (baseChangeOpenChartDiagram B S hS f hf V W)
    (openChartOfComparisonToChart B S hS X _ W) (𝟙 V) hcond y
  have h4 : ((modulePushforward B S hS f).obj (smallEtaleAdicQuotient B S hS X.1 X.2
      (inverseImageIdeal B S hS f hf J) (n + 1) F)).val.map (𝟙 V).op y = y :=
    ConcreteCategory.congr_hom (((modulePushforward B S hS f).obj (smallEtaleAdicQuotient B S hS
      X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1) F)).val.presheaf.map_id (op V)) y
  have h3' := (congrArg (modulePushforwardCounitApp B S hS f
    (smallEtaleAdicQuotient B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1) F)
    (baseChangeOpenChartDiagram B S hS f hf V W)) h4).symm.trans h3
  refine Eq.trans ?_ h3'.symm
  exact (PresheafOfModules.map_comp_apply
    (smallEtaleAdicQuotient B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1) F).val
    (openChartOfComparisonToChart B S hS X ((smallBaseChange B S hS f hf).obj V) ⊤).op
    (openChartOfComparisonHom B S hS X ((smallBaseChange B S hS f hf).obj V) (le_top : W ≤ ⊤)).op
    _).symm.trans (PresheafOfModules.congr_map_apply _
      (op_comp.symm.trans (congrArg Quiver.Hom.op
        (openChartOfComparisonHom_comp_toChart B S hS f hf V W))) _)

section DirectImage

attribute [local instance] Stacks.Algebraization.sectionsModuleΓSheafVal
  Stacks.Algebraization.sectionsModuleΓ

variable [IsNoetherianRing Γ(chartScheme V, ⊤)]

namespace C1573
/-- The affine chart scheme of `V` with Noetherian ring of global sections is Noetherian. -/
instance : _root_.AlgebraicGeometry.IsNoetherian (chartScheme V) :=
  haveI := Stacks.Coherent.isLocallyNoetherian_of_isNoetherianRing_top (chartScheme V)
  ⟨⟩

end C1573
omit [IsAffine (chartScheme V)]
  [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
  [IsNoetherianRing Γ(chartScheme V, ⊤)] in
/-- The morphism of chart schemes `f_V : U ⟶ V` is proper when `f` is. -/
theorem C1573.isProper_chartBaseChangeSchemeHom (hfp : IsProper B S hS f.hom) :
    _root_.AlgebraicGeometry.IsProper (chartBaseChangeSchemeHom B S hS f hf V) :=
  isProper_toScheme_smallBaseChangeProjection B S hS f hf hfp V

variable (hfp : IsProper B S hS f.hom)

include hfp hF in
/-- For `f` proper and `𝓕` coherent, the direct image along `f_V` of the chart restriction
`𝓕|_U` is coherent. -/
theorem C1573.isCoherent_pushforward_chartZariskiModule :
    ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).obj
      ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F)).IsCoherent :=
  have := isProper_chartBaseChangeSchemeHom B S hS f hf V hfp
  have := isCoherent_chartZariskiModule B S hS X F hF ((smallBaseChange B S hS f hf).obj V)
    inferInstance
  AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward _ _

/-- The direct image along `f_V` of the chart restriction of `𝓕`, as a coherent module. -/
abbrev C1573.chartPushforwardCoherent :
    AlgebraicGeometry.SheafOfModules.CoherentModules (chartScheme V).ringCatSheaf :=
  ⟨(Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).obj
      ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F),
    isCoherent_pushforward_chartZariskiModule B S hS f hf V F hF hfp⟩

variable (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
  (hM : IsCartesianOnAffineCharts ((modulePushforward B S hS f).obj F))

/-- The sections over `V` of `(f_*𝓕) / 𝒥ⁿ⁺¹(f_*𝓕)` are `(f_*𝓕)(V) / 𝒥(V)ⁿ⁺¹`, read over
`Γ(V, 𝒪_V)`. -/
def C1573.chartAdicQuotientSectionsEquiv (n : ℕ) :
    (chartSectionsTop B S hS V).obj (smallEtaleAdicQuotient B S hS Y.1 Y.2 J (n + 1)
        ((modulePushforward B S hS f).obj F)) ≃ₗ[Γ(chartScheme V, ⊤)]
      (chartSectionsTop B S hS V).obj ((modulePushforward B S hS f).obj F) ⧸
        (chartTopIdeal B S hS V J ^ (n + 1) •
          (⊤ : Submodule Γ(chartScheme V, ⊤)
            ((chartSectionsTop B S hS V).obj ((modulePushforward B S hS f).obj F)))) :=
  adicQuotientSectionsEquivOfIsAffine B S hS Y.1 Y.2 J hJ _ hM (n + 1) ‹IsAffine (chartScheme V)›

/-- The projection of the global sections of `f_{V*}𝓕|_U` onto those of its `n`-th completion
term, read on the sections of `f_*𝓕` over `V`. -/
def C1573.chartPushforwardProjection (n : ℕ) :
    (chartSectionsTop B S hS V).obj ((modulePushforward B S hS f).obj F) →ₗ[Γ(chartScheme V, ⊤)]
      Γ(((Stacks.Algebraization.completionFunctor _
          (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
            (chartPushforwardCoherent B S hS f hf V F hF hfp)).obj.obj (op n), ⊤) :=
  (Scheme.Modules.sectionsLinearMap (Stacks.Algebraization.completionProjection _ _
      (chartPushforwardCoherent B S hS f hf V F hF hfp) n) ⊤).comp
    (chartBaseChangeSectionsEquiv B S hS f hf V F).toLinearMap

/-- `chartPushforwardProjection` applied to a section `x` of `f_*𝓕` over `V` is the projection
onto the `n`-th completion term of the corresponding global section of `f_{V*}𝓕|_U`. -/
theorem C1573.chartPushforwardProjection_apply (n : ℕ)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    chartPushforwardProjection B S hS f hf V J F hF hfp n x =
      Scheme.Modules.Hom.app (Stacks.Algebraization.completionProjection _
        (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
        (chartPushforwardCoherent B S hS f hf V F hF hfp) n) ⊤
        (chartBaseChangeSectionsMap B S hS f hf V F x) :=
  rfl

/-- The projection `chartPushforwardProjection` is surjective. -/
theorem C1573.surjective_chartPushforwardProjection (n : ℕ) :
    Function.Surjective (chartPushforwardProjection B S hS f hf V J F hF hfp n) :=
  (Stacks.Algebraization.completionProjection_app_surjective _ _
    (chartPushforwardCoherent B S hS f hf V F hF hfp) n ⟨⊤, isAffineOpen_top _⟩).comp
    (chartBaseChangeSectionsEquiv B S hS f hf V F).surjective

/-- The kernel of `chartPushforwardProjection` is `𝒥(V)ⁿ⁺¹ • ⊤`. -/
theorem C1573.ker_chartPushforwardProjection (n : ℕ) :
    LinearMap.ker (chartPushforwardProjection B S hS f hf V J F hF hfp n) =
      chartTopIdeal B S hS V J ^ (n + 1) • ⊤ := by
  have h := Stacks.Algebraization.completionProjection_app_ker _
    (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
    (chartPushforwardCoherent B S hS f hf V F hF hfp) n ⟨⊤, isAffineOpen_top _⟩
  rw [Stacks.Coherent.ofIdealTop_ideal_top] at h
  have h' : LinearMap.ker (Scheme.Modules.sectionsLinearMap
      (Stacks.Algebraization.completionProjection _
        (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
        (chartPushforwardCoherent B S hS f hf V F hF hfp) n) ⊤) =
        chartTopIdeal B S hS V J ^ (n + 1) • ⊤ :=
    SetLike.ext fun x => SetLike.ext_iff.mp h x
  rw [chartPushforwardProjection, LinearMap.ker_comp, h']
  exact Stacks.Submodule.C1573.comap_equiv_smul_top _ _

/-- **The sections over `V` of `(f_*𝓕) / 𝒥ⁿ⁺¹(f_*𝓕)` are the global sections of the `n`-th term
of the completion of `f_{V*}𝓕|_U` along `𝒥(V)~`.** -/
def C1573.chartPushforwardAdicQuotientEquiv (n : ℕ) :
    (chartSectionsTop B S hS V).obj (smallEtaleAdicQuotient B S hS Y.1 Y.2 J (n + 1)
        ((modulePushforward B S hS f).obj F)) ≃ₗ[Γ(chartScheme V, ⊤)]
      Γ(((Stacks.Algebraization.completionFunctor _
          (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
            (chartPushforwardCoherent B S hS f hf V F hF hfp)).obj.obj (op n), ⊤) :=
  (chartAdicQuotientSectionsEquiv B S hS f V J F hJ hM n).trans
    ((Submodule.quotEquivOfEq _ _
      (ker_chartPushforwardProjection B S hS f hf V J F hF hfp n).symm).trans
      (LinearMap.quotKerEquivOfSurjective _
        (surjective_chartPushforwardProjection B S hS f hf V J F hF hfp n)))

/-- The identification carries the projection of `f_*𝓕` to the projection of `f_{V*}𝓕|_U`. -/
theorem C1573.chartPushforwardAdicQuotientEquiv_projection (n : ℕ)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op V)) :
    chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n
        ((smallEtaleAdicQuotientProjection B S hS Y.1 Y.2 J (n + 1)
          ((modulePushforward B S hS f).obj F)).val.app (op V) x) =
      chartPushforwardProjection B S hS f hf V J F hF hfp n x := by
  have h : chartAdicQuotientSectionsEquiv B S hS f V J F hJ hM n
      ((smallEtaleAdicQuotientProjection B S hS Y.1 Y.2 J (n + 1)
        ((modulePushforward B S hS f).obj F)).val.app (op V) x) = Submodule.Quotient.mk x :=
    adicQuotientSectionsEquivOfIsAffine_projection B S hS Y.1 Y.2 J hJ _ hM (n + 1)
      ‹IsAffine (chartScheme V)› x
  exact (congrArg (fun z => ((Submodule.quotEquivOfEq _ _
    (ker_chartPushforwardProjection B S hS f hf V J F hF hfp n).symm).trans
      (LinearMap.quotKerEquivOfSurjective _
        (surjective_chartPushforwardProjection B S hS f hf V J F hF hfp n))) z) h).trans rfl

/-- **The comparison `(f_*𝓕)/𝒥ⁿ⁺¹ ⟶ f_*(𝓕/𝓘ⁿ⁺¹𝓕)` on the sections over `V` is the scheme
comparison `(f_{V*}𝓕|_U)^ ⟶ f_{V*}(𝓕|_U^)` of Stacks 088B on global sections**, through the two
identifications of sections. -/
theorem C1573.chartDirectImageAdicQuotientIso_comparison
    (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS Y J Q).FG) (n : ℕ)
    (y : (smallEtaleAdicQuotient B S hS Y.1 Y.2 J (n + 1)
      ((modulePushforward B S hS f).obj F)).val.obj (op V)) :
    haveI := isCoherent_chartZariskiModule B S hS X F hF ((smallBaseChange B S hS f hf).obj V)
      inferInstance
    haveI := isCoherent_pushforward_chartZariskiModule B S hS f hf V F hF hfp
    (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom
        ((directImageQuotientComparison B S hS f hf J F (n + 1)).val.app (op V) y) =
      (Scheme.Modules.Hom.app ((Stacks.Coherent.pushforwardCompletionComparison
        (chartBaseChangeSchemeHom B S hS f hf V)
        (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
        ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F)).app (op n)) ⊤
        (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n y) :
        ↑((Stacks.Algebraization.affineSectionFunctor ⟨⊤, isAffineOpen_top (chartScheme V)⟩).obj
          ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).obj
            (((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
              (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n))))) := by
  have := isCoherent_chartZariskiModule B S hS X F hF ((smallBaseChange B S hS f hf).obj V)
    inferInstance
  have := isCoherent_pushforward_chartZariskiModule B S hS f hf V F hF hfp
  obtain ⟨x, rfl⟩ : ∃ x, (smallEtaleAdicQuotientProjection B S hS Y.1 Y.2 J (n + 1)
      ((modulePushforward B S hS f).obj F)).val.app (op V) x = y :=
    surjective_val_app_idealPowerQuotient_π B S hS Y.1 Y.2 J hJ _ hM (n + 1)
      ‹IsAffine (chartScheme V)› y
  have h1 := congrArg (fun k => k.val.app (op V) x)
    (projection_directImageQuotientComparison B S hS f hf J F (n + 1))
  refine (congrArg (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom h1).trans ?_
  refine (chartDirectImageAdicQuotientIso_hom_projection B S hS f hf V J F hF hJ hJfg n x).trans ?_
  refine Eq.trans ?_ (congrArg (Scheme.Modules.Hom.app
      ((Stacks.Coherent.pushforwardCompletionComparison
        (chartBaseChangeSchemeHom B S hS f hf V)
        (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
        ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F)).app (op n)) ⊤)
    (chartPushforwardAdicQuotientEquiv_projection B S hS f hf V J F hF hfp hJ hM n x).symm)
  rw [chartPushforwardProjection_apply]
  have h2 : Stacks.Algebraization.completionProjection _
      (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
      (chartPushforwardCoherent B S hS f hf V F hF hfp) n ≫
        (Stacks.Coherent.pushforwardCompletionComparison (chartBaseChangeSchemeHom B S hS f hf V)
          (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
          ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F)).app (op n) =
      (Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).map
        (Stacks.Algebraization.completionProjection _ (chartBaseChangeIdeal B S hS f hf V J)
          (chartCoherentModule B S hS f hf V F hF) n) :=
    Stacks.Coherent.pushforwardCompletionComponent_π
      (chartBaseChangeSchemeHom B S hS f hf V)
      (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
      ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F) n
  exact (hom_app_apply_congr h2 ⊤ (chartBaseChangeSectionsMap B S hS f hf V F x)).symm

end DirectImage

end AlgebraicGeometry.Space
