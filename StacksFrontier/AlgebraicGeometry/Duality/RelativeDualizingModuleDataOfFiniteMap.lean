module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleDataOfFinite
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparisonPushout

/-!
# Relative dualizing module data along a map of finite factorizations

Let `f = i₁ ≫ g₁ = i₂ ≫ h ≫ g₁ : Y ⟶ X` be two factorizations of `f` into an open immersion
followed by a finite morphism, related by a finite `h : Y₂ ⟶ Y₁` over `X` with `i₂ ≫ h = i₁`.
Let `M₁`, `M₂` be quasi-coherent modules on `Y₁`, `Y₂` with traces `t₁ : g₁_*M₁ ⟶ 𝒪_X` and
`t₂ : (h ≫ g₁)_*M₂ ⟶ 𝒪_X` inducing the dualities of
`Stacks.Discriminant.RelativeDualizingModuleData.ofFiniteTrace`, and `τ : h_*M₂ ⟶ M₁` with
`t₂ = t₁ ∘ g₁_*τ`. If `N ≅ M₁|_Y` and `N ≅ M₂|_Y` are compatible with `τ`, the two chart
identifications of `N` with the algebraic relative dualizing modules agree.

## Main results

* `Stacks.Discriminant.ofFiniteTraceLocalEquiv_eq_of_map`: the two chart identifications agree,
  given the pushout of the rings of the chart.
* `Stacks.Discriminant.isPushout_appLE_of_map`: that pushout, when `i₂ ≫ h = i₁` is cartesian.
* `Stacks.Discriminant.ofFiniteTraceLocalEquiv_eq_of_isPullback`: the two combined.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

variable {X Y Y₁ Y₂ : Scheme.{u}} {f : Y ⟶ X} {g₁ : Y₁ ⟶ X} {i₁ : Y ⟶ Y₁} {i₂ : Y ⟶ Y₂}
  [IsOpenImmersion i₁] [IsOpenImmersion i₂] [IsFinite g₁] (h : Y₂ ⟶ Y₁) [IsFinite h]
  (hig₁ : i₁ ≫ g₁ = f) (hih : i₂ ≫ h = i₁)
  (M₁ : Y₁.Modules) [M₁.IsQuasicoherent] (M₂ : Y₂.Modules) [M₂.IsQuasicoherent]
  (t₁ : (Scheme.Modules.pushforward g₁).obj M₁ ⟶ SheafOfModules.unit X.ringCatSheaf)
  (t₂ : (Scheme.Modules.pushforward (h ≫ g₁)).obj M₂ ⟶ SheafOfModules.unit X.ringCatSheaf)
  (hbij₁ : ∀ U : X.affineOpens, Function.Bijective (traceDual g₁ t₁ U.1))
  (hbij₂ : ∀ U : X.affineOpens, Function.Bijective (traceDual (h ≫ g₁) t₂ U.1))
  {N : Y.Modules} (e₁ : N ≅ M₁.restrict i₁) (e₂ : N ≅ M₂.restrict i₂)
  (τ : (Scheme.Modules.pushforward h).obj M₂ ⟶ M₁)

omit [IsOpenImmersion i₁] [IsOpenImmersion i₂] [IsFinite g₁] [IsFinite h] in
include hig₁ hih in
/-- The second factorization is a factorization of `f`. -/
theorem comp_comp_of_map : i₂ ≫ h ≫ g₁ = f := by
  rw [← Category.assoc, hih, hig₁]

omit [IsOpenImmersion i₂] [IsFinite h] in
include hih in
/-- An open of `Y` over `W ⊆ Y₁` lies over `h⁻¹W ⊆ Y₂`. -/
theorem le_preimage_of_map {W : Y₁.Opens} {V : Y.Opens} (hV : V ≤ i₁ ⁻¹ᵁ W) :
    V ≤ i₂ ⁻¹ᵁ (h ⁻¹ᵁ W) := by
  subst hih
  exact hV

omit [IsOpenImmersion i₂] in
/-- **The chart pushout of a map of finite factorizations.** If `h⁻¹(i₁ Y) = i₂ Y`, i.e. the square
`i₂ ≫ h = i₁` is cartesian, then on a chart `V ⊆ f⁻¹U` the square of rings
`Γ(Y₁, g₁⁻¹U) → Γ(Y₂, h⁻¹g₁⁻¹U) → Γ(Y, V)` is a pushout: `Γ(Y₂, h⁻¹g₁⁻¹U) ⊗ Γ(Y, V) = Γ(Y, V)`. -/
theorem isPushout_appLE_of_map (sq : IsPullback i₂ (𝟙 Y) h i₁) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    IsPushout (h.appLE (g₁ ⁻¹ᵁ U.1) (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) le_rfl)
      (i₁.appLE (g₁ ⁻¹ᵁ U.1) V.1 (le_preimage_preimage hig₁ hVU))
      (i₂.appLE (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) V.1
        (le_preimage_of_map h (sq.w.trans (Category.id_comp _)) (le_preimage_preimage hig₁ hVU)))
      (𝟙 Γ(Y, V.1)) := by
  have hih : i₂ ≫ h = i₁ := sq.w.trans (Category.id_comp _)
  have hle := le_preimage_preimage hig₁ hVU
  have hUY : V.1 = i₂ ⁻¹ᵁ (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) ⊓ (𝟙 Y) ⁻¹ᵁ V.1 :=
    (inf_eq_right.mpr (le_preimage_of_map h hih hle)).symm
  have hsq := Scheme.Hom.isPullback_resLE sq (US := g₁ ⁻¹ᵁ U.1) (UT := V.1)
    (UX := h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) hle le_rfl hUY
  have hW : IsAffineOpen (g₁ ⁻¹ᵁ U.1) := U.2.preimage g₁
  have : IsAffine (g₁ ⁻¹ᵁ U.1).toScheme := hW
  have : IsAffine (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)).toScheme := hW.preimage h
  have : IsAffine V.1.toScheme := V.2
  have hr := isPushout_appTop_of_isPullback hsq
  have hid : Scheme.Hom.appLE (𝟙 Y) V.1 V.1 (by exact hUY.le.trans inf_le_right) =
      𝟙 Γ(Y, V.1) :=
    (Scheme.Hom.appLE_eq_app (𝟙 Y) (U := V.1)).trans (Scheme.Hom.id_app V.1)
  rw [← hid]
  refine hr.of_iso (g₁ ⁻¹ᵁ U.1).topIso (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)).topIso V.1.topIso V.1.topIso
    ?_ ?_ ?_ ?_
  · exact (arrowResLEAppIso h _ _ le_rfl).hom.w.symm
  · exact (arrowResLEAppIso i₁ _ _ hle).hom.w.symm
  · exact (arrowResLEAppIso i₂ _ _ _).hom.w.symm
  · exact (arrowResLEAppIso (𝟙 Y) _ _ _).hom.w.symm

/-- On sections, `i₂.appLE ∘ h.appLE` is `i₁.appLE` when `i₂ ≫ h = i₁`. -/
private theorem appLE_appLE_apply_of_map {i₂ : Y ⟶ Y₂} (h : Y₂ ⟶ Y₁) (hih : i₂ ≫ h = i₁)
    {W : Y₁.Opens} {V : Y.Opens} (hV : V ≤ i₁ ⁻¹ᵁ W) (c : Γ(Y₁, W)) :
    (i₂.appLE (h ⁻¹ᵁ W) V (le_preimage_of_map h hih hV)).hom
      ((h.appLE W (h ⁻¹ᵁ W) le_rfl).hom c) = (i₁.appLE W V hV).hom c := by
  subst hih
  exact RingHom.congr_fun (CommRingCat.hom_ext_iff.mp
    (Scheme.Hom.appLE_comp_appLE i₂ h _ _ V le_rfl (le_preimage_of_map h rfl hV))) c

/-- The `Γ(X, U)`-algebra map `Γ(Y₁, g₁⁻¹U) → Γ(Y₂, (h ≫ g₁)⁻¹U)` induced by `h`. -/
private def appLEAlgHom (U : X.Opens) :
    letI : Algebra Γ(X, U) Γ(Y₁, g₁ ⁻¹ᵁ U) := (g₁.appLE U (g₁ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(Y₂, (h ≫ g₁) ⁻¹ᵁ U) :=
      ((h ≫ g₁).appLE U ((h ≫ g₁) ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    Γ(Y₁, g₁ ⁻¹ᵁ U) →ₐ[Γ(X, U)] Γ(Y₂, (h ≫ g₁) ⁻¹ᵁ U) :=
  letI : Algebra Γ(X, U) Γ(Y₁, g₁ ⁻¹ᵁ U) := (g₁.appLE U (g₁ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI : Algebra Γ(X, U) Γ(Y₂, (h ≫ g₁) ⁻¹ᵁ U) :=
    ((h ≫ g₁).appLE U ((h ≫ g₁) ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  { (h.appLE (g₁ ⁻¹ᵁ U) (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U)) le_rfl).hom with
    commutes' := fun a =>
      (RingHom.congr_fun (CommRingCat.hom_ext_iff.mp
        (Scheme.Hom.appLE_comp_appLE h g₁ U (g₁ ⁻¹ᵁ U) _ le_rfl le_rfl)) a) }

omit [IsFinite g₁] [IsFinite h] [M₁.IsQuasicoherent] [M₂.IsQuasicoherent] in
/-- If `τ` carries the trace `t₂` to `t₁` over `U`, then the trace dual of `s` along `h ≫ g₁`,
composed with `appLEAlgHom h U`, is the trace dual of `τ s` along `g₁`. -/
private theorem traceDual_comp_appLEAlgHom (U : X.Opens)
    (htr : ∀ s : Γ(M₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U)),
      traceApp (h ≫ g₁) t₂ U s = traceApp g₁ t₁ U (τ.app (g₁ ⁻¹ᵁ U) s))
    (s : Γ(M₂, (h ≫ g₁) ⁻¹ᵁ U)) :
    letI : Algebra Γ(X, U) Γ(Y₁, g₁ ⁻¹ᵁ U) := (g₁.appLE U (g₁ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    letI : Algebra Γ(X, U) Γ(Y₂, (h ≫ g₁) ⁻¹ᵁ U) :=
      ((h ≫ g₁).appLE U ((h ≫ g₁) ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    (traceDual (h ≫ g₁) t₂ U s).comp (appLEAlgHom h U).toLinearMap =
      traceDual g₁ t₁ U (τ.app (g₁ ⁻¹ᵁ U) s) := by
  let : Algebra Γ(X, U) Γ(Y₁, g₁ ⁻¹ᵁ U) := (g₁.appLE U (g₁ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(Y₂, (h ≫ g₁) ⁻¹ᵁ U) :=
    ((h ≫ g₁).appLE U ((h ≫ g₁) ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  refine LinearMap.ext fun c => ?_
  change traceApp (h ≫ g₁) t₂ U (appLEAlgHom h U c • s) =
    traceApp g₁ t₁ U (c • τ.app (g₁ ⁻¹ᵁ U) s)
  refine (htr (appLEAlgHom h U c • s)).trans (congrArg (traceApp g₁ t₁ U) ?_)
  have hrc : appLEAlgHom h U c = (h.app (g₁ ⁻¹ᵁ U)).hom c := by
    change (h.appLE (g₁ ⁻¹ᵁ U) (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U)) le_rfl).hom c = _
    rw [Scheme.Hom.app_eq_appLE]
  refine (congrArg (fun a : Γ(Y₂, (h ≫ g₁) ⁻¹ᵁ U) => τ.app (g₁ ⁻¹ᵁ U) (a • s)) hrc).trans ?_
  exact Scheme.Modules.Hom.app_smul (U := g₁ ⁻¹ᵁ U) τ c s

/-- Under the hypotheses of `ofFiniteTraceLocalEquiv_eq_of_map`, the chart identification through
`e₁`, precomposed with the comparison of dualizing modules, is the one through `e₂`. -/
private theorem chartEquiv_dualizingModuleEquiv_of_map [IsLocallyNoetherian X]
    (htr : ∀ (U : X.Opens) (s : Γ(M₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U))),
      traceApp (h ≫ g₁) t₂ U s = traceApp g₁ t₁ U (τ.app (g₁ ⁻¹ᵁ U) s))
    (hres : ∀ (W : Y₁.Opens) (V : Y.Opens) (hV : V ≤ i₁ ⁻¹ᵁ W) (s : Γ(M₂, h ⁻¹ᵁ W)),
      chartRestrict M₁ e₁ hV (τ.app W s) =
        chartRestrict M₂ e₂ (le_preimage_of_map h hih hV) s)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hpush :
      letI : Algebra Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) :=
        (h.appLE (g₁ ⁻¹ᵁ U.1) (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) le_rfl).hom.toAlgebra
      letI : Algebra Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y, V.1) :=
        (i₁.appLE (g₁ ⁻¹ᵁ U.1) V.1 (le_preimage_preimage hig₁ hVU)).hom.toAlgebra
      letI : Algebra Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) Γ(Y, V.1) :=
        (i₂.appLE (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) V.1
          (le_preimage_of_map h hih (le_preimage_preimage hig₁ hVU))).hom.toAlgebra
      letI : IsScalarTower Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) Γ(Y, V.1) :=
        IsScalarTower.of_algebraMap_eq fun c =>
          (appLE_appLE_apply_of_map h hih (le_preimage_preimage hig₁ hVU) c).symm
      Algebra.IsPushout Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y, V.1) Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) Γ(Y, V.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    ∀ x, chartEquiv hig₁ M₁ t₁ hbij₁ e₁ U V hVU
        (dualizingModuleEquiv (chartFactorization (comp_comp_of_map h hig₁ hih) U V hVU)
          (chartFactorization hig₁ U V hVU) x) =
      chartEquiv (comp_comp_of_map h hig₁ hih) M₂ t₂ hbij₂ e₂ U V hVU x := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hig₂ := comp_comp_of_map h hig₁ hih
  let : Algebra Γ(X, U.1) Γ(Y₁, g₁ ⁻¹ᵁ U.1) :=
    (g₁.appLE U.1 (g₁ ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y₂, (h ≫ g₁) ⁻¹ᵁ U.1) :=
    ((h ≫ g₁).appLE U.1 ((h ≫ g₁) ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have hr : ∀ c, algebraMap (chartFactorization hig₂ U V hVU).middle Γ(Y, V.1)
      (appLEAlgHom h U.1 c) = algebraMap (chartFactorization hig₁ U V hVU).middle Γ(Y, V.1) c :=
    appLE_appLE_apply_of_map h hih (le_preimage_preimage hig₁ hVU)
  intro x
  change Module.Dual _ (chartFactorization hig₂ U V hVU).middle ⊗[(chartFactorization hig₂ U V
    hVU).middle] Γ(Y, V.1) at x
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    exact ((congrArg _ (map_add _ x x')).trans ((map_add _ _ _).trans
      (congrArg₂ (· + ·) hx hx'))).trans (map_add _ x x').symm
  | tmul φ b =>
    change chartEquiv hig₁ M₁ t₁ hbij₁ e₁ U V hVU
        (dualizingModuleEquiv (chartFactorization hig₂ U V hVU) (chartFactorization hig₁ U V hVU)
          (dualizingModule.tmul (chartFactorization hig₂ U V hVU) φ b)) =
      chartEquiv hig₂ M₂ t₂ hbij₂ e₂ U V hVU
        (dualizingModule.tmul (chartFactorization hig₂ U V hVU) φ b)
    obtain ⟨s, rfl⟩ := (hbij₂ U).2 φ
    refine (congrArg (chartEquiv hig₁ M₁ t₁ hbij₁ e₁ U V hVU)
      (dualizingModuleEquiv_tmul_of_isPushout (chartFactorization hig₂ U V hVU)
        (chartFactorization hig₁ U V hVU) (appLEAlgHom h U.1) hr hpush _ b)).trans ?_
    refine (congrArg (fun φ => chartEquiv hig₁ M₁ t₁ hbij₁ e₁ U V hVU
      (dualizingModule.tmul (chartFactorization hig₁ U V hVU) φ b))
      (traceDual_comp_appLEAlgHom h M₁ M₂ t₁ t₂ τ U.1 (htr U.1) s)).trans ?_
    refine (chartEquiv_tmul hig₁ M₁ t₁ hbij₁ e₁ U V hVU _ b).trans
      (Eq.trans ?_ (chartEquiv_tmul hig₂ M₂ t₂ hbij₂ e₂ U V hVU _ b).symm)
    have h₁ : (traceDualEquiv M₁ t₁ hbij₁ U).symm
        (traceDual g₁ t₁ U.1 (τ.app (g₁ ⁻¹ᵁ U.1) s)) = τ.app (g₁ ⁻¹ᵁ U.1) s :=
      (traceDualEquiv M₁ t₁ hbij₁ U).symm_apply_apply _
    have h₂ : (traceDualEquiv M₂ t₂ hbij₂ U).symm (traceDual (h ≫ g₁) t₂ U.1 s) = s :=
      (traceDualEquiv M₂ t₂ hbij₂ U).symm_apply_apply _
    refine congrArg (b • ·) ?_
    refine (congrArg (chartRestrict M₁ e₁ (le_preimage_preimage hig₁ hVU)) h₁).trans ?_
    refine (hres _ V.1 (le_preimage_preimage hig₁ hVU) s).trans ?_
    exact (congrArg (chartRestrict M₂ e₂ (le_preimage_preimage hig₂ hVU)) h₂).symm

/-- **The chart identifications along a map of finite factorizations agree.** Let `τ : h_*M₂ ⟶ M₁`
carry the trace `t₂` to `t₁` and the restriction of sections through `e₂` to the one through
`e₁`, and let `Γ(Y₂, h⁻¹g₁⁻¹U) ⊗ Γ(Y, V) = Γ(Y, V)` over `Γ(Y₁, g₁⁻¹U)`. Then on the chart
`(U, V)` the identifications of `Γ(N, V)` with the algebraic relative dualizing module
attached to the two factorizations are equal. -/
theorem ofFiniteTraceLocalEquiv_eq_of_map [IsLocallyNoetherian X]
    (htr : ∀ (U : X.Opens) (s : Γ(M₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U))),
      traceApp (h ≫ g₁) t₂ U s = traceApp g₁ t₁ U (τ.app (g₁ ⁻¹ᵁ U) s))
    (hres : ∀ (W : Y₁.Opens) (V : Y.Opens) (hV : V ≤ i₁ ⁻¹ᵁ W) (s : Γ(M₂, h ⁻¹ᵁ W)),
      chartRestrict M₁ e₁ hV (τ.app W s) =
        chartRestrict M₂ e₂ (le_preimage_of_map h hih hV) s)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hpush :
      letI : Algebra Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) :=
        (h.appLE (g₁ ⁻¹ᵁ U.1) (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) le_rfl).hom.toAlgebra
      letI : Algebra Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y, V.1) :=
        (i₁.appLE (g₁ ⁻¹ᵁ U.1) V.1 (le_preimage_preimage hig₁ hVU)).hom.toAlgebra
      letI : Algebra Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) Γ(Y, V.1) :=
        (i₂.appLE (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) V.1
          (le_preimage_of_map h hih (le_preimage_preimage hig₁ hVU))).hom.toAlgebra
      letI : IsScalarTower Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) Γ(Y, V.1) :=
        IsScalarTower.of_algebraMap_eq fun c => by
          subst hih
          exact (RingHom.congr_fun (CommRingCat.hom_ext_iff.mp
            (Scheme.Hom.appLE_comp_appLE i₂ h _ _ V.1 le_rfl
              (le_preimage_of_map h rfl (le_preimage_preimage hig₁ hVU)))) c).symm
      Algebra.IsPushout Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y, V.1) Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) Γ(Y, V.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      ofFiniteTraceLocalEquiv (comp_comp_of_map h hig₁ hih) M₂ t₂ hbij₂ e₂ U V hVU F =
        ofFiniteTraceLocalEquiv hig₁ M₁ t₁ hbij₁ e₁ U V hVU F := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  intro F
  have hig₂ := comp_comp_of_map h hig₁ hih
  refine LinearEquiv.ext fun n => ?_
  change dualizingModuleEquiv (chartFactorization hig₂ U V hVU) F
      ((chartEquiv hig₂ M₂ t₂ hbij₂ e₂ U V hVU).symm n) =
    dualizingModuleEquiv (chartFactorization hig₁ U V hVU) F
      ((chartEquiv hig₁ M₁ t₁ hbij₁ e₁ U V hVU).symm n)
  rw [← dualizingModuleEquiv_trans (chartFactorization hig₂ U V hVU)
    (chartFactorization hig₁ U V hVU) F, LinearEquiv.trans_apply]
  congr 1
  apply (chartEquiv hig₁ M₁ t₁ hbij₁ e₁ U V hVU).injective
  rw [LinearEquiv.apply_symm_apply, chartEquiv_dualizingModuleEquiv_of_map h hig₁ hih M₁ M₂ t₁ t₂
    hbij₁ hbij₂ e₁ e₂ τ htr hres U V hVU hpush, LinearEquiv.apply_symm_apply]

/-- **The chart identifications along a cartesian map of finite factorizations agree.** This is
`ofFiniteTraceLocalEquiv_eq_of_map` with the chart pushout supplied by
`isPushout_appLE_of_map`, for a square `i₂ ≫ h = i₁` that is cartesian. -/
theorem ofFiniteTraceLocalEquiv_eq_of_isPullback [IsLocallyNoetherian X]
    (sq : IsPullback i₂ (𝟙 Y) h i₁)
    (htr : ∀ (U : X.Opens) (s : Γ(M₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U))),
      traceApp (h ≫ g₁) t₂ U s = traceApp g₁ t₁ U (τ.app (g₁ ⁻¹ᵁ U) s))
    (hres : ∀ (W : Y₁.Opens) (V : Y.Opens) (hV : V ≤ i₁ ⁻¹ᵁ W) (s : Γ(M₂, h ⁻¹ᵁ W)),
      chartRestrict M₁ e₁ hV (τ.app W s) =
        chartRestrict M₂ e₂ (le_preimage_of_map h (sq.w.trans (Category.id_comp _)) hV) s)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      ofFiniteTraceLocalEquiv
          (comp_comp_of_map h hig₁ (sq.w.trans (Category.id_comp _))) M₂ t₂ hbij₂ e₂ U V hVU F =
        ofFiniteTraceLocalEquiv hig₁ M₁ t₁ hbij₁ e₁ U V hVU F :=
  ofFiniteTraceLocalEquiv_eq_of_map h hig₁ (sq.w.trans (Category.id_comp _)) M₁ M₂ t₁ t₂ hbij₁
    hbij₂ e₁ e₂ τ htr hres U V hVU (by
      let : Algebra Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) :=
        (h.appLE (g₁ ⁻¹ᵁ U.1) (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) le_rfl).hom.toAlgebra
      let : Algebra Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y, V.1) :=
        (i₁.appLE (g₁ ⁻¹ᵁ U.1) V.1 (le_preimage_preimage hig₁ hVU)).hom.toAlgebra
      let : Algebra Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) Γ(Y, V.1) :=
        (i₂.appLE (h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) V.1 (le_preimage_of_map h
          (sq.w.trans (Category.id_comp _)) (le_preimage_preimage hig₁ hVU))).hom.toAlgebra
      let : IsScalarTower Γ(Y₁, g₁ ⁻¹ᵁ U.1) Γ(Y₂, h ⁻¹ᵁ (g₁ ⁻¹ᵁ U.1)) Γ(Y, V.1) :=
        IsScalarTower.of_algebraMap_eq fun c =>
          (appLE_appLE_apply_of_map h (sq.w.trans (Category.id_comp _))
            (le_preimage_preimage hig₁ hVU) c).symm
      exact CommRingCat.isPushout_iff_isPushout.mp
        (isPushout_appLE_of_map h hig₁ sq U V hVU).flip)

end Stacks.Discriminant
