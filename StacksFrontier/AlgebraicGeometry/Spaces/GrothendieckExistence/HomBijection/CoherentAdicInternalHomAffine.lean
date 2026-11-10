module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CoherentAdicInternalHomSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.AdicSectionsAffineDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.SliceHomEvaluationAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAffineQuotientSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubmoduleColimitNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerQuasicoherent
public import StacksFrontier.RingTheory.AdicCompletion.HomBijection.HomCompletionLevels

/-!
# Morphisms of completions of coherent modules on an algebraic space

Let `F` be a locally Noetherian algebraic space, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of ideals and
`M`, `N` coherent `𝒪_F`-modules, with `𝓗 = 𝓗om_{𝒪_F}(M, N)`. Then

`lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗) = Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`.

## Main definitions

* `AlgebraicGeometry.Space.C1573.internalHomChartEval`: a section of the internal hom over a
  chart, read as a linear map of sections over the chart.
* `AlgebraicGeometry.Space.C1573.chartAdicQuotientEquiv`: the sections of `M / 𝓘 ^ k M` over an
  affine chart `V` are `M(V) / 𝓘(V) ^ k M(V)`.
* `AlgebraicGeometry.Space.C1573.smallEtaleInternalHomSmallAdicEquiv`: the bijection
  `lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗) ≃ Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`.

## Main results

* `AlgebraicGeometry.Space.C1573.bijective_smallAdicSectionsMapAt_of_isAffine`: the comparison of
  `𝓗 / 𝓘 ^ (n + 1) 𝓗` with `𝓗om(M, N / 𝓘 ^ (n + 1) N)` is bijective on the inverse limits of the
  sections over an affine chart.
* `AlgebraicGeometry.Space.C1573.bijective_smallAdicSectionsMapAt`: the same over every étale
  chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space.C1573

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Sections of the internal hom over a chart -/

/-- A section of the internal hom over a chart `U`, read as the linear map it induces on the
sections over `U`. -/
def internalHomChartEval (M N : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C)
    (s : (smallEtaleInternalHom B S hS F hF M N).val.obj (op U)) :
    M.val.obj (op U) →ₗ[chartRing B S hS F hF U] N.val.obj (op U) :=
  sliceHomEvaluation B S hS F hF U (⟨s⟩ : M.over U ⟶ N.over U)

/-- Over an affine chart, for quasi-coherent `M` and `N`, `internalHomChartEval` is bijective. -/
theorem bijective_internalHomChartEval (M N : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hU : IsAffine (chartScheme U))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    Function.Bijective (internalHomChartEval B S hS F hF M N U) :=
  Function.Bijective.comp (g := sliceHomEvaluation B S hS F hF U (G := M) (G' := N))
    (f := fun s : (smallEtaleInternalHom B S hS F hF M N).val.obj (op U) =>
      (⟨s⟩ : M.over U ⟶ N.over U))
    (bijective_sliceHomEvaluation B S hS F hF U hU hM hN)
    ⟨fun _ _ h => congrArg SheafOfModules.Hom.val h,
      fun α => ⟨α.val, rfl⟩⟩

/-- `internalHomChartEval` commutes with scalar multiplication by the chart ring. -/
theorem internalHomChartEval_smul (M N : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C)
    (r : chartRing B S hS F hF U) (s : (smallEtaleInternalHom B S hS F hF M N).val.obj (op U)) :
    internalHomChartEval B S hS F hF M N U
        (r • s : (smallEtaleInternalHom B S hS F hF M N).val.obj (op U)) =
      r • internalHomChartEval B S hS F hF M N U s := by
  have h0 : fRestr (smallEtaleRingedSite B S hS F hF).O.obj
      U r (op (CategoryTheory.Over.mk (𝟙 U))) = r := by
    change ((Oforget _).map (𝟙 (op U))).hom r = r
    rw [CategoryTheory.Functor.map_id]
    rfl
  refine LinearMap.ext fun x => ?_
  change fRestr (smallEtaleRingedSite B S hS F hF).O.obj U r (op (CategoryTheory.Over.mk (𝟙 U))) •
    ((s.app (op (CategoryTheory.Over.mk (𝟙 U)))).hom x :
      ((restrFun (smallEtaleRingedSite B S hS F hF).O.obj U).obj N.val).obj
        (op (CategoryTheory.Over.mk (𝟙 U)))) = _
  rw [h0]
  rfl

/-- `internalHomChartEval` is natural in the target module. -/
theorem internalHomChartEval_mapRight (M : Modules.{u, u} B S hS F hF)
    {N N' : Modules.{u, u} B S hS F hF} (f : N ⟶ N') (U : (smallEtaleRingedSite B S hS F hF).C)
    (s : (smallEtaleInternalHom B S hS F hF M N).val.obj (op U)) :
    internalHomChartEval B S hS F hF M N' U
        ((smallEtaleInternalHomMapRight B S hS F hF M f).val.app (op U) s) =
      (f.val.app (op U)).hom ∘ₗ internalHomChartEval B S hS F hF M N U s :=
  LinearMap.ext fun _ => rfl

/-- `internalHomChartEval` is additive. -/
theorem internalHomChartEval_add (M N : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C)
    (s t : (smallEtaleInternalHom B S hS F hF M N).val.obj (op U)) :
    internalHomChartEval B S hS F hF M N U (s + t) =
      internalHomChartEval B S hS F hF M N U s + internalHomChartEval B S hS F hF M N U t :=
  LinearMap.ext fun _ => rfl

/-- A section of the small internal hom over a chart, read as the linear map it induces on the
sections over the chart. -/
def smallInternalHomChartEval (M N : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    (smallEtaleInternalHomSmall B S hS F hF M N).val.obj (op U) →ₗ[chartRing B S hS F hF U]
      (M.val.obj (op U) →ₗ[chartRing B S hS F hF U] N.val.obj (op U)) where
  toFun s := internalHomChartEval B S hS F hF M N U
    (smallEtaleInternalHomSmallShrink B S hS F hF M N (op U) s)
  map_add' s t := by
    rw [map_add, internalHomChartEval_add]
  map_smul' r s := by
    rw [smallEtaleInternalHomSmallShrink_smul]
    exact internalHomChartEval_smul B S hS F hF M N U r _

/-- `smallInternalHomChartEval` is natural in the target module. -/
theorem smallInternalHomChartEval_mapRight (M : Modules.{u, u} B S hS F hF)
    {N N' : Modules.{u, u} B S hS F hF} (f : N ⟶ N') (U : (smallEtaleRingedSite B S hS F hF).C)
    (s : (smallEtaleInternalHomSmall B S hS F hF M N).val.obj (op U)) :
    smallInternalHomChartEval B S hS F hF M N' U
        ((smallEtaleInternalHomSmallMapRight B S hS F hF M f).val.app (op U) s) =
      (f.val.app (op U)).hom ∘ₗ smallInternalHomChartEval B S hS F hF M N U s := by
  change internalHomChartEval B S hS F hF M N' U
    (smallEtaleInternalHomSmallShrink B S hS F hF M N' (op U)
      ((smallEtaleInternalHomSmallMapRight B S hS F hF M f).val.app (op U) s)) = _
  rw [smallEtaleInternalHomSmallShrink_mapRight]
  exact internalHomChartEval_mapRight B S hS F hF M f U _

/-- Over an affine chart, for quasi-coherent `M` and `N`, `smallInternalHomChartEval` is
bijective. -/
theorem bijective_smallInternalHomChartEval (M N : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hU : IsAffine (chartScheme U))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    Function.Bijective (smallInternalHomChartEval B S hS F hF M N U) :=
  (bijective_internalHomChartEval B S hS F hF M N U hU hM hN).comp
    (smallEtaleInternalHomSmallShrink B S hS F hF M N (op U)).bijective

/-! ### Sections of the ideal-power quotients over an affine chart -/

section Quotient

variable (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- **The sections of `M / 𝓘 ^ k M` over an affine chart are `M(V) / 𝓘(V) ^ k M(V)`.** -/
def chartAdicQuotientEquiv (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M) (k : ℕ)
    (V : (smallEtaleRingedSite B S hS F hF).C) (hV : IsAffine (chartScheme V)) :
    (smallEtaleAdicQuotient B S hS F hF 𝓘 k M).val.obj (op V) ≃ₗ[chartRing B S hS F hF V]
      M.val.obj (op V) ⧸ (chartSectionIdeal B S hS F hF 𝓘 V ^ k •
        (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V)))) :=
  (LinearMap.quotKerEquivOfSurjective
      ((smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k M).val.app (op V)).hom
      (surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart k hV)).symm.trans
    (Submodule.quotEquivOfEq _ _
      (ker_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart k hV))

/-- `chartAdicQuotientEquiv` sends the image of a section `x` of `M` to the class of `x`. -/
theorem chartAdicQuotientEquiv_projection (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M) (k : ℕ)
    (V : (smallEtaleRingedSite B S hS F hF).C) (hV : IsAffine (chartScheme V))
    (x : M.val.obj (op V)) :
    chartAdicQuotientEquiv B S hS F hF 𝓘 hIcart M hMcart k V hV
        ((smallEtaleAdicQuotientProjection B S hS F hF 𝓘 k M).val.app (op V) x) =
      Submodule.Quotient.mk x := by
  refine (chartAdicQuotientEquiv B S hS F hF 𝓘 hIcart M hMcart k V hV).symm.injective ?_
  rw [LinearEquiv.symm_apply_apply]
  rfl

end Quotient

/-! ### The comparison on an affine chart -/

section Affine

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (M N : Modules.{u, u} B S hS F hF) [hM : IsCoherent B S hS F hF M]
    [hN : IsCoherent B S hS F hF N]

include hI in
/-- Over an affine chart `V` of a locally Noetherian algebraic space, the comparison of the
inverse system `𝓗 / 𝓘 ^ (n + 1) 𝓗` with the internal homs `𝓗om(M, N / 𝓘 ^ (n + 1) N)` is
bijective on the inverse limits of the sections over `V`. -/
theorem bijective_smallAdicSectionsMapAt_of_isAffine (V : (smallEtaleRingedSite B S hS F hF).C)
    (hV : IsAffine (chartScheme V)) :
    Function.Bijective (adicSectionsMapAt B S hS F hF
      (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHomSmall B S hS F hF M N))
      (fun n => smallEtaleInternalHomSmall B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N))
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHomSmall B S hS F hF M N))
      (fun n => smallEtaleInternalHomSmallMapRight B S hS F hF M
        (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N))
      (smallEtaleInternalHomSmallAdicComparisonApp B S hS F hF 𝓘 M N)
      (smallEtaleInternalHomSmallAdicComparison_compat B S hS F hF 𝓘 M N) (op V)) := by
  have : IsNoetherianRing (chartRing B S hS F hF V) :=
    isNoetherianRing_chartRing_of_isAffine (hX := hF) Fact.out hV
  have : Module.Finite (chartRing B S hS F hF V) (M.val.obj (op V)) :=
    moduleFinite_sections_of_isCoherent B S hS F hF M hM hV
  have : Module.Finite (chartRing B S hS F hF V) (N.val.obj (op V)) :=
    moduleFinite_sections_of_isCoherent B S hS F hF N hN hV
  have hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ hI
  have hHcoh := isCoherent_smallEtaleInternalHomSmall B S hS F hF M N
  have hHcart : IsCartesianOnAffineCharts (smallEtaleInternalHomSmall B S hS F hF M N) :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _
      hHcoh.toIsQuasicoherentOnSite
  have hNcart : IsCartesianOnAffineCharts N :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF _ hN.toIsQuasicoherentOnSite
  have hNn : ∀ n : ℕ, (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N).IsQuasicoherentOnSite :=
    fun n => (isCoherent_idealPowerQuotient B S hS F hF 𝓘 hI N hN (n + 1)).toIsQuasicoherentOnSite
  let κ : ∀ n : ℕ, (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N).val.obj (op V) ≃ₗ[_] _ :=
    fun n => chartAdicQuotientEquiv B S hS F hF 𝓘 hIcart N hNcart (n + 1) V hV
  have hκ : ∀ n (q : N.val.obj (op V)),
      κ n ((smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1) N).val.app (op V) q) =
        Submodule.Quotient.mk q := fun n q =>
    chartAdicQuotientEquiv_projection B S hS F hF 𝓘 hIcart N hNcart (n + 1) V hV q
  have hcomp : ∀ {P Q R : Modules.{u, u} B S hS F hF} {f : P ⟶ Q} {g : Q ⟶ R} {h : P ⟶ R},
      f ≫ g = h → ∀ x, g.val.app (op V) (f.val.app (op V) x) = h.val.app (op V) x :=
    fun e x => congrArg (fun k => k.val.app (op V) x) e
  refine AdicCompletion.C1573.bijective_limit_of_homQuotient (chartSectionIdeal B S hS F hF 𝓘 V)
    (LinearEquiv.ofBijective (smallInternalHomChartEval B S hS F hF M N V)
      (bijective_smallInternalHomChartEval B S hS F hF M N V hV hM.toIsQuasicoherentOnSite
        hN.toIsQuasicoherentOnSite))
    (X := fun n => (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
      (smallEtaleInternalHomSmall B S hS F hF M N)).val.obj (op V))
    (fun n => (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
      (smallEtaleInternalHomSmall B S hS F hF M N)).val.app (op V))
    (fun n => ((smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1)
      (smallEtaleInternalHomSmall B S hS F hF M N)).val.app (op V)).hom)
    (fun n => surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart _ hHcart (n + 1) hV)
    (fun n => ker_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart _ hHcart (n + 1) hV)
    (fun n => hcomp (smallEtaleAdicQuotientProjection_comp_transition B S hS F hF 𝓘 (n + 1) _))
    (Y := fun n => (smallEtaleInternalHomSmall B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N)).val.obj (op V))
    (fun n => (smallEtaleInternalHomSmallMapRight B S hS F hF M
        (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N)).val.app (op V))
    (fun n y => (κ n).toLinearMap ∘ₗ smallInternalHomChartEval B S hS F hF M _ V y)
    (fun n y y' hyy => (bijective_smallInternalHomChartEval B S hS F hF M _ V hV
      hM.toIsQuasicoherentOnSite (hNn n)).1
        (LinearMap.ext fun p => (κ n).injective (LinearMap.congr_fun hyy p)))
    (fun n y => by
      refine LinearMap.ext fun p => ?_
      change κ n (smallInternalHomChartEval B S hS F hF M _ V
        ((smallEtaleInternalHomSmallMapRight B S hS F hF M
          (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N)).val.app (op V) y) p) = _
      rw [smallInternalHomChartEval_mapRight]
      obtain ⟨q, hq⟩ := surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart N hNcart
        (n + 1 + 1) hV (smallInternalHomChartEval B S hS F hF M _ V y p)
      change κ n ((smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N).val.app (op V)
        (smallInternalHomChartEval B S hS F hF M _ V y p)) =
          AdicCompletion.transitionMap _ _ (Nat.le_succ (n + 1)) (κ (n + 1)
            (smallInternalHomChartEval B S hS F hF M _ V y p))
      rw [← hq]
      refine ((congrArg (κ n) (hcomp (smallEtaleAdicQuotientProjection_comp_transition
        B S hS F hF 𝓘 (n + 1) N) q)).trans (hκ n q)).trans ?_
      exact (congrArg (AdicCompletion.transitionMap _ _ (Nat.le_succ (n + 1)))
        (hκ (n + 1) q)).symm)
    (fun n => (smallEtaleInternalHomSmallAdicComparisonApp B S hS F hF 𝓘 M N n).val.app (op V))
    (fun n h => by
      refine LinearMap.ext fun p => ?_
      have h1 := hcomp (smallEtaleAdicQuotientProjection_comp_smallComparisonApp
        B S hS F hF 𝓘 M N n) h
      change κ n (smallInternalHomChartEval B S hS F hF M _ V
        ((smallEtaleInternalHomSmallAdicComparisonApp B S hS F hF 𝓘 M N n).val.app (op V)
          ((smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1)
            (smallEtaleInternalHomSmall B S hS F hF M N)).val.app (op V) h)) p) = _
      rw [show (smallEtaleInternalHomSmallAdicComparisonApp B S hS F hF 𝓘 M N n).val.app (op V)
          ((smallEtaleAdicQuotientProjection B S hS F hF 𝓘 (n + 1)
            (smallEtaleInternalHomSmall B S hS F hF M N)).val.app (op V) h) = _ from h1,
        smallInternalHomChartEval_mapRight]
      exact hκ n _)
    _ (fun _ _ => rfl)

include hI in
/-- The comparison of the inverse system `𝓗 / 𝓘 ^ (n + 1) 𝓗` with the internal homs
`𝓗om(M, N / 𝓘 ^ (n + 1) N)` is bijective on the inverse limits of the sections over every étale
chart. -/
theorem bijective_smallAdicSectionsMapAt
    (U : ((smallEtaleRingedSite B S hS F hF).C)ᵒᵖ) :
    Function.Bijective (adicSectionsMapAt B S hS F hF
      (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHomSmall B S hS F hF M N))
      (fun n => smallEtaleInternalHomSmall B S hS F hF M
        (smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1) N))
      (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
        (smallEtaleInternalHomSmall B S hS F hF M N))
      (fun n => smallEtaleInternalHomSmallMapRight B S hS F hF M
        (smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1) N))
      (smallEtaleInternalHomSmallAdicComparisonApp B S hS F hF 𝓘 M N)
      (smallEtaleInternalHomSmallAdicComparison_compat B S hS F hF 𝓘 M N) U) :=
  bijective_adicSectionsMapAt_of_bijective_affineCharts B S hS F hF _ _ _ _ _ _
    (fun V hV => bijective_smallAdicSectionsMapAt_of_isAffine B S hS F hF 𝓘 hI M N V hV) U

/-- Let `F` be a locally Noetherian algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a
quasi-coherent sheaf of ideals and let `M`, `N` be coherent `𝒪_F`-modules. Put
`𝓗 = 𝓗om_{𝒪_F}(M, N)`. Then

`lim_n H⁰(F, 𝓗 / 𝓘 ^ n 𝓗) = Mor((M / 𝓘 ^ n M), (N / 𝓘 ^ n N))`,

the inverse limit of the global sections of the ideal-power quotients of `𝓗` being the
morphisms of inverse systems of `𝒪_F`-modules from the completion of `M` to the completion of
`N`; since `Coh(F, 𝓘)` is a full subcategory of the inverse systems of `𝒪_F`-modules, this is
`Mor_{Coh(F, 𝓘)}(M^∧, N^∧)`. Here `𝓗` is the internal hom at the module universe of the
schemes, `AlgebraicGeometry.Space.smallEtaleInternalHomSmall`. -/
def smallEtaleInternalHomSmallAdicEquiv :
    adicSections B S hS F hF
        (fun n => smallEtaleAdicQuotient B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHomSmall B S hS F hF M N))
        (fun n => smallEtaleAdicQuotientTransition B S hS F hF 𝓘 (n + 1)
          (smallEtaleInternalHomSmall B S hS F hF M N)) ≃
      (smallEtaleAdicQuotientSystem B S hS F hF 𝓘 M ⟶
        smallEtaleAdicQuotientSystem B S hS F hF 𝓘 N) :=
  smallEtaleInternalHomSmallAdicEquivOfBijective B S hS F hF 𝓘 M N
    (bijective_smallAdicSectionsMapAt B S hS F hF 𝓘 hI M N)

end Affine

end AlgebraicGeometry.Space.C1573

end
