module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinTangentLift

/-!
# The lifts of a quotient over `k[V]` and their pullbacks to `k[W]`

Let `f : V ⟶ W` be a linear map of finite-dimensional `k`-vector spaces and `Spec k[W] ⟶ Spec k[V]`
the morphism of `k[f]`. The transfer of `AlgebraicGeometry.Space.transferMap` along the induced
morphism `X_{k[W]} ⟶ X_{k[V]}` of split thickenings of `X_k` maps the extension
`r_*F_{k[V]}` to `r_*F_{k[W]}` compatibly with the projections to `F_k`, and, for a quotient `𝒬`
over `k[V]` lifting `F_k/𝒦₀` with pullback `𝒬'` to `k[W]`, maps `r_*𝒬` to `r_*𝒬'` compatibly with
the maps from `r_*F` and carrying the multiplication by `v` to the multiplication by `f v`. These
are the inputs of `Deformation.ModuleDeformation.CopowerQuotientLift.difference_naturality`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.sqTransfer_p`.
* `AlgebraicGeometry.Space.QuotSituation.sqG_comp_sqTransferQ`.
* `AlgebraicGeometry.Space.QuotSituation.sqμ_comp_sqTransferQ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation Deformation.Artin

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [-instance] CategoryTheory.IsGrothendieckAbelian.hasExt
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

/-- **A comparison of quotients induced by comparisons of their sources.** Let `τ : L₁ ⟶ Lσ ⋙ L₂`
and let `ψF₁ : L₁ F₁ ≅ F₀`, `ψF₂ : L₂ F₂ ≅ F₀`, `θF : Lσ F₁ ⟶ F₂` satisfy
`ψF₁ = τ ≫ L₂ θF ≫ ψF₂`. For quotients `q₁, q₂, q₀` and maps `ψQ₁`, `ψQ₂`, `θQ` compatible with
them, with `L₁ q₁` an epimorphism, the same relation holds for `ψQ₁`, `θQ`, `ψQ₂`. -/
theorem CategoryTheory.Functor.comparison_hom_eq_of_fac {C₀ C₁ C₂ : Type*} [Category C₀]
    [Category C₁] [Category C₂] {L₁ : C₁ ⥤ C₀} {L₂ : C₂ ⥤ C₀} {Lσ : C₁ ⥤ C₂}
    (τ : L₁ ⟶ Lσ ⋙ L₂) {F₁ Q₁ : C₁} {F₂ Q₂ : C₂} {F₀ Q₀ : C₀} (q₁ : F₁ ⟶ Q₁) (q₂ : F₂ ⟶ Q₂)
    (q₀ : F₀ ⟶ Q₀) (ψF₁ : L₁.obj F₁ ≅ F₀) (ψF₂ : L₂.obj F₂ ≅ F₀) (θF : Lσ.obj F₁ ⟶ F₂)
    (ψQ₁ : L₁.obj Q₁ ⟶ Q₀) (ψQ₂ : L₂.obj Q₂ ⟶ Q₀) (θQ : Lσ.obj Q₁ ⟶ Q₂) [Epi (L₁.map q₁)]
    (h₁ : L₁.map q₁ ≫ ψQ₁ = ψF₁.hom ≫ q₀) (h₂ : L₂.map q₂ ≫ ψQ₂ = ψF₂.hom ≫ q₀)
    (hm : Lσ.map q₁ ≫ θQ = θF ≫ q₂) (hb : ψF₁.hom = τ.app F₁ ≫ L₂.map θF ≫ ψF₂.hom) :
    ψQ₁ = τ.app Q₁ ≫ L₂.map θQ ≫ ψQ₂ := by
  rw [← cancel_epi (L₁.map q₁), h₁, τ.naturality_assoc, Functor.comp_map,
    ← Functor.map_comp_assoc, hm, Functor.map_comp_assoc, h₂, hb]
  simp only [Category.assoc]

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS)
  (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
  [hY : ∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]
  {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  (hF : IsFlatOver B S hS D.X.2 D.f.hom D.F)
  {V W : FGModuleCat.{u} k} (f : V ⟶ W)

/-- The comparison `(X_{k[f]})^*F_{k[V]} ⟶ F_{k[W]}`. -/
def sqThetaF :
    (modulePullback B S hS (D.relativeMap (D.sqσ ι toS hk f))).obj
        ((modulePullback B S hS (D.sourceProjection (D.sqT ι toS hk V))).obj D.F) ⟶
      (modulePullback B S hS (D.sourceProjection (D.sqT ι toS hk W))).obj D.F :=
  (D.baseChangeComparison (D.sqσ ι toS hk f)).inv.app D.F

/-- The transfer `r_*F_{k[V]} ⟶ r_*F_{k[W]}`. -/
abbrev sqTransfer :
    (retractionPushforward B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)).obj
        ((modulePullback B S hS (D.sourceProjection (D.sqT ι toS hk V))).obj D.F) ⟶
      (retractionPushforward B S hS (D.relativeMap (D.sqπ ι toS hk W)) (D.sqRep ι toS hk W)).obj
        ((modulePullback B S hS (D.sourceProjection (D.sqT ι toS hk W))).obj D.F) :=
  transferMap B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)
    (D.relativeMap (D.sqπ ι toS hk W)) (D.sqRep ι toS hk W) (D.relativeMap (D.sqσ ι toS hk f))
    (D.sqH_sqR ι toS hk f) (D.sqThetaF ι toS hk f)

include hY in
/-- The identification of the restriction of `F_{k[V]}` to `X_k` with `F_k` factors through the
comparison `(X_{k[f]})^*F_{k[V]} ⟶ F_{k[W]}` and the identification for `F_{k[W]}`. -/
theorem sqBaseIso_hom_eq :
    (D.sqBaseIso ι toS hk V).hom =
      (modulePullbackTriangle B S hS (D.sqI_sqH ι toS hk f)).hom.app
          ((modulePullback B S hS (D.sourceProjection (D.sqT ι toS hk V))).obj D.F) ≫
        (modulePullback B S hS (D.relativeMap (D.sqβ ι toS hk W))).map
          (D.sqThetaF ι toS hk f) ≫ (D.sqBaseIso ι toS hk W).hom :=
  D.baseChangeComparison_fac_hom _ _ _ (D.sqβ_sqσ ι toS hk f) (D.sqI_sqH ι toS hk f) _ _ _
    rfl rfl rfl

include hY in
/-- **The transfer is compatible with the projections to `F_k`.** -/
theorem sqTransfer_p :
    letI := D.sqLinear ι toS hk
    D.sqTransfer ι toS hk f ≫ (D.sqBaseExtension ι toS hk hF W).p =
      (D.sqBaseExtension ι toS hk hF V).p := by
  rw [sqBaseExtension_p, sqBaseExtension_p]
  exact transferMap_comp_retractionProjection B S hS (D.sqBaseIso ι toS hk V)
    (D.sqBaseIso ι toS hk W) (D.relativeMap (D.sqσ ι toS hk f)) (D.sqH_sqR ι toS hk f)
    (D.sqI_sqH ι toS hk f) (D.sqThetaF ι toS hk f) (D.sqBaseIso_hom_eq ι toS hk f)

variable (K₀ : Subobject (D.baseChangeModule (D.sq₀ ι toS hk)))
  (K : Subobject (D.baseChangeModule (D.sqT ι toS hk V)))
  (K' : Subobject (D.baseChangeModule (D.sqT ι toS hk W)))
  (e : D.quotientPullback (D.sqσ ι toS hk f) K = K')

/-- The identification of the pullback of `F_{k[V]}/K` with `F_{k[W]}/K'`. -/
abbrev sqQuotTheta :
    (modulePullback B S hS (D.relativeMap (D.sqσ ι toS hk f))).obj
        (D.quotientModule (D.sqT ι toS hk V) K) ⟶ D.quotientModule (D.sqT ι toS hk W) K' :=
  ((D.quotientPullbackCokernelIso (D.sqσ ι toS hk f) K).symm ≪≫
    eqToIso (congrArg (D.quotientModule (D.sqT ι toS hk W)) e)).hom

include hY in
/-- The identification of the pullback of `F_{k[V]}/K` with `F_{k[W]}/K'` is compatible with the
quotient maps and the comparison `(X_{k[f]})^*F_{k[V]} ⟶ F_{k[W]}`. -/
theorem map_qProj_comp_sqQuotTheta :
    (modulePullback B S hS (D.relativeMap (D.sqσ ι toS hk f))).map (D.qProj _ K) ≫
        D.sqQuotTheta ι toS hk f K K' e = D.sqThetaF ι toS hk f ≫ D.qProj _ K' :=
  D.map_qProj_comp_quotIso _ K K' e

/-- The transfer `r_*(F_{k[V]}/K) ⟶ r_*(F_{k[W]}/K')`. -/
abbrev sqTransferQ :
    (retractionPushforward B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)).obj
        (D.quotientModule (D.sqT ι toS hk V) K) ⟶
      (retractionPushforward B S hS (D.relativeMap (D.sqπ ι toS hk W)) (D.sqRep ι toS hk W)).obj
        (D.quotientModule (D.sqT ι toS hk W) K') :=
  transferMap B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)
    (D.relativeMap (D.sqπ ι toS hk W)) (D.sqRep ι toS hk W) (D.relativeMap (D.sqσ ι toS hk f))
    (D.sqH_sqR ι toS hk f) (D.sqQuotTheta ι toS hk f K K' e)

include hY in
/-- **The transfers intertwine the maps `r_*F ⟶ r_*𝒬`.** -/
theorem sqG_comp_sqTransferQ :
    D.sqG ι toS hk V K ≫ D.sqTransferQ ι toS hk f K K' e =
      D.sqTransfer ι toS hk f ≫ D.sqG ι toS hk W K' :=
  transferMap_naturality B S hS _ _ _ _ _ (D.sqH_sqR ι toS hk f) (D.qProj _ K) (D.qProj _ K')
    (D.sqThetaF ι toS hk f) (D.sqQuotTheta ι toS hk f K K' e)
    (D.map_qProj_comp_sqQuotTheta ι toS hk f K K' e)

include hY in
/-- The identification of the restriction of `F_{k[V]}/K` to `X_k` with `F_k/K₀` factors through
the identification of the pullback of `F_{k[V]}/K` with `F_{k[W]}/K'` and the identification for
`F_{k[W]}/K'`. -/
theorem sqQuotIso_hom_eq (hres : D.quotientPullback (D.sqβ ι toS hk V) K = K₀)
    (hres' : D.quotientPullback (D.sqβ ι toS hk W) K' = K₀) :
    (D.sqQuotIso ι toS hk K₀ V K hres).hom =
      (modulePullbackTriangle B S hS (D.sqI_sqH ι toS hk f)).hom.app
          (D.quotientModule (D.sqT ι toS hk V) K) ≫
        (modulePullback B S hS (D.relativeMap (D.sqβ ι toS hk W))).map
          (D.sqQuotTheta ι toS hk f K K' e) ≫ (D.sqQuotIso ι toS hk K₀ W K' hres').hom :=
  CategoryTheory.Functor.comparison_hom_eq_of_fac
    (modulePullbackTriangle B S hS (D.sqI_sqH ι toS hk f)).hom (D.qProj _ K) (D.qProj _ K')
    (D.qProj _ K₀) (D.sqBaseIso ι toS hk V) (D.sqBaseIso ι toS hk W) _ _ _ _
    (D.sqQuotIso_hom ι toS hk K₀ V K hres) (D.sqQuotIso_hom ι toS hk K₀ W K' hres')
    (D.map_qProj_comp_sqQuotTheta ι toS hk f K K' e) (D.sqBaseIso_hom_eq ι toS hk f)

include hY in
/-- **The transfer carries the multiplication by `v` to the multiplication by `f v`.** -/
theorem sqμ_comp_sqTransferQ (hK : K ∈ D.quotients (D.sqT ι toS hk V))
    (hK' : K' ∈ D.quotients (D.sqT ι toS hk W))
    (hres : D.quotientPullback (D.sqβ ι toS hk V) K = K₀)
    (hres' : D.quotientPullback (D.sqβ ι toS hk W) K' = K₀) (v : ↥V) :
    retractionMultiplicationFactor B S hS _ _ (D.sqQuotIso ι toS hk K₀ V K hres) hK.1
        (D.sq_isSplitThickeningBy ι toS hk V) v ≫ D.sqTransferQ ι toS hk f K K' e =
      retractionMultiplicationFactor B S hS _ _ (D.sqQuotIso ι toS hk K₀ W K' hres') hK'.1
        (D.sq_isSplitThickeningBy ι toS hk W) (f.hom.hom v) :=
  retractionMultiplicationFactor_comp_transferMap B S hS (D.sq_isSplitThickeningBy ι toS hk V)
    (D.sq_isSplitThickeningBy ι toS hk W) (D.sqQuotIso ι toS hk K₀ V K hres)
    (D.sqQuotIso ι toS hk K₀ W K' hres') hK.1 hK'.1 f (D.relativeMap (D.sqσ ι toS hk f))
    (D.sqH_sqR ι toS hk f) (D.sqI_sqH ι toS hk f) (D.sqQuotTheta ι toS hk f K K' e)
    (D.sqQuotIso_hom_eq ι toS hk f K₀ K K' e hres hres')
    (fun U w => D.sq_transfer_functions ι toS hk f U w) v

end QuotSituation

end AlgebraicGeometry.Space

end
