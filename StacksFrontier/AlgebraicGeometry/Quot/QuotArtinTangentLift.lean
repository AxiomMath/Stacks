module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinTangentDifference
public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinTangentSplit
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackInfFinite
public import StacksFrontier.AlgebraicGeometry.Quot.QuotValuativeExtension

/-!
# Deformations of a quotient over `k[V]` as lifts over copower extensions

Let `D` be a situation of Stacks 09TR over a base with a unique point over every scheme of the
site, with `F` flat over the base, and let `F_k ⟶ F_k/𝒦₀` be a quotient over a field `k`. A
quotient `F_{k[V]} ⟶ 𝒬` over `k[V]` which is quasi-coherent, flat over `k[V]` and restricts to
`F_k/𝒦₀` gives, after the direct image along the retraction `r : X_{k[V]} ⟶ X_k`, a lift of
`F_k ⟶ F_k/𝒦₀` over the copower extension `0 ⟶ F_k ⊗ V ⟶ r_*F_{k[V]} ⟶ F_k ⟶ 0`
(`Deformation.ModuleDeformation.CopowerQuotientLift`). This file builds these lifts, shows that
the difference with a fixed lift determines the quotient, and builds the maps between the lifts
over `k[V]` and their pullbacks to `k[W]` along a linear map `f : V ⟶ W`, which are the inputs of
the naturality of the difference.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.sqBaseExtension`: the extension `r_*F_{k[V]}`.
* `AlgebraicGeometry.Space.QuotSituation.sqLift`: the lift attached to a quotient over `k[V]`.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.map_qProj_comp_quotIso`: the projection onto a
  pulled-back quotient, read through the base-change comparison.
* `AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison_fac_hom`: the base-change
  comparisons along a factorization of morphisms of test schemes.

## Implementation notes

The module `F_T` is spelled throughout as the inverse image `(X_T ⟶ X)^*F`, the spelling of the
components of the base-change comparisons, rather than as
`AlgebraicGeometry.Space.QuotientSituation.baseChangeModule`: comparing two spellings of the same
object inside a morphism forces the inverse-image functors to be unfolded.
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

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A coherence of comparisons with composites, at an object.** If the comparison
`c₁ : P₀ ≅ P₁ ⋙ L₁` factors through `c₂ : P₀ ≅ P₂ ⋙ L₂`, `cσ : P₂ ≅ P₁ ⋙ Lσ` and
`τ : L₁ ≅ Lσ ⋙ L₂`, then so do the inverses of its components. -/
theorem _root_.CategoryTheory.Functor.inv_app_of_comparison_fac {C D₀ D₁ D₂ : Type*} [Category C]
    [Category D₀] [Category D₁] [Category D₂] {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂}
    {L₁ : D₁ ⥤ D₀} {L₂ : D₂ ⥤ D₀} {Lσ : D₁ ⥤ D₂} (c₁ : P₀ ≅ P₁ ⋙ L₁) (c₂ : P₀ ≅ P₂ ⋙ L₂)
    (cσ : P₂ ≅ P₁ ⋙ Lσ) (τ : L₁ ≅ Lσ ⋙ L₂)
    (hfac : c₁ = (c₂ ≪≫ Functor.isoWhiskerRight cσ L₂ ≪≫ Functor.associator P₁ Lσ L₂) ≪≫
      (Functor.isoWhiskerLeft P₁ τ).symm) (M : C) :
    c₁.inv.app M = τ.hom.app (P₁.obj M) ≫ L₂.map (cσ.inv.app M) ≫ c₂.inv.app M := by
  subst hfac
  simp

/-- `CategoryTheory.Functor.inv_app_of_comparison_fac` for isomorphisms and a morphism
identified with the components of the comparisons. -/
theorem _root_.CategoryTheory.Functor.hom_eq_of_comparison_fac {C D₀ D₁ D₂ : Type*} [Category C]
    [Category D₀] [Category D₁] [Category D₂] {P₀ : C ⥤ D₀} {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂}
    {L₁ : D₁ ⥤ D₀} {L₂ : D₂ ⥤ D₀} {Lσ : D₁ ⥤ D₂} (c₁ : P₀ ≅ P₁ ⋙ L₁) (c₂ : P₀ ≅ P₂ ⋙ L₂)
    (cσ : P₂ ≅ P₁ ⋙ Lσ) (τ : L₁ ≅ Lσ ⋙ L₂)
    (hfac : c₁ = (c₂ ≪≫ Functor.isoWhiskerRight cσ L₂ ≪≫ Functor.associator P₁ Lσ L₂) ≪≫
      (Functor.isoWhiskerLeft P₁ τ).symm) (M : C)
    (ψ₁ : L₁.obj (P₁.obj M) ≅ P₀.obj M) (ψ₂ : L₂.obj (P₂.obj M) ≅ P₀.obj M)
    (θ : Lσ.obj (P₁.obj M) ⟶ P₂.obj M) (hψ₁ : ψ₁.hom = c₁.inv.app M)
    (hψ₂ : ψ₂.hom = c₂.inv.app M) (hθ : θ = cσ.inv.app M) :
    ψ₁.hom = τ.hom.app (P₁.obj M) ≫ L₂.map θ ≫ ψ₂.hom := by
  subst hθ
  rw [hψ₁, hψ₂]
  exact Functor.inv_app_of_comparison_fac c₁ c₂ cσ τ hfac M

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-! ### Quotients of `F_T`, with `F_T` read as the inverse image of `F`

The base-change comparisons of the situation are components of isomorphisms of functors at `F`,
so their sources and targets are the inverse images `(X_T ⟶ X)^*F`, spelled as such. The
projections onto quotients and the inclusions of kernels are recorded here with that spelling, so
that no two spellings of `F_T` ever have to be compared inside a morphism. -/

/-- The projection `F_T ⟶ F_T/K`, with `F_T` spelled as the inverse image of `F`. -/
def qProj (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) :
    (modulePullback B S hS (D.sourceProjection T)).obj D.F ⟶ D.quotientModule T K :=
  D.quotientProjection T K

/-- The projection `F_T ⟶ F_T/K` is an epimorphism. -/
instance (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)) : Epi (D.qProj T K) :=
  D.epi_quotientProjection T K

/-- The inclusion `K ⟶ F_T`, with `F_T` spelled as the inverse image of `F`. -/
def kArrow {T : SchemesOver D.Y} (K : Subobject (D.baseChangeModule T)) :
    (K : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) ⟶
      (modulePullback B S hS (D.sourceProjection T)).obj D.F :=
  K.arrow

/-- The inclusion `K ⟶ F_T` is a monomorphism. -/
instance {T : SchemesOver D.Y} (K : Subobject (D.baseChangeModule T)) : Mono (D.kArrow K) :=
  inferInstanceAs (Mono K.arrow)

/-- The composite `K ⟶ F_T ⟶ F_T/K` is zero. -/
theorem kArrow_qProj {T : SchemesOver D.Y} (K : Subobject (D.baseChangeModule T)) :
    D.kArrow K ≫ D.qProj T K = 0 :=
  cokernel.condition K.arrow

/-- The sequence `K ⟶ F_T ⟶ F_T/K` is exact. -/
theorem exact_kArrow_qProj {T : SchemesOver D.Y} (K : Subobject (D.baseChangeModule T)) :
    (ShortComplex.mk (D.kArrow K) (D.qProj T K) (D.kArrow_qProj K)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel K.arrow)

/-- If the composite `K ⟶ F_T ⟶ F_T/K'` is zero, then `K ≤ K'`. -/
theorem le_of_kArrow_qProj {T : SchemesOver D.Y} (K K' : Subobject (D.baseChangeModule T))
    (h : D.kArrow K ≫ D.qProj T K' = 0) : K ≤ K' := by
  have h' := le_kernelSubobject (cokernel.π K'.arrow) K h
  rwa [kernelSubobject_cokernel_π] at h'

/-- **The projection onto a pulled-back quotient, read through the base-change comparison.**
For `h : T' ⟶ T` and `K' = h^*K`, the inverse image of `F_T ⟶ F_T/K` followed by the
identification `(X_h)^*(F_T/K) ≅ F_{T'}/K'` is the inverse of the comparison
`F_{T'} ≅ (X_h)^*F_T` followed by `F_{T'} ⟶ F_{T'}/K'`. -/
theorem map_qProj_comp_quotIso {T' T : SchemesOver D.Y} (h : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (K' : Subobject (D.baseChangeModule T'))
    (e : D.quotientPullback h K = K') :
    (modulePullback B S hS (D.relativeMap h)).map (D.qProj T K) ≫
        ((D.quotientPullbackCokernelIso h K).symm ≪≫
          eqToIso (congrArg (D.quotientModule T') e)).hom =
      (D.baseChangeComparison h).inv.app D.F ≫ D.qProj T' K' := by
  subst e
  rw [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  have h₂ : D.quotientProjection T' (D.quotientPullback h K) =
      D.quotientPullbackProjection h K ≫ (D.quotientPullbackCokernelIso h K).inv :=
    (Iso.eq_comp_inv _).2 (D.quotientProjection_comp_quotientPullbackCokernelIso_hom h K)
  change _ = _ ≫ D.quotientProjection T' (D.quotientPullback h K)
  rw [h₂, ← cancel_epi ((D.baseChangeComparison h).hom.app D.F), Iso.hom_inv_id_app_assoc]
  change _ = ((D.baseChangeComparison h).hom.app D.F ≫
    (modulePullback B S hS (D.relativeMap h)).map (D.quotientProjection T K)) ≫ _
  rw [Category.assoc]
  rfl

/-- **The base-change comparisons along a factorization `β₂ ≫ σ = β₁` of morphisms of test
schemes**: the comparison along `β₁` is the comparison along `σ` followed by the comparison along
`β₂`, read through the comparison of Stacks 03LU. -/
theorem baseChangeComparison_inv_app_of_comp {T₀ T₁ T₂ : SchemesOver D.Y} (β₁ : T₀ ⟶ T₁)
    (β₂ : T₀ ⟶ T₂) (σ : T₂ ⟶ T₁) (e : β₂ ≫ σ = β₁)
    (hih : D.relativeMap β₂ ≫ D.relativeMap σ = D.relativeMap β₁) :
    (D.baseChangeComparison β₁).inv.app D.F =
      (modulePullbackTriangle B S hS hih).hom.app
          ((modulePullback B S hS (D.sourceProjection T₁)).obj D.F) ≫
        (modulePullback B S hS (D.relativeMap β₂)).map ((D.baseChangeComparison σ).inv.app D.F) ≫
          (D.baseChangeComparison β₂).inv.app D.F := by
  subst e
  have hc := D.baseChangeComparison_comp (modulePushforwardCoherence B S hS) β₂ σ
  have tri : modulePullbackTriangle B S hS (baseChangeMap_comp D.f β₂ σ).symm =
      modulePullbackTriangle B S hS hih := rfl
  rw [tri] at hc
  exact Functor.inv_app_of_comparison_fac _ _ _ _ hc D.F

/-- `AlgebraicGeometry.Space.QuotientSituation.baseChangeComparison_inv_app_of_comp` for
isomorphisms and a morphism identified with the components of the comparisons. -/
theorem baseChangeComparison_fac_hom {T₀ T₁ T₂ : SchemesOver D.Y} (β₁ : T₀ ⟶ T₁)
    (β₂ : T₀ ⟶ T₂) (σ : T₂ ⟶ T₁) (e : β₂ ≫ σ = β₁)
    (hih : D.relativeMap β₂ ≫ D.relativeMap σ = D.relativeMap β₁)
    (ψ₁ : (modulePullback B S hS (D.relativeMap β₁)).obj
        ((modulePullback B S hS (D.sourceProjection T₁)).obj D.F) ≅
      (modulePullback B S hS (D.sourceProjection T₀)).obj D.F)
    (ψ₂ : (modulePullback B S hS (D.relativeMap β₂)).obj
        ((modulePullback B S hS (D.sourceProjection T₂)).obj D.F) ≅
      (modulePullback B S hS (D.sourceProjection T₀)).obj D.F)
    (θ : (modulePullback B S hS (D.relativeMap σ)).obj
        ((modulePullback B S hS (D.sourceProjection T₁)).obj D.F) ⟶
      (modulePullback B S hS (D.sourceProjection T₂)).obj D.F)
    (hψ₁ : ψ₁.hom = (D.baseChangeComparison β₁).inv.app D.F)
    (hψ₂ : ψ₂.hom = (D.baseChangeComparison β₂).inv.app D.F)
    (hθ : θ = (D.baseChangeComparison σ).inv.app D.F) :
    ψ₁.hom = (modulePullbackTriangle B S hS hih).hom.app
          ((modulePullback B S hS (D.sourceProjection T₁)).obj D.F) ≫
        (modulePullback B S hS (D.relativeMap β₂)).map θ ≫ ψ₂.hom := by
  subst hθ
  rw [hψ₁, hψ₂]
  exact D.baseChangeComparison_inv_app_of_comp β₁ β₂ σ e hih

end QuotientSituation

namespace QuotSituation

variable (D : QuotSituation B S hS)
  (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
  [hY : ∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]
  {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S) (hk : B.Contains (Spec (.of k)))
  (hF : IsFlatOver B S hS D.X.2 D.f.hom D.F)

/-! ### The extension `r_*F_{k[V]}` -/

/-- The identification of the restriction of `F_{k[V]}` to `X_k` with `F_k`. -/
abbrev sqBaseIso (V : FGModuleCat.{u} k) :
    (modulePullback B S hS (D.relativeMap (D.sqβ ι toS hk V))).obj
        ((modulePullback B S hS (D.sourceProjection (D.sqT ι toS hk V))).obj D.F) ≅
      (modulePullback B S hS (D.sourceProjection (D.sq₀ ι toS hk))).obj D.F where
  hom := (D.baseChangeComparison (D.sqβ ι toS hk V)).inv.app D.F
  inv := (D.baseChangeComparison (D.sqβ ι toS hk V)).hom.app D.F
  hom_inv_id := (D.baseChangeComparison (D.sqβ ι toS hk V)).inv_hom_id_app D.F
  inv_hom_id := (D.baseChangeComparison (D.sqβ ι toS hk V)).hom_inv_id_app D.F

/-- **The extension `0 ⟶ F_k ⊗ V ⟶ r_*F_{k[V]} ⟶ F_k ⟶ 0`.** -/
def sqBaseExtension (V : FGModuleCat.{u} k) :
    letI := D.sqLinear ι toS hk
    ModuleDeformation.CopowerExtension
      ((modulePullback B S hS (D.sourceProjection (D.sq₀ ι toS hk))).obj D.F) V :=
  D.sqExtension ι toS hk V _ _ (D.sqBaseIso ι toS hk V)
    (D.isQuasicoherentOnSite_baseChangeModule _) (D.isFlatOver_baseChangeModule hF _)

/-- The projection `r_*F_{k[V]} ⟶ F_k` of the extension
`AlgebraicGeometry.Space.QuotSituation.sqBaseExtension` is the projection of the retraction `r`,
read through the identification `AlgebraicGeometry.Space.QuotSituation.sqBaseIso`. -/
theorem sqBaseExtension_p (V : FGModuleCat.{u} k) :
    letI := D.sqLinear ι toS hk
    (D.sqBaseExtension ι toS hk hF V).p =
      retractionProjection B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)
        (D.relativeMap (D.sqβ ι toS hk V)) (D.sqI_sqR ι toS hk V) _ _ (D.sqBaseIso ι toS hk V) :=
  rfl

/-! ### The lift attached to a quotient over `k[V]` -/

variable (K₀ : Subobject (D.baseChangeModule (D.sq₀ ι toS hk)))

/-- The identification of the restriction of a quotient over `k[V]` lifting `F_k/𝒦₀` with
`F_k/𝒦₀`. -/
abbrev sqQuotIso (V : FGModuleCat.{u} k) (K : Subobject (D.baseChangeModule (D.sqT ι toS hk V)))
    (hres : D.quotientPullback (D.sqβ ι toS hk V) K = K₀) :
    (modulePullback B S hS (D.relativeMap (D.sqβ ι toS hk V))).obj
        (D.quotientModule (D.sqT ι toS hk V) K) ≅
      D.quotientModule (D.sq₀ ι toS hk) K₀ :=
  (D.quotientPullbackCokernelIso (D.sqβ ι toS hk V) K).symm ≪≫
    eqToIso (congrArg (D.quotientModule (D.sq₀ ι toS hk)) hres)

/-- The inverse image along `X_k ⟶ X_{k[V]}` of the projection `F_{k[V]} ⟶ 𝒬`, followed by the
identification `AlgebraicGeometry.Space.QuotSituation.sqQuotIso`, is the base-change comparison
followed by the projection `F_k ⟶ F_k/𝒦₀`. -/
theorem sqQuotIso_hom (V : FGModuleCat.{u} k)
    (K : Subobject (D.baseChangeModule (D.sqT ι toS hk V)))
    (hres : D.quotientPullback (D.sqβ ι toS hk V) K = K₀) :
    (modulePullback B S hS (D.relativeMap (D.sqβ ι toS hk V))).map
        (D.qProj (D.sqT ι toS hk V) K) ≫ (D.sqQuotIso ι toS hk K₀ V K hres).hom =
      (D.baseChangeComparison (D.sqβ ι toS hk V)).inv.app D.F ≫
        D.qProj (D.sq₀ ι toS hk) K₀ :=
  D.map_qProj_comp_quotIso _ K K₀ hres

/-- The map `r_*F_{k[V]} ⟶ r_*𝒬` of a quotient over `k[V]`. -/
abbrev sqG (V : FGModuleCat.{u} k) (K : Subobject (D.baseChangeModule (D.sqT ι toS hk V))) :
    (retractionPushforward B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)).obj
        ((modulePullback B S hS (D.sourceProjection (D.sqT ι toS hk V))).obj D.F) ⟶
      (retractionPushforward B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)).obj
        (D.quotientModule (D.sqT ι toS hk V) K) :=
  (retractionPushforward B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)).map
    (D.qProj (D.sqT ι toS hk V) K)

/-- The map `r_*F_{k[V]} ⟶ r_*𝒬` lies over `F_k ⟶ F_k/𝒦₀`: followed by the projection
`r_*𝒬 ⟶ F_k/𝒦₀` it is the projection `r_*F_{k[V]} ⟶ F_k` followed by `F_k ⟶ F_k/𝒦₀`. -/
theorem sqG_p (V : FGModuleCat.{u} k) (K : Subobject (D.baseChangeModule (D.sqT ι toS hk V)))
    (hres : D.quotientPullback (D.sqβ ι toS hk V) K = K₀) :
    D.sqG ι toS hk V K ≫ retractionProjection B S hS (D.relativeMap (D.sqπ ι toS hk V))
        (D.sqRep ι toS hk V) (D.relativeMap (D.sqβ ι toS hk V)) (D.sqI_sqR ι toS hk V) _ _
        (D.sqQuotIso ι toS hk K₀ V K hres) =
      retractionProjection B S hS (D.relativeMap (D.sqπ ι toS hk V)) (D.sqRep ι toS hk V)
          (D.relativeMap (D.sqβ ι toS hk V)) (D.sqI_sqR ι toS hk V) _ _ (D.sqBaseIso ι toS hk V) ≫
        D.qProj (D.sq₀ ι toS hk) K₀ := by
  rw [retractionProjection, retractionProjection, ← Category.assoc, reductionMap_naturality,
    Category.assoc, Category.assoc, D.sqQuotIso_hom ι toS hk K₀ V K hres]

/-- The map `r_*F_{k[V]} ⟶ r_*𝒬` commutes with multiplication by `v ∈ V`: the multiplication
factor `F_k ⟶ r_*F_{k[V]}` of `v` followed by it is `F_k ⟶ F_k/𝒦₀` followed by the
multiplication factor `F_k/𝒦₀ ⟶ r_*𝒬` of `v`. -/
theorem sqG_μ (V : FGModuleCat.{u} k) (K : Subobject (D.baseChangeModule (D.sqT ι toS hk V)))
    (hK : K ∈ D.quotients (D.sqT ι toS hk V))
    (hres : D.quotientPullback (D.sqβ ι toS hk V) K = K₀) (v : ↥V) :
    retractionMultiplicationFactor B S hS _ _ (D.sqBaseIso ι toS hk V)
        (D.isQuasicoherentOnSite_baseChangeModule _) (D.sq_isSplitThickeningBy ι toS hk V) v ≫
        D.sqG ι toS hk V K =
      D.qProj (D.sq₀ ι toS hk) K₀ ≫
        retractionMultiplicationFactor B S hS _ _ (D.sqQuotIso ι toS hk K₀ V K hres) hK.1
          (D.sq_isSplitThickeningBy ι toS hk V) v := by
  have := epi_retractionProjection B S hS _ _ (D.sqBaseIso ι toS hk V)
    (D.isQuasicoherentOnSite_baseChangeModule _) (D.sq_isSplitThickeningBy ι toS hk V)
  rw [← cancel_epi (retractionProjection B S hS (D.relativeMap (D.sqπ ι toS hk V))
    (D.sqRep ι toS hk V) (D.relativeMap (D.sqβ ι toS hk V)) (D.sqI_sqR ι toS hk V) _ _
    (D.sqBaseIso ι toS hk V)),
    ← Category.assoc, retractionProjection_comp_factor, ← Category.assoc,
    ← D.sqG_p ι toS hk K₀ V K hres, Category.assoc, retractionProjection_comp_factor,
    retractionMultiplication, retractionMultiplication, ← Functor.map_comp, ← Functor.map_comp,
    Stacks.Cohomology.SiteModules.comp_globalSmul]

/-- **The lift of `F_k ⟶ F_k/𝒦₀` over `r_*F_{k[V]}` attached to a quotient over `k[V]`** which
is quasi-coherent, flat over `k[V]` and restricts to `F_k/𝒦₀`. -/
def sqLift (V : FGModuleCat.{u} k) (K : Subobject (D.baseChangeModule (D.sqT ι toS hk V)))
    (hK : K ∈ D.quotients (D.sqT ι toS hk V))
    (hres : D.quotientPullback (D.sqβ ι toS hk V) K = K₀) :
    letI := D.sqLinear ι toS hk
    ModuleDeformation.CopowerQuotientLift (D.qProj (D.sq₀ ι toS hk) K₀)
      (D.sqBaseExtension ι toS hk hF V) :=
  letI := D.sqLinear ι toS hk
  { ext := D.sqExtension ι toS hk V _ _ (D.sqQuotIso ι toS hk K₀ V K hres) hK.1 hK.2
    g := D.sqG ι toS hk V K
    g_p := D.sqG_p ι toS hk K₀ V K hres
    μ_g := D.sqG_μ ι toS hk K₀ V K hK hres }

end QuotSituation

end AlgebraicGeometry.Space

end
