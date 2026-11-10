module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleUnitEnd
public import StacksFrontier.AlgebraicGeometry.Quot.PicardTestSectionsScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedModuleStalk

/-!
# On an affine represented space the associated module is `𝒪 ⊗_R -`

Let `U` be an object of the big fppf site whose scheme is affine, with ring of functions
`R = Γ(U, 𝒪_U)`. Two functors `Mod(R) ⥤ Mod(𝒪_{h_U})` produce "the quasi-coherent module of an
`R`-module" on the small étale site of the algebraic space `h_U`:

* the associated module `M ↦ M^~` (`AlgebraicGeometry.Space.representedAffineAssociated`), through
  which the derived categories of `R` and of `D_QCoh(𝒪_{h_U})` are compared;
* the base-ring tensor product `M ↦ 𝒪 ⊗_R M` of Stacks 0D3F
  (`AlgebraicGeometry.Space.baseRingTensorModule`), whose global sections are computed on the
  model of the small étale site.

This file identifies them, naturally in `M`.

## The argument

The base-ring tensor product is left adjoint to global sections read as `R`-modules, so a
natural transformation `𝒪 ⊗_R - ⟶ (-)^~` is an `R`-linear natural map `M ⟶ Γ(M^~)`; we send `m`
to the section `𝒪 ≅ R^~ ⟶ M^~` induced by `r ↦ r m`. That this is `R`-linear is the statement
that `(a ·)^~`, read on `𝒪` through `R^~ ≅ 𝒪`, is multiplication by the function `a`
(`AlgebraicGeometry.Space.representedAffineAssociatedObjUnitIso_conj_toSpanSingleton`), which is
computed on the section `1` over the identity chart. Both functors preserve colimits, so the
transformation is an isomorphism as soon as it is one at `R`
(`AlgebraicGeometry.Space.isIso_app_of_isIso_app_self`), where both sides corepresent global
sections.

## Main results

* `AlgebraicGeometry.Space.representedAffineAssociatedObjUnitIso_conj_toSpanSingleton`:
  `(a ·)^~` is multiplication by `a` on `𝒪`.
* `AlgebraicGeometry.Space.baseRingTensorModuleIsoRepresentedAffineAssociated`:
  `𝒪 ⊗_R - ≅ (-)^~`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- An endomorphism of the structure sheaf of a represented algebraic space is multiplication by
a function `r`, which is its value on the section `1` over the identity chart. -/
private theorem unitModule_endo_exists_selfChart
    (e : unitModule B S hS (schemeSpace U).2 ⟶ unitModule B S hS (schemeSpace U).2) :
    ∃ r : baseRing B S hS U,
      e = unitModuleMul B S hS (schemeSpace U) (globalFunctionsOfMap (𝟙 (schemeSpace U)) r) ∧
      e.val.app (op (selfChart B S hS U))
        (1 : chartRing B S hS (schemeSpace U).1 (schemeSpace U).2 (selfChart B S hS U)) = r := by
  have hc := (bijective_unitModuleMul (schemeSpace U)).surjective e
  obtain ⟨c, rfl⟩ := hc
  have hr := (bijective_globalFunctionsOfMap_id U).surjective c
  obtain ⟨r, rfl⟩ := hr
  exact ⟨r, rfl, (unitModuleMul_val_app_one B S hS (schemeSpace U) _ (selfChart B S hS U)).trans
    (globalFunctionsOfMap_id_selfChart U r)⟩

/-- **Endomorphisms of the structure sheaf of a represented algebraic space are determined by
their value on the section `1` over the identity chart.** -/
theorem unitModule_endo_ext_selfChart
    {e₁ e₂ : unitModule B S hS (schemeSpace U).2 ⟶ unitModule B S hS (schemeSpace U).2}
    (h : e₁.val.app (op (selfChart B S hS U))
        (1 : chartRing B S hS (schemeSpace U).1 (schemeSpace U).2 (selfChart B S hS U)) =
      e₂.val.app (op (selfChart B S hS U))
        (1 : chartRing B S hS (schemeSpace U).1 (schemeSpace U).2 (selfChart B S hS U))) :
    e₁ = e₂ := by
  obtain ⟨r₁, hr₁, h₁⟩ := unitModule_endo_exists_selfChart B S hS U e₁
  obtain ⟨r₂, hr₂, h₂⟩ := unitModule_endo_exists_selfChart B S hS U e₂
  rw [hr₁, hr₂, (h₁.symm.trans (h.trans h₂))]

section Affine

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- The endomorphism of `𝒪_T` obtained by pulling back `(a ·)^~` along `T ≅ Spec Γ(T, ⊤)` takes the
section `1` to `a`. -/
theorem pullbackUnitIso_conj_tilde_toSpanSingleton_val_app_top
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((Scheme.Modules.pullbackUnitIso ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).inv ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).map
          ((tilde.functor Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).map
            (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ a))) ≫
        (Scheme.Modules.pullbackUnitIso
          ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom).hom).val.app (op ⊤)
      (1 : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) = a := by
  let X := (BigFppfOver.toScheme B S hS).obj U
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (Scheme.Hom.toRingCatSheafHom X.isoSpec.hom)) :=
    (Scheme.Modules.pullbackUnitIso X.isoSpec.hom).isIso_hom
  have h1 := pullbackObjUnitToUnit_conj_val_app_one
    (Scheme.Hom.toRingCatSheafHom X.isoSpec.hom)
    ((tilde.functor Γ(X, ⊤)).map (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ a))) (op ⊤)
  have h2 := tilde_map_toSpanSingleton_val_app_top_one Γ(X, ⊤) a
  refine h1.trans ((congrArg (ConcreteCategory.hom
    ((Scheme.Hom.toRingCatSheafHom X.isoSpec.hom).hom.app (op ⊤))) h2).trans ?_)
  change X.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv a) = a
  rw [show X.isoSpec.hom = X.toSpecΓ from rfl, Scheme.toSpecΓ_appTop]
  simp

/-- **`(a ·)^~`, read on `𝒪` through `R^~ ≅ 𝒪`, is multiplication by the function `a`.** -/
theorem representedAffineAssociatedObjUnitIso_conj_toSpanSingleton (a : baseRing B S hS U) :
    (representedAffineAssociatedObjUnitIso B S hS U).inv ≫
        (representedAffineAssociated B S hS U).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) a)) ≫
          (representedAffineAssociatedObjUnitIso B S hS U).hom =
      unitModuleMul B S hS (schemeSpace U) (globalFunctionsOfMap (𝟙 (schemeSpace U)) a) := by
  apply unitModule_endo_ext_selfChart
  refine Eq.trans ?_ (unitModuleMul_val_app_one B S hS (schemeSpace U) _ (selfChart B S hS U)).symm
  refine Eq.trans ?_ (globalFunctionsOfMap_id_selfChart U a).symm
  let X := (BigFppfOver.toScheme B S hS).obj U
  let a' : Γ(X, ⊤) := a
  let κ : (Scheme.Modules.pullback X.isoSpec.hom).obj ((tilde.functor Γ(X, ⊤)).obj
      (ModuleCat.of Γ(X, ⊤) Γ(X, ⊤))) ≅ SheafOfModules.unit X.ringCatSheaf :=
    (Scheme.Modules.pullback X.isoSpec.hom).mapIso tildeSelf ≪≫
      Scheme.Modules.pullbackUnitIso X.isoSpec.hom
  let G := representedAssociatedModule B S hS U (isAlgebraicSpace_yoneda B S hS U)
  let m := (Scheme.Modules.pullback X.isoSpec.hom).map
    ((tilde.functor Γ(X, ⊤)).map (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ a')))
  let t := κ.inv ≫ m ≫ κ.hom
  let ε := representedAssociatedModuleObjUnitIso B S hS U (isAlgebraicSpace_yoneda B S hS U)
  have hG : G.map t = G.map κ.inv ≫ G.map m ≫ G.map κ.hom :=
    (G.map_comp κ.inv (m ≫ κ.hom)).trans (congrArg (G.map κ.inv ≫ ·) (G.map_comp m κ.hom))
  have e1 : (representedAffineAssociatedObjUnitIso B S hS U).inv ≫
        (representedAffineAssociated B S hS U).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton Γ(X, ⊤) Γ(X, ⊤) a')) ≫
          (representedAffineAssociatedObjUnitIso B S hS U).hom =
      ε.inv ≫ (G.map κ.inv ≫ G.map m ≫ G.map κ.hom) ≫ ε.hom := rfl
  rw [e1, ← hG]
  refine (representedAssociatedModuleObjUnitIso_conj_val_app_selfChart B S hS U t).trans ?_
  have hid : ∀ (M : (Spec Γ(X, ⊤)).Modules) y,
      ((Scheme.Modules.pullback X.isoSpec.hom).map (𝟙 M)).val.app (op ⊤) y = y :=
    fun _ y => congrArg (fun φ => φ.val.app (op ⊤) y)
      ((Scheme.Modules.pullback X.isoSpec.hom).map_id _)
  have e2 : t.val.app (op ⊤) (1 : Γ(X, ⊤)) =
      (Scheme.Modules.pullbackUnitIso X.isoSpec.hom).hom.val.app (op ⊤)
        (((Scheme.Modules.pullback X.isoSpec.hom).map (𝟙 _)).val.app (op ⊤)
          (m.val.app (op ⊤) (((Scheme.Modules.pullback X.isoSpec.hom).map (𝟙 _)).val.app (op ⊤)
            ((Scheme.Modules.pullbackUnitIso X.isoSpec.hom).inv.val.app (op ⊤)
              (1 : Γ(X, ⊤)))))) := rfl
  refine e2.trans (Eq.trans ?_ (pullbackUnitIso_conj_tilde_toSpanSingleton_val_app_top B S hS U a'))
  exact congrArg (fun y => (Scheme.Modules.pullbackUnitIso X.isoSpec.hom).hom.val.app (op ⊤) y)
    ((hid _ _).trans (congrArg (fun y => m.val.app (op ⊤) y) (hid _ _)))

/-- The associated module `M ↦ M^~`, read with the scalars `baseRing B S hS U` and on the modules
of the algebraic space `schemeSpace U`; it is `AlgebraicGeometry.Space.representedAffineAssociated`
up to the spelling of its source and target. -/
def affineAssociated :
    ModuleCat.{u} (baseRing B S hS U) ⥤ Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2 :=
  representedAffineAssociated B S hS U

/-- The functor `M ↦ M^~` is additive. -/
instance additive_affineAssociated : (affineAssociated B S hS U).Additive :=
  inferInstanceAs (representedAffineAssociated B S hS U).Additive

/-- `𝒪 ≅ R^~`. -/
def affineAssociatedUnitIso : unitModule B S hS (schemeSpace U).2 ≅
    (affineAssociated B S hS U).obj (ModuleCat.of (baseRing B S hS U) (baseRing B S hS U)) :=
  (representedAffineAssociatedObjUnitIso B S hS U).symm

/-- `ε ≫ (a ·)^~ = (a ·) ≫ ε` for `ε : 𝒪 ≅ R^~`. -/
@[reassoc]
theorem affineAssociatedUnitIso_hom_comp_map_toSpanSingleton (a : baseRing B S hS U) :
    (affineAssociatedUnitIso B S hS U).hom ≫ (affineAssociated B S hS U).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing B S hS U) (baseRing B S hS U) a)) =
      unitModuleMul B S hS (schemeSpace U) (globalFunctionsOfMap (𝟙 (schemeSpace U)) a) ≫
        (affineAssociatedUnitIso B S hS U).hom := by
  have h : (affineAssociatedUnitIso B S hS U).hom ≫ (affineAssociated B S hS U).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing B S hS U) (baseRing B S hS U) a)) ≫
        (affineAssociatedUnitIso B S hS U).inv =
      unitModuleMul B S hS (schemeSpace U) (globalFunctionsOfMap (𝟙 (schemeSpace U)) a) :=
    representedAffineAssociatedObjUnitIso_conj_toSpanSingleton B S hS U a
  rw [← h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The global section of `M^~` attached to `m ∈ M`: `𝒪 ≅ R^~ ⟶ M^~`, induced by `r ↦ r m`. -/
def affineAssociatedSection (M : ModuleCat.{u} (baseRing B S hS U)) (m : M) :
    unitModule B S hS (schemeSpace U).2 ⟶ (affineAssociated B S hS U).obj M :=
  (affineAssociatedUnitIso B S hS U).hom ≫
    (affineAssociated B S hS U).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing B S hS U) M m))

/-- The section `m̃` of `M^~` is additive in `m`. -/
theorem affineAssociatedSection_add (M : ModuleCat.{u} (baseRing B S hS U)) (m m' : M) :
    affineAssociatedSection B S hS U M (m + m') =
      affineAssociatedSection B S hS U M m + affineAssociatedSection B S hS U M m' := by
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing B S hS U) M (m + m')) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton _ M m) +
        ModuleCat.ofHom (LinearMap.toSpanSingleton _ M m') := by
    ext
    simp
  simp only [affineAssociatedSection, h, Functor.map_add, Preadditive.comp_add]

/-- The section attached to `a • m` is the section attached to `m` precomposed with
multiplication by `a` on `𝒪`. -/
theorem affineAssociatedSection_smul (M : ModuleCat.{u} (baseRing B S hS U))
    (a : baseRing B S hS U) (m : M) :
    affineAssociatedSection B S hS U M (a • m) =
      unitModuleMul B S hS (schemeSpace U) (globalFunctionsOfMap (𝟙 (schemeSpace U)) a) ≫
        affineAssociatedSection B S hS U M m := by
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing B S hS U) M (a • m)) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing B S hS U) (baseRing B S hS U) a) ≫
        ModuleCat.ofHom (LinearMap.toSpanSingleton _ M m) := by
    ext
    simp
  exact (congrArg (fun φ => (affineAssociatedUnitIso B S hS U).hom ≫
    (affineAssociated B S hS U).map φ) h).trans
    ((congrArg ((affineAssociatedUnitIso B S hS U).hom ≫ ·)
      ((affineAssociated B S hS U).map_comp _ _)).trans
      (affineAssociatedUnitIso_hom_comp_map_toSpanSingleton_assoc B S hS U a _))

/-- For a linear map `g : M ⟶ M'`, the section of `M'^~` attached to `g m` is the section of
`M^~` attached to `m` followed by `g^~`. -/
theorem affineAssociatedSection_naturality {M M' : ModuleCat.{u} (baseRing B S hS U)} (g : M ⟶ M')
    (m : M) :
    affineAssociatedSection B S hS U M' (g m) =
      affineAssociatedSection B S hS U M m ≫ (affineAssociated B S hS U).map g := by
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing B S hS U) M' (g m)) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton _ M m) ≫ g := by
    ext
    simp
  rw [affineAssociatedSection, affineAssociatedSection, h, Functor.map_comp, Category.assoc]

/-- The section of `R^~` attached to `1 ∈ R` is the isomorphism `𝒪 ≅ R^~`. -/
theorem affineAssociatedSection_one :
    affineAssociatedSection B S hS U (ModuleCat.of (baseRing B S hS U) (baseRing B S hS U)) 1 =
      (affineAssociatedUnitIso B S hS U).hom := by
  have h1 : ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing B S hS U) (baseRing B S hS U) 1) =
      𝟙 _ := by
    ext
    simp
  rw [affineAssociatedSection, h1, CategoryTheory.Functor.map_id, Category.comp_id]

/-- `m ↦ m̃`, as an `R`-linear map to the global sections of `M^~` read on the model. -/
def affineAssociatedSectionLinearMap (M : ModuleCat.{u} (baseRing B S hS U)) :
    M →ₗ[baseRing B S hS U]
      (baseRingGlobalSectionsModule B S hS (schemeSpace U)
        (baseRingHomOfMap (𝟙 (schemeSpace U)))).obj ((affineAssociated B S hS U).obj M) where
  toFun m := (modelSectionsHomEquiv B S hS (schemeSpace U) _ _).symm
    (affineAssociatedSection B S hS U M m)
  map_add' m m' := by
    rw [affineAssociatedSection_add, modelSectionsHomEquiv_symm_add]
  map_smul' a m :=
    (congrArg (modelSectionsHomEquiv B S hS (schemeSpace U) _ _).symm
      (affineAssociatedSection_smul B S hS U M a m)).trans
      (modelSectionsHomEquiv_symm_comp B S hS (schemeSpace U) (𝟙 _) _ a _)

/-- `m ↦ m̃` is natural in the module. -/
def affineAssociatedSectionNatTrans :
    𝟭 (ModuleCat.{u} (baseRing B S hS U)) ⟶
      affineAssociated B S hS U ⋙
        baseRingGlobalSectionsModule B S hS (schemeSpace U)
            (baseRingHomOfMap (𝟙 (schemeSpace U))) where
  app M := ModuleCat.ofHom (Y := ((baseRingGlobalSectionsModule B S hS (schemeSpace U)
    (baseRingHomOfMap (𝟙 (schemeSpace U)))).obj ((affineAssociated B S hS U).obj M) : Type u))
    (affineAssociatedSectionLinearMap B S hS U M)
  naturality M M' g := by
    ext m
    change (modelSectionsHomEquiv B S hS (schemeSpace U) _ _).symm
        (affineAssociatedSection B S hS U M' (g m)) =
      (baseRingGlobalSectionsModule B S hS (schemeSpace U) _).map
        ((affineAssociated B S hS U).map g)
        ((modelSectionsHomEquiv B S hS (schemeSpace U) _ _).symm
          (affineAssociatedSection B S hS U M m))
    rw [← modelSectionsHomEquiv_symm_naturality, affineAssociatedSection_naturality]

/-- The comparison `𝒪 ⊗_R - ⟶ (-)^~`, transposed from `m ↦ m̃`. -/
def baseRingTensorModuleToAffineAssociated :
    baseRingTensorModule B S hS (schemeSpace U) (baseRingHomOfMap (𝟙 (schemeSpace U))) ⟶
      affineAssociated B S hS U :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (affineAssociatedSectionNatTrans B S hS U) _ ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (affineAssociated B S hS U)
          (baseRingTensorModuleAdjunction B S hS (schemeSpace U) _).counit ≫
          (Functor.rightUnitor _).hom

/-- The component of `𝒪 ⊗_R - ⟶ (-)^~` at `M` is the adjoint transpose of `m ↦ m̃`. -/
theorem baseRingTensorModuleToAffineAssociated_app (M : ModuleCat.{u} (baseRing B S hS U)) :
    (baseRingTensorModuleToAffineAssociated B S hS U).app M =
      ((baseRingTensorModuleAdjunction B S hS (schemeSpace U) _).homEquiv M
        ((affineAssociated B S hS U).obj M)).symm
        ((affineAssociatedSectionNatTrans B S hS U).app M) := by
  simp [baseRingTensorModuleToAffineAssociated, Adjunction.homEquiv_counit]

/-- The comparison `𝒪 ⊗_R R ⟶ R^~` is an isomorphism. -/
theorem isIso_baseRingTensorModuleToAffineAssociated_app_self :
    IsIso ((baseRingTensorModuleToAffineAssociated B S hS U).app
      (ModuleCat.of (baseRing B S hS U) (baseRing B S hS U))) := by
  let R := baseRing B S hS U
  let ε := affineAssociatedUnitIso B S hS U
  refine isIso_of_coyoneda_map_bijective _ fun F => ?_
  let e₁ := ((baseRingTensorModuleAdjunction B S hS (schemeSpace U)
          (baseRingHomOfMap (𝟙 (schemeSpace U)))).homEquiv (ModuleCat.of R R) F).trans
    (ModuleCat.selfHomEquiv R ((baseRingGlobalSectionsModule B S hS (schemeSpace U) _).obj F))
  let g : ((affineAssociated B S hS U).obj (ModuleCat.of R R) ⟶ F) →
      (baseRingGlobalSectionsModule B S hS (schemeSpace U)
          (baseRingHomOfMap (𝟙 (schemeSpace U)))).obj F :=
    fun x => (modelSectionsHomEquiv B S hS (schemeSpace U)
      (baseRingHomOfMap (𝟙 (schemeSpace U))) F).symm (ε.hom ≫ x)
  have hg : Function.Bijective g :=
    (modelSectionsHomEquiv B S hS (schemeSpace U) (baseRingHomOfMap (𝟙 (schemeSpace U)))
      F).symm.bijective.comp
      (show Function.Bijective (fun x : (affineAssociated B S hS U).obj (ModuleCat.of R R) ⟶ F =>
        ε.hom ≫ x) from (ε.symm.homFromEquiv (Z := F)).bijective)
  have key : e₁ ∘ (fun x => (baseRingTensorModuleToAffineAssociated B S hS U).app
      (ModuleCat.of R R) ≫ x) = g := by
    funext x
    change (((baseRingTensorModuleAdjunction B S hS (schemeSpace U)
            (baseRingHomOfMap (𝟙 (schemeSpace U)))).homEquiv _ _)
        ((baseRingTensorModuleToAffineAssociated B S hS U).app
      (ModuleCat.of R R) ≫ x)).hom 1 = _
    rw [Adjunction.homEquiv_naturality_right, baseRingTensorModuleToAffineAssociated_app,
      Equiv.apply_symm_apply]
    change (baseRingGlobalSectionsModule B S hS (schemeSpace U) _).map x
        ((modelSectionsHomEquiv B S hS (schemeSpace U) _ _).symm
          (affineAssociatedSection B S hS U (ModuleCat.of R R) 1)) = _
    rw [← modelSectionsHomEquiv_symm_naturality, affineAssociatedSection_one]
  have hc : Function.Bijective (e₁ ∘ (fun x => (baseRingTensorModuleToAffineAssociated B S hS U).app
      (ModuleCat.of R R) ≫ x)) := key ▸ hg
  exact (Function.Bijective.of_comp_iff' e₁.bijective _).1 hc

/-- **On an affine represented algebraic space, `𝒪 ⊗_R - ≅ (-)^~`**: the base-ring tensor
product of Stacks 0D3F is the associated quasi-coherent module, naturally in the `R`-module. -/
def baseRingTensorModuleIsoAffineAssociated :
    baseRingTensorModule B S hS (schemeSpace U) (baseRingHomOfMap (𝟙 (schemeSpace U))) ≅
      affineAssociated B S hS U :=
  have : ∀ M, IsIso ((baseRingTensorModuleToAffineAssociated B S hS U).app M) :=
    have := (baseRingTensorModuleAdjunction B S hS (schemeSpace U)
      (baseRingHomOfMap (𝟙 (schemeSpace U)))).leftAdjoint_preservesColimits
    have : PreservesColimitsOfSize.{u, u} (affineAssociated B S hS U) :=
      (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
    isIso_app_of_isIso_app_self _
      (isIso_baseRingTensorModuleToAffineAssociated_app_self B S hS U)
  have := NatIso.isIso_of_isIso_app (baseRingTensorModuleToAffineAssociated B S hS U)
  asIso (baseRingTensorModuleToAffineAssociated B S hS U)

/-- `AlgebraicGeometry.Space.baseRingTensorModuleIsoAffineAssociated`, with the target spelled as
`AlgebraicGeometry.Space.representedAffineAssociated`. -/
def baseRingTensorModuleIsoRepresentedAffineAssociated :
    baseRingTensorModule B S hS (schemeSpace U) (baseRingHomOfMap (𝟙 (schemeSpace U))) ≅
      representedAffineAssociated B S hS U :=
  baseRingTensorModuleIsoAffineAssociated B S hS U

end Affine

end AlgebraicGeometry.Space

end
