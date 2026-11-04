module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusIdValue
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusCompIsoh
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback

/-!
# Values of the comparisons of derived restriction and extension by zero

The comparisons `Rj^{-1} ≅ j^{-1}` and `j^{-1} ∘ Rj_! ≅ 𝟭` on bounded below derived categories of
étale sheaves of modules, at the image of a bounded below complex: the localizations of the
underived comparisons.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedRestrictionIsoInverseImagePlus_hom_app_Qh`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- The factorization of `F` through the localization, followed by the identity comparison and
the composition comparison of `𝟭 ∘ F ≅ H`, is the localization of the underived comparison
followed by the factorization of `H`. -/
private theorem factorsh_inv_comp_idIso_inv_comp_compIsoh_hom {Y : Scheme.{u}}
    (F H : EtaleModules.{u, 0} Λ X ⥤ EtaleModules.{u, 0} Λ Y) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ≅ H)
    (M : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    F.mapDerivedCategoryPlusFactorsh.inv.app M ≫
        Functor.mapDerivedCategoryPlusIdIso.inv.app
          (F.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj M)) ≫
        (Functor.mapDerivedCategoryPlusCompIsoh (Functor.rightUnitor F ≪≫ e)).hom.app
          (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso e).hom.app M) ≫
        H.mapDerivedCategoryPlusFactorsh.inv.app M := by
  have h2 := Functor.mapDerivedCategoryPlusIdIso.inv.naturality
    (F.mapDerivedCategoryPlusFactorsh.inv.app M)
  have h3 := Functor.mapDerivedCategoryPlusCompIsoh_compatible (Functor.rightUnitor F ≪≫ e) M
  have hinv : Functor.mapDerivedCategoryPlusIdIso.inv.app (DerivedCategory.Plus.Qh.obj
      (F.mapHomotopyCategoryPlus.obj M)) =
      (𝟭 (EtaleModules.{u, 0} Λ Y)).mapDerivedCategoryPlusFactorsh.inv.app
        (F.mapHomotopyCategoryPlus.obj M) :=
    (Iso.inv_eq_inv (Functor.mapDerivedCategoryPlusIdIso.app _)
      ((𝟭 (EtaleModules.{u, 0} Λ Y)).mapDerivedCategoryPlusFactorsh.app _)).2
      (Functor.mapDerivedCategoryPlusIdIso_hom_app_Qh _)
  have hNT : (Functor.mapHomotopyCategoryPlusNatTrans (Functor.rightUnitor F ≪≫ e).hom).app M =
      (Functor.mapHomotopyCategoryPlusNatIso e).hom.app M := by
    apply (HomotopyCategory.Plus.ι _).map_injective
    change (NatTrans.mapHomotopyCategory _ (ComplexShape.up ℤ)).app M.obj =
      (NatTrans.mapHomotopyCategory _ (ComplexShape.up ℤ)).app M.obj
    congr 2
  simp only [Functor.id_map, Functor.comp_obj] at h2
  rw [reassoc_of% h2, hinv]
  refine h3.trans ?_
  rw [hNT]

/-- **The comparison `Rj^{-1} ≅ j^{-1}` at the image of a complex**: the unit of `Rj^{-1}`
followed by the comparison is the localization of the underived comparison followed by the
factorization of `j^{-1}` through the localization. -/
lemma etaleModuleDerivedRestrictionIsoInverseImagePlus_hom_app_Qh
    (M : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleRestriction.{u, 0} Λ j).rightDerivedFunctorPlusUnit.app M ≫
        (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ j).hom.app
          (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm).hom.app M) ≫
        (etaleModuleInverseImage.{u, 0} Λ j).mapDerivedCategoryPlusFactorsh.inv.app M := by
  have h1 := Functor.unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app
    (etaleModuleRestriction.{u, 0} Λ j) M
  have hρ : (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ j).hom.app
      (DerivedCategory.Plus.Qh.obj M) =
      (etaleModuleRestriction.{u, 0} Λ j).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
          (DerivedCategory.Plus.Qh.obj M) ≫
        Functor.mapDerivedCategoryPlusIdIso.inv.app
          ((etaleModuleRestriction.{u, 0} Λ j).mapDerivedCategoryPlus.obj
            (DerivedCategory.Plus.Qh.obj M)) ≫
        (Functor.mapDerivedCategoryPlusCompIsoh (Functor.rightUnitor _ ≪≫
          (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm)).hom.app
            (DerivedCategory.Plus.Qh.obj M) := by
    simp [etaleModuleDerivedRestrictionIsoInverseImagePlus]
  rw [hρ, reassoc_of% h1]
  exact factorsh_inv_comp_idIso_inv_comp_compIsoh_hom Λ _ _
    (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm M

section OpenImmersion

/-- The cancellation pattern of
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_Qh`. -/
lemma value_chain {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C} (a : X₀ ⟶ X₁)
    (ri : X₁ ⟶ X₂) (c1 : X₂ ⟶ X₃) (c2 : X₃ ⟶ X₄) (ri' : X₀ ⟶ Y₁) (R : Y₁ ⟶ X₂) (fh : X₀ ⟶ Y₂)
    (q1 : Y₂ ⟶ Y₃) (uR : Y₃ ⟶ Y₁) (q2 : Y₃ ⟶ Y₄) (uER : Y₄ ⟶ X₃) (q3 : Y₄ ⟶ X₄)
    (qε : Y₂ ⟶ X₄) (q23 : Y₃ ⟶ X₄)
    (n : a ≫ ri = ri' ≫ R) (hr : ri' = fh ≫ q1 ≫ uR) (f1 : uR ≫ R ≫ c1 = q2 ≫ uER)
    (f2 : uER ≫ c2 = q3) (h23 : q2 ≫ q3 = q23) (hc : q1 ≫ q23 = qε) :
    a ≫ ri ≫ c1 ≫ c2 = fh ≫ qε := by
  rw [reassoc_of% n, hr]
  simp only [Category.assoc, reassoc_of% f1, f2, h23, hc]

variable [IsOpenImmersion j]

/-- The underived comparison `j^{-1} ∘ j_! ≅ 𝟭` for an open immersion `j`. -/
def etaleModuleExtensionByZeroInverseImageIso :
    etaleModuleExtensionByZero.{u, 0} Λ j ⋙ etaleModuleInverseImage.{u, 0} Λ j ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft _ (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j) ≪≫
    (asIso (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit).symm

/-- **The comparison `j^{-1} ∘ Rj_! ≅ 𝟭` at the image of a complex**: `j^{-1}` of the unit of
`Rj_!` followed by the comparison is the factorization of `j^{-1}` through the localization
followed by the localization of the underived comparison. -/
lemma etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_Qh
    (K : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ U)) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ j).map
        ((etaleModuleExtensionByZero.{u, 0} Λ j).rightDerivedFunctorPlusUnit.app K) ≫
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ j).hom.app
        (DerivedCategory.Plus.Qh.obj K) =
    (etaleModuleInverseImage.{u, 0} Λ j).mapDerivedCategoryPlusFactorsh.hom.app
        ((etaleModuleExtensionByZero.{u, 0} Λ j).mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
        (etaleModuleExtensionByZeroInverseImageIso Λ j)).hom.app K : _ ⟶ K) := by
  let N := (etaleModuleExtensionByZero.{u, 0} Λ j).mapHomotopyCategoryPlus.obj K
  let ρ := etaleModuleDerivedRestrictionIsoInverseImagePlus Λ j
  have hdef : (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ j).hom.app
      (DerivedCategory.Plus.Qh.obj K) =
      ρ.inv.app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j).obj (DerivedCategory.Plus.Qh.obj K)) ≫
        (Functor.rightDerivedFunctorPlusCompIsoOfExact (etaleModuleExtensionByZero.{u, 0} Λ j)
          (etaleModuleRestriction.{u, 0} Λ j) _ (Iso.refl _)).hom.app
            (DerivedCategory.Plus.Qh.obj K) ≫
        (Functor.rightDerivedFunctorPlusIdIsoOf _
          (asIso (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit).symm).hom.app
            (DerivedCategory.Plus.Qh.obj K) := by
    simp [etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso,
      etaleModuleDerivedExtensionByZeroCompRestrictionIso, ρ]
  have vρ := etaleModuleDerivedRestrictionIsoInverseImagePlus_hom_app_Qh Λ j N
  have hρinv : ρ.inv.app (DerivedCategory.Plus.Qh.obj N) =
      (etaleModuleInverseImage.{u, 0} Λ j).mapDerivedCategoryPlusFactorsh.hom.app N ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm).inv.app N) ≫
        (etaleModuleRestriction.{u, 0} Λ j).rightDerivedFunctorPlusUnit.app N := by
    rw [← cancel_mono (ρ.hom.app _), Iso.inv_hom_id_app, Category.assoc, Category.assoc, vρ,
      ← Category.assoc (DerivedCategory.Plus.Qh.map _), ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    rfl
  have n :=
    ρ.inv.naturality ((etaleModuleExtensionByZero.{u, 0} Λ j).rightDerivedFunctorPlusUnit.app K)
  have f1 :=
    Functor.rightDerivedFunctorPlusCompIsoOfExact_fac (etaleModuleExtensionByZero.{u, 0} Λ j)
      (etaleModuleRestriction.{u, 0} Λ j) _ (Iso.refl _) K
  have f2 := Functor.rightDerivedFunctorPlusIdIsoOf_fac _
    (asIso (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit).symm K
  rw [hdef]
  refine value_chain (q23 := DerivedCategory.Plus.Qh.map
    ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (etaleModuleExtensionByZero.{u, 0} Λ j ⋙
        etaleModuleRestriction.{u, 0} Λ j))).hom.app K ≫
      (Functor.mapHomotopyCategoryPlusIdIsoOf _
        (asIso (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit).symm).hom.app K))
    _ _ _ _ _ _ _ _ _ _ _ _ _ n hρinv f1 f2 ?_ ?_
  · exact (Functor.map_comp _ _ _).symm
  · rw [← Functor.map_comp]
    congr 1

end OpenImmersion

section Identity

omit [Etale j] in
/-- Reassociating a four-fold composite `a ≫ b ≫ c ≫ d` as `(a ≫ b ≫ c) ≫ d`. -/
lemma assoc_three {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) : a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

variable (X)

/-- **The derived inverse image along the identity is the identity** on `D⁺(X_étale, Λ)`. -/
def etaleModuleDerivedInverseImagePlusIdIso :
    etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X) ≅ 𝟭 _ :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ Functor.mapDerivedCategoryPlusIdIso.symm ≪≫
    Functor.mapDerivedCategoryPlusCompIsoh
      (Functor.rightUnitor _ ≪≫ etaleModuleInverseImageIdIso.{u, 0} Λ X) ≪≫
    Functor.mapDerivedCategoryPlusIdIso

/-- `etaleModuleDerivedInverseImagePlusIdIso` at the image of a complex: the localization of the
underived comparison. -/
lemma etaleModuleDerivedInverseImagePlusIdIso_hom_app_Qh
    (M : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleInverseImage.{u, 0} Λ (𝟙 X)).mapDerivedCategoryPlusFactorsh.inv.app M ≫
        (etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso
        (etaleModuleInverseImageIdIso.{u, 0} Λ X)).hom.app M : _ ⟶ M) := by
  have hM := Functor.mapDerivedCategoryPlusIdIso_hom_app_Qh M
  have hθ : (etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app (DerivedCategory.Plus.Qh.obj M) =
      Functor.mapDerivedCategoryPlusIdIso.inv.app
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj
            (DerivedCategory.Plus.Qh.obj M)) ≫
        (Functor.mapDerivedCategoryPlusCompIsoh
          (Functor.rightUnitor _ ≪≫ etaleModuleInverseImageIdIso.{u, 0} Λ X)).hom.app
            (DerivedCategory.Plus.Qh.obj M) ≫
        Functor.mapDerivedCategoryPlusIdIso.hom.app (DerivedCategory.Plus.Qh.obj M) := by
    simp [etaleModuleDerivedInverseImagePlusIdIso]
  rw [hθ, reassoc_of% factorsh_inv_comp_idIso_inv_comp_compIsoh_hom Λ _ _
    (etaleModuleInverseImageIdIso.{u, 0} Λ X) M, hM]
  exact (whisker_eq _ (Iso.inv_hom_id_app
    (𝟭 (EtaleModules.{u, 0} Λ X)).mapDerivedCategoryPlusFactorsh M)).trans (Category.comp_id _)

end Identity

end Stacks.EtaleCohomology
