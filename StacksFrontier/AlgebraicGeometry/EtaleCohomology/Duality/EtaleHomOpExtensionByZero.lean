module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleExtensionByZeroInternalHom
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ScalarCommIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

/-!
# `ℋom_ℤ(j_! F, B) ≅ j_* ℋom_ℤ(F, j⁻¹ B)` as sheaves of `Λᵐᵒᵖ`-modules

For an étale morphism `j : U ⟶ X`, a sheaf `F` of `Λ`-modules on `U_étale` and an abelian sheaf
`B` on `X_étale`, the internal adjunction `Stacks.EtaleCohomology.internalHomExtensionByZeroIso`
is `Λᵐᵒᵖ`-linear for the actions through `F`: extension by zero of sheaves of `Λ`-modules is the
lift of extension by zero of abelian sheaves (both are left adjoint to restriction), on which
`Λ` acts through the image of its action on `F`, and the internal adjunction is natural in `F`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroLiftIso`: `j_!` on sheaves of modules is the
  lift of `j_!` on abelian sheaves.
* `Stacks.EtaleCohomology.homOpExtensionByZeroNatIso`:
  `ℋom_ℤ(j_! F, -) ≅ j_* ∘ ℋom_ℤ(F, -) ∘ j⁻¹` as functors to sheaves of `Λᵐᵒᵖ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Stacks.AbelianInternalHom Stacks.ModuleCatLift

universe u

namespace Stacks.EtaleCohomology

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- The abelian sheaves underlying the lifted and the module restriction agree. -/
def moduleLiftEtaleRestrictionForgetIso (Λ : Type) [Ring Λ] (F : EtaleModules.{u, 0} Λ X) :
    (sheafCompose U.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((moduleLift.{u + 1} Λ X.smallEtaleTopology U.smallEtaleTopology
          (etaleRestriction.{u, 0} j)).obj F) ≅
      (sheafCompose U.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((etaleModuleRestriction.{u, 0} Λ j).obj F) :=
  Iso.refl _

/-- Restriction of sheaves of modules is the lift of restriction of abelian sheaves. -/
def moduleLiftEtaleRestrictionIso (Λ : Type) [Ring Λ] :
    moduleLift.{u + 1} Λ X.smallEtaleTopology U.smallEtaleTopology (etaleRestriction.{u, 0} j) ≅
      etaleModuleRestriction.{u, 0} Λ j :=
  NatIso.ofComponents (fun F => sheafIsoOfScalarComm.{u + 1} Λ _
      (moduleLiftEtaleRestrictionForgetIso j Λ F) (fun _ => rfl))
    (fun _ => rfl)

/-- The abelian sheaves underlying the lifted and the module direct image agree. -/
def moduleLiftEtaleDirectImageForgetIso (Λ : Type) [Ring Λ] (F : EtaleModules.{u, 0} Λ U) :
    (sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((moduleLift.{u + 1} Λ U.smallEtaleTopology X.smallEtaleTopology
          (etaleAbelianDirectImage.{u, 0} j)).obj F) ≅
      (sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((etaleModuleDirectImage.{u, 0} Λ j).obj F) :=
  Iso.refl _

/-- The direct image of sheaves of modules is the lift of the direct image of abelian sheaves. -/
def moduleLiftEtaleDirectImageIso (Λ : Type) [Ring Λ] :
    moduleLift.{u + 1} Λ U.smallEtaleTopology X.smallEtaleTopology
        (etaleAbelianDirectImage.{u, 0} j) ≅
      etaleModuleDirectImage.{u, 0} Λ j :=
  NatIso.ofComponents (fun F => sheafIsoOfScalarComm.{u + 1} Λ _
      (moduleLiftEtaleDirectImageForgetIso j Λ F) (fun _ => rfl))
    (fun _ => rfl)

/-- **Extension by zero of sheaves of modules is the lift of extension by zero of abelian
sheaves**: both are left adjoint to restriction. -/
def etaleModuleExtensionByZeroLiftIso (Λ : Type) [Ring Λ] :
    etaleModuleExtensionByZero.{u, 0} Λ j ≅
      moduleLift.{u + 1} Λ U.smallEtaleTopology X.smallEtaleTopology (extensionByZero.{u, 0} j) :=
  Adjunction.leftAdjointUniq (etaleModuleExtensionByZeroAdj.{u, 0} Λ j)
    ((moduleLiftAdjunction.{u + 1} Λ _ _ (extensionByZero.{u, 0} j) (etaleRestriction.{u, 0} j)
      (extensionByZeroAdj.{u, 0} j)).ofNatIsoRight (moduleLiftEtaleRestrictionIso j Λ))

variable (Λ : Type) [Ring Λ]

/-- `ℋom_ℤ(j_! F, B) ≅ j_* ℋom_ℤ(F, j⁻¹ B)` for the lifted extension by zero, as sheaves of
`Λᵐᵒᵖ`-modules. -/
def homOpLiftExtensionByZeroIso (F : EtaleModules.{u, 0} Λ U)
    (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    homOpSheaf X.smallEtaleTopology
        ((moduleLift.{u + 1} Λ U.smallEtaleTopology X.smallEtaleTopology
          (extensionByZero.{u, 0} j)).obj F)
        B ≅
      (moduleLift.{u + 1} Λᵐᵒᵖ U.smallEtaleTopology X.smallEtaleTopology
        (etaleAbelianDirectImage.{u, 0} j)).obj
          (homOpSheaf U.smallEtaleTopology F ((etaleRestriction.{u, 0} j).obj B)) :=
  sheafIsoOfScalarComm.{u + 1} Λᵐᵒᵖ _ (internalHomExtensionByZeroIso j (toAb _ F) B) (fun a =>
    internalHomExtensionByZeroIso_hom_naturality_left j B (sheafScalarEnd Λ _ F a.unop))

/-- `ℋom_ℤ(j_! F, B) ≅ j_* ℋom_ℤ(F, j⁻¹ B)` for the lifted extension by zero is natural in `B`. -/
lemma homOpLiftExtensionByZeroIso_hom_naturality (F : EtaleModules.{u, 0} Λ U)
    {B B' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (b : B ⟶ B') :
    homOpMap X.smallEtaleTopology
        ((moduleLift.{u + 1} Λ U.smallEtaleTopology X.smallEtaleTopology
          (extensionByZero.{u, 0} j)).obj F) b ≫
        (homOpLiftExtensionByZeroIso j Λ F B').hom =
      (homOpLiftExtensionByZeroIso j Λ F B).hom ≫
        (moduleLift.{u + 1} Λᵐᵒᵖ U.smallEtaleTopology X.smallEtaleTopology
          (etaleAbelianDirectImage.{u, 0} j)).map
            (homOpMap U.smallEtaleTopology F ((etaleRestriction.{u, 0} j).map b)) :=
  (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]
    exact internalHomExtensionByZeroIso_hom_naturality_right j (toAb _ F) b)

/-- Precomposition with an isomorphism `φ : G₁ ≅ G₂`, on `ℋom_ℤ(-, B)`. -/
def homOpMapLeftIso {G₁ G₂ : EtaleModules.{u, 0} Λ X} (φ : G₁ ≅ G₂)
    (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    homOpSheaf X.smallEtaleTopology G₂ B ≅ homOpSheaf X.smallEtaleTopology G₁ B where
  hom := homOpMapLeft _ φ.hom B
  inv := homOpMapLeft _ φ.inv B
  hom_inv_id := by rw [homOpMapLeft_comp, φ.inv_hom_id, homOpMapLeft_id]
  inv_hom_id := by rw [homOpMapLeft_comp, φ.hom_inv_id, homOpMapLeft_id]

/-- **`ℋom_ℤ(j_! F, B) ≅ j_* ℋom_ℤ(F, j⁻¹ B)` as sheaves of `Λᵐᵒᵖ`-modules.** -/
def homOpExtensionByZeroIso (F : EtaleModules.{u, 0} Λ U)
    (B : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    homOpSheaf X.smallEtaleTopology ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F) B ≅
      (etaleModuleDirectImage.{u, 0} Λᵐᵒᵖ j).obj
        (homOpSheaf U.smallEtaleTopology F ((etaleRestriction.{u, 0} j).obj B)) :=
  (homOpMapLeftIso Λ ((etaleModuleExtensionByZeroLiftIso j Λ).app F) B).symm ≪≫
    homOpLiftExtensionByZeroIso j Λ F B ≪≫ (moduleLiftEtaleDirectImageIso j Λᵐᵒᵖ).app _

/-- `ℋom_ℤ(j_! F, B) ≅ j_* ℋom_ℤ(F, j⁻¹ B)` is natural in `B`. -/
lemma homOpExtensionByZeroIso_hom_naturality (F : EtaleModules.{u, 0} Λ U)
    {B B' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (b : B ⟶ B') :
    homOpMap X.smallEtaleTopology ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F) b ≫
        (homOpExtensionByZeroIso j Λ F B').hom =
      (homOpExtensionByZeroIso j Λ F B).hom ≫ (etaleModuleDirectImage.{u, 0} Λᵐᵒᵖ j).map
        (homOpMap U.smallEtaleTopology F ((etaleRestriction.{u, 0} j).map b)) := by
  simp only [homOpExtensionByZeroIso, Iso.trans_hom, Iso.symm_hom, homOpMapLeftIso, Iso.app_hom,
    Category.assoc]
  rw [← Category.assoc, ← homOpMapLeft_homOpMap, Category.assoc, ← Category.assoc
    (homOpMap _ _ b), homOpLiftExtensionByZeroIso_hom_naturality, Category.assoc,
    (moduleLiftEtaleDirectImageIso j Λᵐᵒᵖ).hom.naturality]

/-- **`ℋom_ℤ(j_! F, -) ≅ j_* ∘ ℋom_ℤ(F, -) ∘ j⁻¹`** as functors from abelian sheaves on `X` to
sheaves of `Λᵐᵒᵖ`-modules on `X`. -/
def homOpExtensionByZeroNatIso (F : EtaleModules.{u, 0} Λ U) :
    homOpFunctor X.smallEtaleTopology ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F) ≅
      etaleRestriction.{u, 0} j ⋙ homOpFunctor U.smallEtaleTopology F ⋙
        etaleModuleDirectImage.{u, 0} Λᵐᵒᵖ j :=
  NatIso.ofComponents (homOpExtensionByZeroIso j Λ F)
    (fun b => homOpExtensionByZeroIso_hom_naturality j Λ F b)

end Stacks.EtaleCohomology

end
