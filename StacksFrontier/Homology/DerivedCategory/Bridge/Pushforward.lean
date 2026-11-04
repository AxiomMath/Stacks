module

public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.RingedSpace.DerivedPushforward
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic

/-!
# The derived pushforward at two models of the derived category

A total right derived functor `RF` of `F` along a localization `L` is determined up to unique
isomorphism by its universal property, so it can be compared across two models of the derived
category by `StacksDraft.DerivedModel.rightDerivedModelIso`. This file records how that comparison
interacts with the comparison maps `F ⟶ L ⋙ RF`, and specializes it to the derived direct images
`Rf_*` of the library, along the comparison equivalence `StacksDraft.DerivedModel.modelEquiv` of
two arbitrary models.

## Main results

* `rightDerivedModelIso_hom_app_fac`: `rightDerivedModelIso` is compatible with the units.
* `isIso_app_iff_of_isRightDerivedFunctor`: the unit is invertible at an object in one model iff it
  is in the other.
* `derivedPushforwardModelEquivIso`, `ringedSpaceDerivedPushforwardModelEquivIso`,
  `schemeDerivedPushforwardModelEquivIso`: `Rf_* ⋙ e_Y ≅ e_X ⋙ Rf_*` for the three spellings of
  the derived direct image (ringed spaces, twice, and schemes), at two arbitrary models.
* `isIso_derivedPushforwardUnit_app_iff_model` and its analogues: whether `f_* K ⟶ Rf_* K` is
  invertible does not depend on the model.
* `isIso_derivedPushforward_map_iff_model`, `isZero_derivedPushforward_obj_iff_model` and their
  analogues: invertibility of a morphism and vanishing of an object after `Rf_*` do not depend
  on the model.
* `derivedPushforwardStandardIso`, `schemeDerivedPushforwardStandardIso` and their corollaries:
  the specializations along `SheafOfModules.derivedModelEquiv` and
  `AlgebraicGeometry.Scheme.Modules.derivedModelEquiv`, from `HasDerivedCategory.standard` to the
  locally small models.

## Implementation notes

Every model is an explicit binder, and no `HasDerivedCategory` instance is installed locally, so
both models can appear in one statement.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u w₁ w₂ w₃ w₄

namespace StacksDraft.DerivedModel

/-! ### Compatibility of the transport with the units -/

section Generic

variable {K : Type*} [Category* K] {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {E₁ : Type*} [Category* E₁] {E₂ : Type*} [Category* E₂]
  (W : MorphismProperty K)
  {L₁ : K ⥤ D₁} {L₂ : K ⥤ D₂} [L₁.IsLocalization W] [L₂.IsLocalization W]
  {G : D₁ ⥤ D₂} [G.IsEquivalence] {J : E₁ ⥤ E₂} [J.IsEquivalence]
  {F₁ : K ⥤ E₁} {RF₁ : D₁ ⥤ E₁} (α₁ : F₁ ⟶ L₁ ⋙ RF₁) [RF₁.IsRightDerivedFunctor α₁ W]
  {F₂ : K ⥤ E₂} {RF₂ : D₂ ⥤ E₂} (α₂ : F₂ ⟶ L₂ ⋙ RF₂) [RF₂.IsRightDerivedFunctor α₂ W]

/-- The comparison `rightDerivedModelIso` of two right derived functors is compatible with their
units: transporting the unit of `RF₁` along it gives the unit of `RF₂`. -/
@[reassoc]
theorem rightDerivedModelIso_hom_app_fac (hG : L₁ ⋙ G ≅ L₂) (hF : F₁ ⋙ J ≅ F₂) (X : K) :
    J.map (α₁.app X) ≫ (rightDerivedModelIso W α₁ α₂ hG hF).hom.app (L₁.obj X) =
      hF.hom.app X ≫ α₂.app X ≫ RF₂.map (hG.inv.app X) := by
  let := isRightDerivedFunctor_comp_isEquivalence W α₂ hG
  simpa [rightDerivedModelIso, transportRightDerivedUnit] using
    Functor.rightDerivedNatTrans_app (RF₁ ⋙ J) (G ⋙ RF₂)
      (whiskerRight α₁ J ≫ (Functor.associator L₁ RF₁ J).hom)
      (transportRightDerivedUnit α₂ hG) W hF.hom X

include W in
/-- The unit of a right derived functor is invertible at an object in one model if and only if
the unit of the corresponding right derived functor is invertible there in the other model. -/
theorem isIso_app_iff_of_isRightDerivedFunctor (hG : L₁ ⋙ G ≅ L₂) (hF : F₁ ⋙ J ≅ F₂) (X : K) :
    IsIso (α₁.app X) ↔ IsIso (α₂.app X) := by
  rw [← isIso_iff_of_reflects_iso _ J, ← isIso_comp_right_iff _
    ((rightDerivedModelIso W α₁ α₂ hG hF).hom.app (L₁.obj X)),
    rightDerivedModelIso_hom_app_fac, isIso_comp_left_iff, isIso_comp_right_iff]

end Generic

/-! ### Invertibility and vanishing across a comparison of functors -/

section Transfer

variable {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {E₁ : Type*} [Category* E₁] {E₂ : Type*} [Category* E₂]
  {G : D₁ ⥤ D₂} {J : E₁ ⥤ E₂} [J.IsEquivalence] {RF₁ : D₁ ⥤ E₁} {RF₂ : D₂ ⥤ E₂}
  (e : RF₁ ⋙ J ≅ G ⋙ RF₂)

include e in
/-- If `RF₁ ⋙ J ≅ G ⋙ RF₂` with `J` an equivalence, then `RF₁` inverts a morphism if and only if
`RF₂` inverts its image under `G`. -/
theorem isIso_map_iff_of_iso {X Y : D₁} (φ : X ⟶ Y) :
    IsIso (RF₁.map φ) ↔ IsIso (RF₂.map (G.map φ)) := by
  rw [← isIso_iff_of_reflects_iso _ J]
  exact NatIso.isIso_map_iff e φ

include e in
/-- If `RF₁ ⋙ J ≅ G ⋙ RF₂` with `J` an equivalence of categories with zero morphisms, then
`RF₁` kills an object if and only if `RF₂` kills its image under `G`. -/
theorem isZero_obj_iff_of_iso [HasZeroMorphisms E₁] [HasZeroMorphisms E₂] (X : D₁) :
    IsZero (RF₁.obj X) ↔ IsZero (RF₂.obj (G.obj X)) := by
  refine ⟨fun h => (J.map_isZero h).of_iso (e.app X).symm, fun h => ?_⟩
  exact (J.asEquivalence.inverse.map_isZero ((h.of_iso (e.app X)))).of_iso
    (J.asEquivalence.unitIso.app _)

end Transfer

/-! ### The derived direct image of `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces` -/

section RingedSpaces

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (hX₁ : HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X)))
  (hY₁ : HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y)))
  (hX₂ : HasDerivedCategory.{w₃} (SheafOfModules.{u} (structureSheafRing X)))
  (hY₂ : HasDerivedCategory.{w₄} (SheafOfModules.{u} (structureSheafRing Y)))

/-- Degreewise pushforward followed by localization, at two models of `D(𝒪_Y)`: the two agree
up to the comparison equivalence. -/
def pushforwardToDerivedCategoryModelEquivIso :
    @pushforwardToDerivedCategory X Y f hY₁ ⋙ (modelEquiv hY₁ hY₂).functor ≅
      @pushforwardToDerivedCategory X Y f hY₂ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Localization.compUniqFunctor _ _ _)

/-- **`Rf_*` does not depend on the model.** The derived direct image along a morphism of ringed
spaces, at two arbitrary models of `D(𝒪_X)` and `D(𝒪_Y)`, commutes with the comparison
equivalences. -/
def derivedPushforwardModelEquivIso :
    @derivedPushforward X Y f hX₁ hY₁ ⋙ (modelEquiv hY₁ hY₂).functor ≅
      (modelEquiv hX₁ hX₂).functor ⋙ @derivedPushforward X Y f hX₂ hY₂ :=
  rightDerivedModelIso
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ))
    (@derivedPushforwardUnit X Y f hX₁ hY₁)
    (@derivedPushforwardUnit X Y f hX₂ hY₂) (Localization.compUniqFunctor _ _ _)
    (pushforwardToDerivedCategoryModelEquivIso f hY₁ hY₂)

/-- The comparison `f_* K ⟶ Rf_* K` is invertible in one model if and only if it is in the
other. -/
theorem isIso_derivedPushforwardUnit_app_iff_model
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) :
    IsIso ((@derivedPushforwardUnit X Y f hX₁ hY₁).app K) ↔
      IsIso ((@derivedPushforwardUnit X Y f hX₂ hY₂).app K) :=
  isIso_app_iff_of_isRightDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) _ _
    (Localization.compUniqFunctor _ _ (HomotopyCategory.subcategoryAcyclic _).trW)
    (pushforwardToDerivedCategoryModelEquivIso f hY₁ hY₂) K

/-- `Rf_*` inverts a morphism in one model if and only if it inverts its transport in the
other. -/
theorem isIso_derivedPushforward_map_iff_model
    {K L : @DerivedCategory _ _ _ hX₁} (φ : K ⟶ L) :
    IsIso ((@derivedPushforward X Y f hX₁ hY₁).map φ) ↔
      IsIso ((@derivedPushforward X Y f hX₂ hY₂).map ((modelEquiv hX₁ hX₂).functor.map φ)) :=
  isIso_map_iff_of_iso (derivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂) φ

/-- `Rf_*` kills an object in one model if and only if it kills its transport in the other. -/
theorem isZero_derivedPushforward_obj_iff_model (K : @DerivedCategory _ _ _ hX₁) :
    IsZero ((@derivedPushforward X Y f hX₁ hY₁).obj K) ↔
      IsZero ((@derivedPushforward X Y f hX₂ hY₂).obj ((modelEquiv hX₁ hX₂).functor.obj K)) :=
  isZero_obj_iff_of_iso (derivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂) K

/-- The isomorphism `derivedPushforwardModelEquivIso` is compatible with the comparisons
`f_* ⟶ Rf_*` of the two models. -/
@[reassoc]
theorem derivedPushforwardModelEquivIso_hom_app_fac
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) :
    (modelEquiv hY₁ hY₂).functor.map ((@derivedPushforwardUnit X Y f hX₁ hY₁).app K) ≫
        (derivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂).hom.app
          ((@DerivedCategory.Qh _ _ _ hX₁).obj K) =
      (pushforwardToDerivedCategoryModelEquivIso f hY₁ hY₂).hom.app K ≫
        (@derivedPushforwardUnit X Y f hX₂ hY₂).app K ≫
          (@derivedPushforward X Y f hX₂ hY₂).map
            ((Localization.compUniqFunctor _ _ (HomotopyCategory.subcategoryAcyclic _).trW).inv.app
              K) :=
  rightDerivedModelIso_hom_app_fac _ _ _ _ _ K

end RingedSpaces

section RingedSpacesStandard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- `derivedPushforwardModelEquivIso` from the standard model to the locally small model
`SheafOfModules.hasDerivedCategory`, along `SheafOfModules.derivedModelEquiv`. -/
abbrev derivedPushforwardStandardIso :
    @derivedPushforward X Y f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) ⋙
        (SheafOfModules.derivedModelEquiv (structureSheafRing Y)).functor ≅
      (SheafOfModules.derivedModelEquiv (structureSheafRing X)).functor ⋙
        derivedPushforward f :=
  derivedPushforwardModelEquivIso f _ _ _ _

/-- `Rf_*` kills an object of the standard model if and only if it kills its transport to the
locally small model. -/
theorem isZero_derivedPushforward_obj_iff_standard
    (K : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing X)))) :
    IsZero ((@derivedPushforward X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _)).obj K) ↔
      IsZero ((derivedPushforward f).obj
        ((SheafOfModules.derivedModelEquiv (structureSheafRing X)).functor.obj K)) :=
  isZero_derivedPushforward_obj_iff_model f _ _ _ _ K

/-- `Rf_*` inverts a morphism of the standard model if and only if it inverts its transport to
the locally small model. -/
theorem isIso_derivedPushforward_map_iff_standard
    {K L : @DerivedCategory _ _ _ (HasDerivedCategory.standard
      (SheafOfModules.{u} (structureSheafRing X)))} (φ : K ⟶ L) :
    IsIso ((@derivedPushforward X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _)).map φ) ↔
      IsIso ((derivedPushforward f).map
        ((SheafOfModules.derivedModelEquiv (structureSheafRing X)).functor.map φ)) :=
  isIso_derivedPushforward_map_iff_model f _ _ _ _ φ

end RingedSpacesStandard

/-! ### The derived direct image `AlgebraicGeometry.RingedSpace.derivedPushforward` -/

section RingedSpaceDerivedPushforward

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (hX₁ : HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X)))
  (hY₁ : HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing Y)))
  (hX₂ : HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing X)))
  (hY₂ : HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y)))

/-- `AlgebraicGeometry.RingedSpace.pushforwardToDerivedCategory` at two models of `D(𝒪_Y)`. -/
def ringedSpacePushforwardToDerivedCategoryModelEquivIso :
    @RingedSpace.pushforwardToDerivedCategory X Y f hY₁ ⋙ (modelEquiv hY₁ hY₂).functor ≅
      @RingedSpace.pushforwardToDerivedCategory X Y f hY₂ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Localization.compUniqFunctor _ _ _)

/-- **`AlgebraicGeometry.RingedSpace.derivedPushforward` does not depend on the model.** At two
arbitrary models of `D(𝒪_X)` and `D(𝒪_Y)` it commutes with the comparison equivalences. -/
def ringedSpaceDerivedPushforwardModelEquivIso :
    @RingedSpace.derivedPushforward X Y f hX₁ hY₁ ⋙ (modelEquiv hY₁ hY₂).functor ≅
      (modelEquiv hX₁ hX₂).functor ⋙ @RingedSpace.derivedPushforward X Y f hX₂ hY₂ :=
  rightDerivedModelIso
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ))
    (@RingedSpace.derivedPushforwardUnit X Y f hX₁ hY₁)
    (@RingedSpace.derivedPushforwardUnit X Y f hX₂ hY₂) (Localization.compUniqFunctor _ _ _)
    (ringedSpacePushforwardToDerivedCategoryModelEquivIso f hY₁ hY₂)

/-- The comparison `f_* K ⟶ Rf_* K` of `AlgebraicGeometry.RingedSpace.derivedPushforward` is
invertible in one model if and only if it is in the other. -/
theorem isIso_ringedSpaceDerivedPushforwardUnit_app_iff_model
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) :
    IsIso ((@RingedSpace.derivedPushforwardUnit X Y f hX₁ hY₁).app K) ↔
      IsIso ((@RingedSpace.derivedPushforwardUnit X Y f hX₂ hY₂).app K) :=
  isIso_app_iff_of_isRightDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (.up ℤ)) _ _
    (Localization.compUniqFunctor _ _ (HomotopyCategory.subcategoryAcyclic _).trW)
    (ringedSpacePushforwardToDerivedCategoryModelEquivIso f hY₁ hY₂) K

/-- `AlgebraicGeometry.RingedSpace.derivedPushforward` inverts a morphism in one model if and only
if it inverts its transport in the other. -/
theorem isIso_ringedSpaceDerivedPushforward_map_iff_model
    {K L : @DerivedCategory _ _ _ hX₁} (φ : K ⟶ L) :
    IsIso ((@RingedSpace.derivedPushforward X Y f hX₁ hY₁).map φ) ↔
      IsIso ((@RingedSpace.derivedPushforward X Y f hX₂ hY₂).map
        ((modelEquiv hX₁ hX₂).functor.map φ)) :=
  isIso_map_iff_of_iso (ringedSpaceDerivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂) φ

/-- `AlgebraicGeometry.RingedSpace.derivedPushforward` kills an object in one model if and only if
it kills its transport in the other. -/
theorem isZero_ringedSpaceDerivedPushforward_obj_iff_model (K : @DerivedCategory _ _ _ hX₁) :
    IsZero ((@RingedSpace.derivedPushforward X Y f hX₁ hY₁).obj K) ↔
      IsZero ((@RingedSpace.derivedPushforward X Y f hX₂ hY₂).obj
        ((modelEquiv hX₁ hX₂).functor.obj K)) :=
  isZero_obj_iff_of_iso (ringedSpaceDerivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂) K

end RingedSpaceDerivedPushforward

section RingedSpaceDerivedPushforwardStandard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- `ringedSpaceDerivedPushforwardModelEquivIso` from the standard model to the locally small
model, along `SheafOfModules.derivedModelEquiv`. -/
abbrev ringedSpaceDerivedPushforwardStandardIso :
    @RingedSpace.derivedPushforward X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) ⋙
        (SheafOfModules.derivedModelEquiv (structureSheafRing Y)).functor ≅
      (SheafOfModules.derivedModelEquiv (structureSheafRing X)).functor ⋙
        RingedSpace.derivedPushforward f :=
  ringedSpaceDerivedPushforwardModelEquivIso f _ _ _ _

end RingedSpaceDerivedPushforwardStandard

/-! ### The derived direct image `Stacks.Duality.derivedPushforward` of schemes -/

section Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hX₁ : HasDerivedCategory.{w₁} X.Modules) (hY₁ : HasDerivedCategory.{w₁} Y.Modules)
  (hX₂ : HasDerivedCategory.{w₂} X.Modules) (hY₂ : HasDerivedCategory.{w₂} Y.Modules)

/-- `Stacks.Duality.homotopyPushforward` at two models of `D(𝒪_Y)`. -/
def schemeHomotopyPushforwardModelEquivIso :
    @Stacks.Duality.homotopyPushforward X Y f hY₁ ⋙ (modelEquiv hY₁ hY₂).functor ≅
      @Stacks.Duality.homotopyPushforward X Y f hY₂ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Localization.compUniqFunctor _ _ _)

/-- **`Rf_*` on schemes does not depend on the model.** The derived direct image
`Stacks.Duality.derivedPushforward` along a morphism of schemes, at two arbitrary models of
`D(𝒪_X)` and `D(𝒪_Y)`, commutes with the comparison equivalences. -/
def schemeDerivedPushforwardModelEquivIso :
    @Stacks.Duality.derivedPushforward X Y f hX₁ hY₁ ⋙ (modelEquiv hY₁ hY₂).functor ≅
      (modelEquiv hX₁ hX₂).functor ⋙ @Stacks.Duality.derivedPushforward X Y f hX₂ hY₂ :=
  rightDerivedModelIso (HomotopyCategory.quasiIso X.Modules (.up ℤ))
    ((@Stacks.Duality.homotopyPushforward X Y f hY₁).totalRightDerivedUnit
      (@DerivedCategory.Qh _ _ _ hX₁) (HomotopyCategory.quasiIso X.Modules (.up ℤ)))
    ((@Stacks.Duality.homotopyPushforward X Y f hY₂).totalRightDerivedUnit
      (@DerivedCategory.Qh _ _ _ hX₂) (HomotopyCategory.quasiIso X.Modules (.up ℤ)))
    (Localization.compUniqFunctor _ _ _) (schemeHomotopyPushforwardModelEquivIso f hY₁ hY₂)

/-- The comparison `f_* K ⟶ Rf_* K` on schemes is invertible in one model if and only if it is in
the other. -/
theorem isIso_schemeDerivedPushforwardUnit_app_iff_model
    (K : HomotopyCategory X.Modules (.up ℤ)) :
    IsIso (((@Stacks.Duality.homotopyPushforward X Y f hY₁).totalRightDerivedUnit
        (@DerivedCategory.Qh _ _ _ hX₁) (HomotopyCategory.quasiIso X.Modules (.up ℤ))).app K) ↔
      IsIso (((@Stacks.Duality.homotopyPushforward X Y f hY₂).totalRightDerivedUnit
        (@DerivedCategory.Qh _ _ _ hX₂) (HomotopyCategory.quasiIso X.Modules (.up ℤ))).app K) :=
  isIso_app_iff_of_isRightDerivedFunctor (HomotopyCategory.quasiIso X.Modules (.up ℤ)) _ _
    (Localization.compUniqFunctor _ _ (HomotopyCategory.subcategoryAcyclic _).trW)
    (schemeHomotopyPushforwardModelEquivIso f hY₁ hY₂) K

/-- `Rf_*` on schemes inverts a morphism in one model if and only if it inverts its transport in
the other. -/
theorem isIso_schemeDerivedPushforward_map_iff_model
    {K L : @DerivedCategory _ _ _ hX₁} (φ : K ⟶ L) :
    IsIso ((@Stacks.Duality.derivedPushforward X Y f hX₁ hY₁).map φ) ↔
      IsIso ((@Stacks.Duality.derivedPushforward X Y f hX₂ hY₂).map
        ((modelEquiv hX₁ hX₂).functor.map φ)) :=
  isIso_map_iff_of_iso (schemeDerivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂) φ

/-- `Rf_*` on schemes kills an object in one model if and only if it kills its transport in the
other. -/
theorem isZero_schemeDerivedPushforward_obj_iff_model (K : @DerivedCategory _ _ _ hX₁) :
    IsZero ((@Stacks.Duality.derivedPushforward X Y f hX₁ hY₁).obj K) ↔
      IsZero ((@Stacks.Duality.derivedPushforward X Y f hX₂ hY₂).obj
        ((modelEquiv hX₁ hX₂).functor.obj K)) :=
  isZero_obj_iff_of_iso (schemeDerivedPushforwardModelEquivIso f hX₁ hY₁ hX₂ hY₂) K

end Scheme

section SchemeStandard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `schemeDerivedPushforwardModelEquivIso` from the standard model to the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. -/
abbrev schemeDerivedPushforwardStandardIso :
    @Stacks.Duality.derivedPushforward X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) ⋙
        (Scheme.Modules.derivedModelEquiv Y).functor ≅
      (Scheme.Modules.derivedModelEquiv X).functor ⋙
        Stacks.Duality.derivedPushforward f :=
  schemeDerivedPushforwardModelEquivIso f _ _ _ _

/-- `Rf_*` on schemes kills an object of the standard model if and only if it kills its transport
to the locally small model. -/
theorem isZero_schemeDerivedPushforward_obj_iff_standard
    (K : @DerivedCategory _ _ _ (HasDerivedCategory.standard X.Modules)) :
    IsZero ((@Stacks.Duality.derivedPushforward X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _)).obj K) ↔
      IsZero ((Stacks.Duality.derivedPushforward f).obj
        ((Scheme.Modules.derivedModelEquiv X).functor.obj K)) :=
  isZero_schemeDerivedPushforward_obj_iff_model f _ _ _ _ K

/-- `Rf_*` on schemes inverts a morphism of the standard model if and only if it inverts its
transport to the locally small model. -/
theorem isIso_schemeDerivedPushforward_map_iff_standard
    {K L : @DerivedCategory _ _ _ (HasDerivedCategory.standard X.Modules)} (φ : K ⟶ L) :
    IsIso ((@Stacks.Duality.derivedPushforward X Y f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _)).map φ) ↔
      IsIso ((Stacks.Duality.derivedPushforward f).map
        ((Scheme.Modules.derivedModelEquiv X).functor.map φ)) :=
  isIso_schemeDerivedPushforward_map_iff_model f _ _ _ _ φ

end SchemeStandard

end StacksDraft.DerivedModel

end
