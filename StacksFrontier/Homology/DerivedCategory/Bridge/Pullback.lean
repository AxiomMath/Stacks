module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pushforward
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# The derived pullback commutes with the comparison of two models of the derived category

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. The derived pullback
`Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` is defined at any choice of models of `D(𝒪_X)` and of `D(𝒪_Y)`. For two
such choices on each side, the comparison equivalences `StacksDraft.DerivedModel.modelEquiv`
intertwine the two derived pullbacks, compatibly with the comparisons `Lf^* ⟶ f^*`; in particular
invertibility of a morphism `Lf^* φ`, vanishing of an object `Lf^* K`, and invertibility of the
comparison `Lf^* K ⟶ f^* K` do not depend on the models.

## Main definitions

* `StacksDraft.DerivedModel.derivedPullbackModelEquivIso`: `Lf^* ⋙ e_X ≅ e_Y ⋙ Lf^*` for two
  arbitrary pairs of models, `e` being `StacksDraft.DerivedModel.modelEquiv`.
* `StacksDraft.DerivedModel.derivedPullbackStandardModelEquivIso` and
  `StacksDraft.DerivedModel.schemeDerivedPullbackStandardModelEquivIso`: the comparison of the
  standard model with the locally small one, for ringed spaces and for schemes.

## Main results

* `StacksDraft.DerivedModel.leftDerivedModelIso_hom_app_fac`: the transport of a total left
  derived functor of `StacksDraft.DerivedModel.leftDerivedModelIso` is compatible with the two
  counits.
* `StacksDraft.DerivedModel.isIso_app_iff_of_isLeftDerivedFunctor`: the two counits are invertible
  at the same objects.
* `StacksDraft.DerivedModel.derivedPullbackModelEquivIso_hom_app_comp`,
  `StacksDraft.DerivedModel.isIso_derivedPullbackComparison_app_iff`,
  `StacksDraft.DerivedModel.isIso_derivedPullback_map_iff` and
  `StacksDraft.DerivedModel.isZero_derivedPullback_obj_iff`: the consequences for `Lf^*`.
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
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u v w₁ w₂ w₃ w₄

namespace StacksDraft.DerivedModel

/-! ### Transported left derived functors and their counits -/

section Derived

variable {K : Type u} [Category.{v} K] {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {E₁ : Type*} [Category* E₁] {E₂ : Type*} [Category* E₂]
  (W : MorphismProperty K)
  {L₁ : K ⥤ D₁} {L₂ : K ⥤ D₂} [L₁.IsLocalization W] [L₂.IsLocalization W]
  {G : D₁ ⥤ D₂} [G.IsEquivalence] {J : E₁ ⥤ E₂} [J.IsEquivalence]
  {F₁ : K ⥤ E₁} {LF₁ : D₁ ⥤ E₁} (α₁ : L₁ ⋙ LF₁ ⟶ F₁) [LF₁.IsLeftDerivedFunctor α₁ W]
  {F₂ : K ⥤ E₂} {LF₂ : D₂ ⥤ E₂} (α₂ : L₂ ⋙ LF₂ ⟶ F₂) [LF₂.IsLeftDerivedFunctor α₂ W]
  (hG : L₁ ⋙ G ≅ L₂) (hF : F₁ ⋙ J ≅ F₂)

/-- The transport `leftDerivedModelIso` of a total left derived functor carries the counit of
`LF₁` to the counit of `LF₂`. -/
theorem leftDerivedModelIso_hom_app_fac (X : K) :
    (leftDerivedModelIso W α₁ α₂ hG hF).hom.app (L₁.obj X) ≫ LF₂.map (hG.hom.app X) ≫
        α₂.app X =
      J.map (α₁.app X) ≫ hF.hom.app X := by
  have := isLeftDerivedFunctor_comp_isEquivalence W α₂ hG
  have h := Functor.leftDerivedNatTrans_app _ _
    ((Functor.associator L₁ LF₁ J).inv ≫ whiskerRight α₁ J) (transportLeftDerivedCounit α₂ hG) W
    hF.hom X
  simp only [transportLeftDerivedCounit, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp] at h
  exact h

include W hG hF in
/-- The counits of two left derived functors matched by `leftDerivedModelIso` are invertible at
the same objects. -/
theorem isIso_app_iff_of_isLeftDerivedFunctor (X : K) : IsIso (α₁.app X) ↔ IsIso (α₂.app X) := by
  rw [← isIso_iff_of_reflects_iso _ J, ← isIso_comp_right_iff _ (hF.hom.app X),
    ← leftDerivedModelIso_hom_app_fac W α₁ α₂ hG hF X, isIso_comp_left_iff,
    isIso_comp_left_iff]

end Derived

/-! ### The derived pullback of a morphism of ringed spaces at two pairs of models -/

section RingedSpaces

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (hX₁ : HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X)))
  (hX₂ : HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing X)))
  (hY₁ : HasDerivedCategory.{w₃} (SheafOfModules.{u} (structureSheafRing Y)))
  (hY₂ : HasDerivedCategory.{w₄} (SheafOfModules.{u} (structureSheafRing Y)))

/-- **The derived pullback at two pairs of models.** For a morphism of ringed spaces `f`, the
comparison equivalences of the models of `D(𝒪_X)` and of `D(𝒪_Y)` intertwine the two derived
pullbacks `Lf^*`. -/
def derivedPullbackModelEquivIso :
    @derivedPullback X Y f hX₁ hY₁ inferInstance ⋙ (modelEquiv hX₁ hX₂).functor ≅
      (modelEquiv hY₁ hY₂).functor ⋙ @derivedPullback X Y f hX₂ hY₂ inferInstance :=
  leftDerivedModelIso
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (@derivedPullbackComparison X Y f hX₁ hY₁ inferInstance)
    (@derivedPullbackComparison X Y f hX₂ hY₂ inferInstance)
    (Localization.compUniqFunctor _ _ _)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Localization.compUniqFunctor _ _ _))

/-- The comparison of the two models of `D(𝒪_X)`, transported along `f^*` on homotopy categories. -/
private abbrev derivedPullbackModelEquivCompIso :
    ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ @DerivedCategory.Qh _ _ _ hX₁) ⋙
        (modelEquiv hX₁ hX₂).functor ≅
      (modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ @DerivedCategory.Qh _ _ _ hX₂ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (Localization.compUniqFunctor _ _ (HomotopyCategory.subcategoryAcyclic _).trW)

/-- `derivedPullbackModelEquivIso` is compatible with the comparisons `Lf^* ⟶ f^*` at the two
pairs of models. -/
theorem derivedPullbackModelEquivIso_hom_app_comp
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    (derivedPullbackModelEquivIso f hX₁ hX₂ hY₁ hY₂).hom.app
        ((@DerivedCategory.Qh _ _ _ hY₁).obj M) ≫
      (@derivedPullback X Y f hX₂ hY₂ inferInstance).map
        ((Localization.compUniqFunctor (@DerivedCategory.Qh _ _ _ hY₁)
          (@DerivedCategory.Qh _ _ _ hY₂) (HomotopyCategory.subcategoryAcyclic _).trW).hom.app M) ≫
      (@derivedPullbackComparison X Y f hX₂ hY₂ inferInstance).app M =
    (modelEquiv hX₁ hX₂).functor.map
        ((@derivedPullbackComparison X Y f hX₁ hY₁ inferInstance).app M) ≫
      (Localization.compUniqFunctor (@DerivedCategory.Qh _ _ _ hX₁)
          (@DerivedCategory.Qh _ _ _ hX₂) (HomotopyCategory.subcategoryAcyclic _).trW).hom.app
        (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) := by
  have h := leftDerivedModelIso_hom_app_fac
    (HomotopyCategory.quasiIso _ _) (@derivedPullbackComparison X Y f hX₁ hY₁ inferInstance)
    (@derivedPullbackComparison X Y f hX₂ hY₂ inferInstance)
    (Localization.compUniqFunctor _ _ (HomotopyCategory.subcategoryAcyclic _).trW)
    (derivedPullbackModelEquivCompIso f hX₁ hX₂) M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp] at h
  exact h

/-- The comparison `Lf^* M ⟶ f^* M` is invertible at one model if and only if it is at any
other. -/
theorem isIso_derivedPullbackComparison_app_iff
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    IsIso ((@derivedPullbackComparison X Y f hX₁ hY₁ inferInstance).app M) ↔
      IsIso ((@derivedPullbackComparison X Y f hX₂ hY₂ inferInstance).app M) :=
  isIso_app_iff_of_isLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ _) (@derivedPullbackComparison X Y f hX₁ hY₁ inferInstance)
    (@derivedPullbackComparison X Y f hX₂ hY₂ inferInstance)
    (Localization.compUniqFunctor _ _ (HomotopyCategory.subcategoryAcyclic _).trW)
    (derivedPullbackModelEquivCompIso f hX₁ hX₂) M

/-- `Lf^*` at one pair of models inverts a morphism `φ` if and only if `Lf^*` at another pair
inverts the image of `φ` under the comparison equivalence. -/
theorem isIso_derivedPullback_map_iff
    {K L : @DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) _ _ hY₁} (φ : K ⟶ L) :
    IsIso ((@derivedPullback X Y f hX₁ hY₁ inferInstance).map φ) ↔
      IsIso ((@derivedPullback X Y f hX₂ hY₂ inferInstance).map
        ((modelEquiv hY₁ hY₂).functor.map φ)) :=
  isIso_map_iff_of_iso (derivedPullbackModelEquivIso f hX₁ hX₂ hY₁ hY₂) φ

/-- `Lf^* K` vanishes at one pair of models if and only if `Lf^*` of the image of `K` under the
comparison equivalence vanishes at another. -/
theorem isZero_derivedPullback_obj_iff
    (K : @DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) _ _ hY₁) :
    IsZero ((@derivedPullback X Y f hX₁ hY₁ inferInstance).obj K) ↔
      IsZero ((@derivedPullback X Y f hX₂ hY₂ inferInstance).obj
        ((modelEquiv hY₁ hY₂).functor.obj K)) :=
  isZero_obj_iff_of_iso (derivedPullbackModelEquivIso f hX₁ hX₂ hY₁ hY₂) K

/-- **The derived pullback at the standard and at the locally small model**, compared through
`SheafOfModules.derivedModelEquiv`. -/
abbrev derivedPullbackStandardModelEquivIso :
    @derivedPullback X Y f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
          inferInstance ⋙ (SheafOfModules.derivedModelEquiv (structureSheafRing X)).functor ≅
      (SheafOfModules.derivedModelEquiv (structureSheafRing Y)).functor ⋙
        @derivedPullback X Y f (SheafOfModules.hasDerivedCategory _)
          (SheafOfModules.hasDerivedCategory _) inferInstance :=
  derivedPullbackModelEquivIso f _ _ _ _

end RingedSpaces

/-- **The derived pullback of a morphism of schemes at the standard and at the locally small
model**, the latter being `Stacks.Duality.derivedPullback`, compared through
`AlgebraicGeometry.Scheme.Modules.derivedModelEquiv`. -/
abbrev schemeDerivedPullbackStandardModelEquivIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    @derivedPullback X.toRingedSpace Y.toRingedSpace f.toLRSHom.toShHom
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) inferInstance ⋙
        (Scheme.Modules.derivedModelEquiv X).functor ≅
      (Scheme.Modules.derivedModelEquiv Y).functor ⋙ Stacks.Duality.derivedPullback f :=
  derivedPullbackModelEquivIso f.toLRSHom.toShHom _ _ _ _

end StacksDraft.DerivedModel

end
