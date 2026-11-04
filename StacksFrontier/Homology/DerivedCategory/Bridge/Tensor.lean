module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorModelTransport
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic

/-!
# The derived tensor product along the comparison of two models

For two models `h₁`, `h₂` of the derived category of sheaves of modules on a ringed site, the
comparison equivalence `e = StacksDraft.DerivedModel.modelEquiv h₁ h₂` carries the derived tensor
product of [Stacks, Tag 06YU] at `h₁` to the one at `h₂`: `e (K ⊗^L L) ≅ e K ⊗^L e L`, naturally
in `K` and `L`. Consequently vanishing of a derived tensor product, and invertibility of the
derived tensor product of a morphism with an object, can be tested in either model.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelEquivIso`

## Main results

* `Stacks.DerivedTensor.RingedSite.isZero_derivedTensorProductFunctor_modelEquiv_iff`
* `Stacks.DerivedTensor.RingedSite.isIso_derivedTensorProductFunctor_map_app_modelEquiv_iff`
* `Stacks.DerivedTensor.RingedSite.isIso_derivedTensorProductFunctor_obj_map_modelEquiv_iff`

Each is also specialized to the comparisons `SheafOfModules.derivedModelEquiv` and
`AlgebraicGeometry.Scheme.Modules.derivedModelEquiv` of the standard model with the locally small
ones `SheafOfModules.hasDerivedCategory` and `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

## Implementation notes

The comparison is `StacksDraft.DerivedModel.derivedTensorModelIso` at the comparison equivalence
and the canonical derived tensor product at both models: both sides descend the total tensor
product of K-flat complexes, so they agree by the universal property of the localization.

For a scheme the derived tensor product at `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`
is written at `SheafOfModules.hasDerivedCategory` of the ringed-site spelling `Modules X.sheaf` of
`X.Modules`: the two instances are equal by `rfl`, but only the second elaborates there.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StacksDraft.DerivedModel

universe d₁ d₂ u

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (h₁ : HasDerivedCategory.{d₁} (Modules R)) (h₂ : HasDerivedCategory.{d₂} (Modules R))

/-- **The derived tensor product along the comparison of two models**: `e (K ⊗^L L)` is
`e K ⊗^L e L`, naturally in `K` and `L`, for `e` the comparison equivalence. -/
def derivedTensorProductFunctorModelEquivIso :
    @derivedTensorProductFunctor _ _ _ R _ _ h₁ _ _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj (modelEquiv h₁ h₂).functor ≅
      (modelEquiv h₁ h₂).functor ⋙ @derivedTensorProductFunctor _ _ _ R _ _ h₂ _ _ _ ⋙
        (Functor.whiskeringLeft _ _ _).obj (modelEquiv h₁ h₂).functor :=
  derivedTensorModelIso R h₁ h₂ (modelEquiv h₁ h₂).functor (modelCompQIso h₁ h₂)
    (@canonicalDerivedTensorProduct _ _ _ R _ _ h₁ _ _ _)
    (@canonicalDerivedTensorProduct _ _ _ R _ _ h₂ _ _ _)

variable {R h₁ h₂}

/-- A derived tensor product vanishes in one model if and only if the derived tensor product of
the images vanishes in the other. -/
theorem isZero_derivedTensorProductFunctor_modelEquiv_iff
    (K L : @DerivedCategory (Modules R) _ _ h₁) :
    IsZero (((@derivedTensorProductFunctor _ _ _ R _ _ h₁ _ _ _).obj K).obj L) ↔
      IsZero (((@derivedTensorProductFunctor _ _ _ R _ _ h₂ _ _ _).obj
        ((modelEquiv h₁ h₂).functor.obj K)).obj ((modelEquiv h₁ h₂).functor.obj L)) :=
  (isZero_modelEquiv_functor_obj_iff h₁ h₂ _).symm.trans
    (((derivedTensorProductFunctorModelEquivIso R h₁ h₂).app K).app L).isZero_iff

/-- `f ⊗^L L` is invertible in one model if and only if `e f ⊗^L e L` is in the other. -/
theorem isIso_derivedTensorProductFunctor_map_app_modelEquiv_iff
    {K K' : @DerivedCategory (Modules R) _ _ h₁} (f : K ⟶ K')
    (L : @DerivedCategory (Modules R) _ _ h₁) :
    IsIso (((@derivedTensorProductFunctor _ _ _ R _ _ h₁ _ _ _).map f).app L) ↔
      IsIso (((@derivedTensorProductFunctor _ _ _ R _ _ h₂ _ _ _).map
        ((modelEquiv h₁ h₂).functor.map f)).app ((modelEquiv h₁ h₂).functor.obj L)) :=
  (isIso_modelEquiv_functor_map_iff h₁ h₂ _).symm.trans
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight
      (derivedTensorProductFunctorModelEquivIso R h₁ h₂) ((evaluation _ _).obj L)) f)

/-- `K ⊗^L g` is invertible in one model if and only if `e K ⊗^L e g` is in the other. -/
theorem isIso_derivedTensorProductFunctor_obj_map_modelEquiv_iff
    (K : @DerivedCategory (Modules R) _ _ h₁) {L L' : @DerivedCategory (Modules R) _ _ h₁}
    (g : L ⟶ L') :
    IsIso (((@derivedTensorProductFunctor _ _ _ R _ _ h₁ _ _ _).obj K).map g) ↔
      IsIso (((@derivedTensorProductFunctor _ _ _ R _ _ h₂ _ _ _).obj
        ((modelEquiv h₁ h₂).functor.obj K)).map ((modelEquiv h₁ h₂).functor.map g)) :=
  (isIso_modelEquiv_functor_map_iff h₁ h₂ _).symm.trans
    (NatIso.isIso_map_iff ((derivedTensorProductFunctorModelEquivIso R h₁ h₂).app K) g)

/-! ### The standard and the locally small model -/

section LocallySmall

variable (R) in
/-- The derived tensor product at the standard model, carried to the locally small model
`SheafOfModules.hasDerivedCategory`: `e (K ⊗^L L) ≅ e K ⊗^L e L`. -/
abbrev derivedTensorProductFunctorStandardIso :
    @derivedTensorProductFunctor _ _ _ R _ _ (HasDerivedCategory.standard _) _ _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (SheafOfModules.derivedModelEquiv _).functor ≅
      (SheafOfModules.derivedModelEquiv _).functor ⋙
        @derivedTensorProductFunctor _ _ _ R _ _ (SheafOfModules.hasDerivedCategory _) _ _ _ ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (SheafOfModules.derivedModelEquiv _).functor :=
  derivedTensorProductFunctorModelEquivIso R _ _

/-- A derived tensor product at the standard model vanishes if and only if the derived tensor
product of the images at the locally small model does. -/
theorem isZero_derivedTensorProductFunctor_standard_iff
    (K L : @DerivedCategory (Modules R) _ _ (HasDerivedCategory.standard _)) :
    IsZero (((@derivedTensorProductFunctor _ _ _ R _ _ (HasDerivedCategory.standard _)
        _ _ _).obj K).obj L) ↔
      IsZero (((@derivedTensorProductFunctor _ _ _ R _ _ (SheafOfModules.hasDerivedCategory _)
        _ _ _).obj
        ((SheafOfModules.derivedModelEquiv _).functor.obj K)).obj
          ((SheafOfModules.derivedModelEquiv _).functor.obj L)) :=
  isZero_derivedTensorProductFunctor_modelEquiv_iff K L

/-- `f ⊗^L L` is invertible at the standard model if and only if `e f ⊗^L e L` is invertible at
the locally small model. -/
theorem isIso_derivedTensorProductFunctor_map_app_standard_iff
    {K K' : @DerivedCategory (Modules R) _ _ (HasDerivedCategory.standard _)} (f : K ⟶ K')
    (L : @DerivedCategory (Modules R) _ _ (HasDerivedCategory.standard _)) :
    IsIso (((@derivedTensorProductFunctor _ _ _ R _ _ (HasDerivedCategory.standard _)
        _ _ _).map f).app L) ↔
      IsIso (((@derivedTensorProductFunctor _ _ _ R _ _ (SheafOfModules.hasDerivedCategory _)
        _ _ _).map
        ((SheafOfModules.derivedModelEquiv _).functor.map f)).app
          ((SheafOfModules.derivedModelEquiv _).functor.obj L)) :=
  isIso_derivedTensorProductFunctor_map_app_modelEquiv_iff f L

/-- `K ⊗^L g` is invertible at the standard model if and only if `e K ⊗^L e g` is invertible at
the locally small model. -/
theorem isIso_derivedTensorProductFunctor_obj_map_standard_iff
    (K : @DerivedCategory (Modules R) _ _ (HasDerivedCategory.standard _))
    {L L' : @DerivedCategory (Modules R) _ _ (HasDerivedCategory.standard _)} (g : L ⟶ L') :
    IsIso (((@derivedTensorProductFunctor _ _ _ R _ _ (HasDerivedCategory.standard _)
        _ _ _).obj K).map g) ↔
      IsIso (((@derivedTensorProductFunctor _ _ _ R _ _ (SheafOfModules.hasDerivedCategory _)
        _ _ _).obj
        ((SheafOfModules.derivedModelEquiv _).functor.obj K)).map
          ((SheafOfModules.derivedModelEquiv _).functor.map g)) :=
  isIso_derivedTensorProductFunctor_obj_map_modelEquiv_iff K g

end LocallySmall

end Stacks.DerivedTensor.RingedSite

/-! ### Schemes -/

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.DerivedTensor.RingedSite Stacks.Topology.SheafTensorAdditiveOnOpens

variable (X : Scheme.{u})

/-- For a scheme `X`, the derived tensor product of `D(𝒪_X)` at the standard model, carried to
the model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`: `e (K ⊗^L L) ≅ e K ⊗^L e L`. -/
abbrev derivedTensorProductFunctorStandardIso :
    @derivedTensorProductFunctor _ _ _ X.sheaf _ _ (HasDerivedCategory.standard _) _ _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj (derivedModelEquiv X).functor ≅
      (derivedModelEquiv X).functor ⋙
        @derivedTensorProductFunctor _ _ _ X.sheaf _ _ (SheafOfModules.hasDerivedCategory _)
          _ _ _ ⋙
        (Functor.whiskeringLeft _ _ _).obj (derivedModelEquiv X).functor :=
  derivedTensorProductFunctorModelEquivIso X.sheaf _ _

variable {X}

/-- A derived tensor product in `D(𝒪_X)` at the standard model vanishes if and only if the derived
tensor product of the images at `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` does. -/
theorem isZero_derivedTensorProductFunctor_standard_iff
    (K L : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) :
    IsZero (((@derivedTensorProductFunctor _ _ _ X.sheaf _ _ (HasDerivedCategory.standard _)
        _ _ _).obj K).obj L) ↔
      IsZero (((@derivedTensorProductFunctor _ _ _ X.sheaf _ _
        (SheafOfModules.hasDerivedCategory _)
        _ _ _).obj ((derivedModelEquiv X).functor.obj K)).obj
          ((derivedModelEquiv X).functor.obj L)) :=
  isZero_derivedTensorProductFunctor_modelEquiv_iff K L

/-- `f ⊗^L L` in `D(𝒪_X)` is invertible at the standard model if and only if `e f ⊗^L e L` is
invertible at `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. -/
theorem isIso_derivedTensorProductFunctor_map_app_standard_iff
    {K K' : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)} (f : K ⟶ K')
    (L : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) :
    IsIso (((@derivedTensorProductFunctor _ _ _ X.sheaf _ _ (HasDerivedCategory.standard _)
        _ _ _).map f).app L) ↔
      IsIso (((@derivedTensorProductFunctor _ _ _ X.sheaf _ _
        (SheafOfModules.hasDerivedCategory _)
        _ _ _).map ((derivedModelEquiv X).functor.map f)).app
          ((derivedModelEquiv X).functor.obj L)) :=
  isIso_derivedTensorProductFunctor_map_app_modelEquiv_iff f L

/-- `K ⊗^L g` in `D(𝒪_X)` is invertible at the standard model if and only if `e K ⊗^L e g` is
invertible at `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. -/
theorem isIso_derivedTensorProductFunctor_obj_map_standard_iff
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    {L L' : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)} (g : L ⟶ L') :
    IsIso (((@derivedTensorProductFunctor _ _ _ X.sheaf _ _ (HasDerivedCategory.standard _)
        _ _ _).obj K).map g) ↔
      IsIso (((@derivedTensorProductFunctor _ _ _ X.sheaf _ _
        (SheafOfModules.hasDerivedCategory _)
        _ _ _).obj ((derivedModelEquiv X).functor.obj K)).map
          ((derivedModelEquiv X).functor.map g)) :=
  isIso_derivedTensorProductFunctor_obj_map_modelEquiv_iff K g

end AlgebraicGeometry.Scheme.Modules

end
