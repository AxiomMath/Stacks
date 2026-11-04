module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ModulePullbackSquareCubeSide
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleThickenedModulesRestrictIso
public import StacksFrontier.Deformation.ToposThickening.Helpers.IdealSquareCompatibleOfTranspose
public import StacksFrontier.Deformation.ToposThickening.Helpers.IsoConjugateMap

/-!
# The map of pulled-back ideals on the top of a cube of algebraic spaces

For a cube of algebraic spaces (top `j : W ⟶ X`, vertical `f₂ : W ⟶ T₂`, `f₁ : X ⟶ T₁`, bottom
`γ : T₂ ⟶ T₁`, with `j ≫ f₁ = k = f₂ ≫ γ`), modules `Fₖ` identified with `fₖ^*Nₖ` and a map
`κ : N₁ ⟶ γ_*N₂`, this file defines the map `F₁ ⟶ j_*F₂` of `κ`
(`AlgebraicGeometry.Space.cubeIdealTranspose`): the transpose under `f₁^* ⊣ f₁_*` of `κ` followed
by `γ_*` of the unit of `f₂` and `γ_*f₂_* ≅ f₁_*j_*` (Stacks 03LU), read through the
identifications. It also records the comparison `Ψ₀ ∘ f_* ≅ k_*` of the thickened direct images
for `f ≫ g = k`:
`AlgebraicGeometry.Space.restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_of_eq`.

These are the inputs of the ideal-square compatibility of the relative squares of `Coh_{X/B}`
(second proof of Stacks 08WA).

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section EBridge

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The pullbacks of modules along the two four-field readings of the morphism of small étale
ringed topoi of a morphism of algebraic spaces are equal. -/
theorem pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules =
      (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules :=
  congrArg (fun ψ : Stacks.Sheaves.RingedToposModules.RingedToposHom
    (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) ↦ ψ.pullbackModules)
      (smallEtaleRingedToposHom B S hS f).toModulesHom_eq_toRingedToposModulesHom

/-- `AlgebraicGeometry.Space.restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app`
for `f ≫ g = k`. -/
theorem restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_of_eq
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O)) :
    ((smallEtaleThickeningTargetOfEq f g k hk).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS f)).obj M)).hom ≫
      (structureRestrict (smallEtaleRingedToposHom B S hS k)).map
        ((smallEtaleThickenedModulesCompIso f g k hk).hom.app M) =
    (modulePushforwardCompIsoOfEq f g k hk).hom.app M := by
  subst hk
  exact (restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app f g M).trans
    (Category.comp_id _).symm

end EBridge

section Cube

variable {V W X T T₂ T₁ : AlgebraicSpaces B S hS} (i₂ : V ⟶ W) (j : W ⟶ X) (i₁ : V ⟶ X)
  (hi : i₂ ≫ j = i₁) (p : V ⟶ T) (f₂ : W ⟶ T₂) (f₁ : X ⟶ T₁) (t₂ : T ⟶ T₂) (γ : T₂ ⟶ T₁)
  (t₁ : T ⟶ T₁) (ht : t₂ ≫ γ = t₁) (k : W ⟶ T₁) (hk : j ≫ f₁ = k) (hk' : f₂ ≫ γ = k)
  (k₁ : V ⟶ T₁) (h₁ : i₁ ≫ f₁ = k₁) (h₁' : p ≫ t₁ = k₁) (k₂ : V ⟶ T₂) (h₂ : i₂ ≫ f₂ = k₂)
  (h₂' : p ≫ t₂ = k₂)
  {N₁ : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS T₁).O)}
  {N₂ : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS T₂).O)}
  (κ : N₁ ⟶ (smallEtaleRingedToposHom B S hS γ).pushforwardModules.obj N₂)
  {F₁ F'₁ : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)}
  (Z₁ : F₁ = F'₁)
  (ρ₁ : F'₁ ≅ (pullbackModules (smallEtaleRingedToposHom B S hS f₁).toRingedToposModulesHom).obj N₁)
  {F₂ F'₂ : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS W).O)}
  (Z₂ : F₂ = F'₂)
  (ρ₂ : F'₂ ≅ (pullbackModules (smallEtaleRingedToposHom B S hS f₂).toRingedToposModulesHom).obj N₂)

/-- **The map `F₁ ⟶ j_*F₂` of the top of the cube attached to `κ : N₁ ⟶ γ_*N₂`**, through the
identifications `ρₖ : Fₖ ≅ fₖ^*Nₖ`: `Deformation.ToposThickening.cubeTopTranspose` (the transpose
under `f₁^* ⊣ f₁_*` of `κ` followed by `γ_*` of the unit of `f₂` and `γ_*f₂_* ≅ f₁_*j_*`) read
through `ρ₁` and `j_*ρ₂⁻¹`, in the shape `CategoryTheory.isoConjugateMap`. -/
def cubeIdealTranspose : F₁ ⟶ (smallEtaleRingedToposHom B S hS j).pushforwardModules.obj F₂ :=
  isoConjugateMap (smallEtaleRingedToposHom B S hS j).pushforwardModules Z₁ ρ₁
    (congrArg (fun φ : Stacks.Sheaves.RingedToposModules.RingedToposHom
        (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS T₁) =>
          (pullbackModules φ).obj N₁)
      (smallEtaleRingedToposHom B S hS f₁).toModulesHom_eq_toRingedToposModulesHom.symm)
    (Deformation.ToposThickening.cubeTopTranspose (spaceModuleAdj f₁) (spaceModuleAdj f₂)
      (modulePushforwardCompIsoOfEq j f₁ k hk) (modulePushforwardCompIsoOfEq f₂ γ k hk') κ)
    (congrArg (fun φ : Stacks.Sheaves.RingedToposModules.RingedToposHom
        (smallEtaleRingedTopos B S hS W) (smallEtaleRingedTopos B S hS T₂) =>
          (pullbackModules φ).obj N₂)
      (smallEtaleRingedToposHom B S hS f₂).toModulesHom_eq_toRingedToposModulesHom) ρ₂ Z₂

end Cube

section Spelling

variable {U U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (h : U ⟶ U')
  (hiso : IsIso (Subfunctor.toRange (representedSpaceMap B S hS h).hom))
  (hfo : IsFirstOrderThickening B S hS ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩
    (Subfunctor.range (representedSpaceMap B S hS h).hom))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- `AlgebraicGeometry.Space.representedThickeningIdealPullbackSpellingIso` is the
identification of the objects given by
`AlgebraicGeometry.Space.pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom`.
-/
theorem representedThickeningIdealPullbackSpellingIso_hom_eq :
    (representedThickeningIdealPullbackSpellingIso h hiso hfo).hom =
      eqToHom (congrArg (fun F => F.obj (affineThickeningIdeal h hiso hfo).I)
        (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom
          (representedSpaceMap B S hS h))).symm :=
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- The inverse of `AlgebraicGeometry.Space.representedThickeningIdealPullbackSpellingIso` is the
identification of the objects given by
`AlgebraicGeometry.Space.pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom`.
-/
theorem representedThickeningIdealPullbackSpellingIso_inv_eq :
    (representedThickeningIdealPullbackSpellingIso h hiso hfo).inv =
      eqToHom (congrArg (fun F => F.obj (affineThickeningIdeal h hiso hfo).I)
        (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom
          (representedSpaceMap B S hS h))) :=
  rfl

end Spelling

section IdealMapMate

variable {U U'₁ U'₂ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₁)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₂)]
  (h₁ : U ⟶ U'₁) (h₂ : U ⟶ U'₂) (g : U'₂ ⟶ U'₁) (hg : h₂ ≫ g = h₁)
  (hiso₁ : IsIso (Subfunctor.toRange ((schemeSpaceFunctor B S hS).map h₁).hom))
  (hfo₁ : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj U'₁)
    (Subfunctor.range ((schemeSpaceFunctor B S hS).map h₁).hom))
  (hiso₂ : IsIso (Subfunctor.toRange ((schemeSpaceFunctor B S hS).map h₂).hom))
  (hfo₂ : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj U'₂)
    (Subfunctor.range ((schemeSpaceFunctor B S hS).map h₂).hom))
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂))

/-- `AlgebraicGeometry.Space.homEquiv_thickeningIdealMap` through the adjunctions
`AlgebraicGeometry.Space.spaceModuleAdj`, with their instance terms. -/
theorem homEquiv_spaceModuleAdj_thickeningIdealMap :
    (spaceModuleAdj (representedSpaceMap B S hS h₁)).homEquiv _ _
        ((representedThickeningIdealPullbackSpellingIso h₁ hiso₁ hfo₁).inv ≫
        thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂ ≫
        (representedThickeningIdealPullbackSpellingIso h₂ hiso₂ hfo₂).hom) =
      thickeningIdealPushforwardMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ ≫
        (RingedToposHom.pushforwardModules
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g))).map
          ((spaceModuleAdj (representedSpaceMap B S hS h₂)).unit.app
            (affineThickeningIdeal h₂ hiso₂ hfo₂).I) ≫
        (modulePushforwardCompIsoOfEq (representedSpaceMap B S hS h₂)
          (representedSpaceMap B S hS g) (representedSpaceMap B S hS h₁)
          ((representedSpaceMap_comp B S hS h₂ g).trans
          (congrArg (representedSpaceMap B S hS) hg))).hom.app _ :=
  homEquiv_thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂

end IdealMapMate

end AlgebraicGeometry.Space
