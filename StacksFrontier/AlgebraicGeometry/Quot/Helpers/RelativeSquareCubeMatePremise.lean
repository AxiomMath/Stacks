module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ModulePullbackSquareCubeSideRelativeSquare
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeSquareThickeningIdealMapMate
public import StacksFrontier.Deformation.ToposThickening.Helpers.IdealSquareCompatibleOfCube

/-!
# The mate hypothesis of the cube comparison, from the mate identity in its own spelling

The hypothesis `hlam` of
`AlgebraicGeometry.Space.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj`
(the mate identity `t₁^♭(s₁ ≫ λ ≫ s₂) = κ ≫ γ_*(η) ≫ (γ_*t₂_* ≅ t₁_*)` on the bottom of the cube)
is the statement of
`AlgebraicGeometry.Space.CoherentSituation.relativeSquare_homEquiv_thickeningIdealMap` at the cube
of the relative squares, but the two are not compared cheaply: the spaces, morphisms,
ideals and maps of the latter are spelled through the test schemes as they are elaborated there.
`AlgebraicGeometry.Space.premise_homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj`
gives that hypothesis for an arbitrary cube of algebraic spaces from the mate identity for data
equal to the bottom face of the cube, each identification a separate hypothesis, by substitution;
it is instantiated once, at the relative squares, in `CoherentStackRelativeIdealSquareReduction`.

This is used in the functoriality of the obstruction classes of `Coh_{X/B}` (second proof of
Stacks 08WA). This module is a helper and carries no `@[stacks]` attribute.

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
  {V W X T T₂ T₁ : AlgebraicSpaces B S hS} (i₂ : V ⟶ W) (j : W ⟶ X) (i₁ : V ⟶ X)
  (hi : i₂ ≫ j = i₁) (p : V ⟶ T) (f₂ : W ⟶ T₂) (f₁ : X ⟶ T₁) (t₂ : T ⟶ T₂) (γ : T₂ ⟶ T₁)
  (t₁ : T ⟶ T₁) (ht : t₂ ≫ γ = t₁) (k : W ⟶ T₁) (hk : j ≫ f₁ = k) (hk' : f₂ ≫ γ = k)
  (k₁ : V ⟶ T₁) (h₁ : i₁ ≫ f₁ = k₁) (h₁' : p ≫ t₁ = k₁) (k₂ : V ⟶ T₂) (h₂ : i₂ ≫ f₂ = k₂)
  (h₂' : p ≫ t₂ = k₂)

/-- **The mate hypothesis of the cube comparison at the adjunctions
`AlgebraicGeometry.Space.spaceModuleAdj`, from the mate identity for equal data.** For a
commutative cube of algebraic spaces with bottom face `t₂ ≫ γ = t₁`, modules `N₁`, `N₂`, a map
`κ : N₁ ⟶ γ_*N₂` and a map `λ : t₁^*N₁ ⟶ t₂^*N₂` of inverse images in the four-field reading, the
hypothesis `hlam` of
`AlgebraicGeometry.Space.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj` holds as
soon as `λ`, read through the two spellings of the inverse images, corresponds under
`t₁^* ⊣ t₁_*` to `κ ≫ γ_*(η) ≫ (γ_*t₂_* ≅ t₁_*)` for data `t'ₖ`, `γ'`, `N'ₖ`, `κ'`, `λ'` equal to
these (heterogeneously), with the comparison `AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq`
for any proof of `t'₂ ≫ γ' = t'₁`. -/
theorem premise_homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj
    (N₁ : spaceModules T₁) (N₂ : spaceModules T₂)
    (κ : N₁ ⟶ (smallEtaleRingedToposHom B S hS γ).pushforwardModules.obj N₂)
    (lam : (smallEtaleRingedToposHom B S hS t₁).toRingedToposModulesHom.pullbackModules.obj N₁ ⟶
      (smallEtaleRingedToposHom B S hS t₂).toRingedToposModulesHom.pullbackModules.obj N₂)
    {T' T₁' T₂' : AlgebraicSpaces B S hS} {t₁' : T' ⟶ T₁'} {t₂' : T' ⟶ T₂'} {γ' : T₂' ⟶ T₁'}
    {ht' : t₂' ≫ γ' = t₁'} {N₁' : spaceModules T₁'} {N₂' : spaceModules T₂'}
    {κ' : N₁' ⟶ (smallEtaleRingedToposHom B S hS γ').pushforwardModules.obj N₂'}
    {lam' : (smallEtaleRingedToposHom B S hS t₁').toRingedToposModulesHom.pullbackModules.obj N₁' ⟶
      (smallEtaleRingedToposHom B S hS t₂').toRingedToposModulesHom.pullbackModules.obj N₂'}
    (H : (spaceModuleAdj t₁').homEquiv _ _
        (eqToHom (congrArg (fun F => F.obj N₁')
          (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom t₁')) ≫
        CategoryStruct.comp
          (X := (smallEtaleRingedToposHom B S hS t₁').toRingedToposModulesHom.pullbackModules.obj
            N₁')
          (Y := (smallEtaleRingedToposHom B S hS t₂').toRingedToposModulesHom.pullbackModules.obj
            N₂')
          lam'
          (eqToHom (congrArg (fun F => F.obj N₂')
            (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom t₂')).symm)) =
      CategoryStruct.comp
        (Y := (smallEtaleRingedToposHom B S hS γ').pushforwardModules.obj N₂')
        κ'
        ((smallEtaleRingedToposHom B S hS γ').pushforwardModules.map
          ((spaceModuleAdj t₂').unit.app N₂') ≫
        (modulePushforwardCompIsoOfEq t₂' γ' t₁' ht').hom.app _))
    (eT : T' = T) (eT₁ : T₁' = T₁) (eT₂ : T₂' = T₂) (e₁ : t₁' ≍ t₁) (e₂ : t₂' ≍ t₂)
    (eγ : γ' ≍ γ) (eN₁ : N₁' ≍ N₁) (eN₂ : N₂' ≍ N₂) (eκ : κ' ≍ κ) (elam : lam' ≍ lam) :
    premise (homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj i₂ j i₁ hi p f₂ f₁ t₂
      γ t₁ ht k hk hk' k₁ h₁ h₁' k₂ h₂ h₂' N₁ N₂ κ lam _ rfl _ rfl _ rfl) := by
  unfold premise
  exact homEquiv_spaceModuleAdj_eq_comp_map_unit_comp_of_heq eT eT₁ eT₂ ht' ht e₁ e₂ eγ eN₁ eN₂ eκ
    elam rfl rfl rfl rfl H

end AlgebraicGeometry.Space

end
