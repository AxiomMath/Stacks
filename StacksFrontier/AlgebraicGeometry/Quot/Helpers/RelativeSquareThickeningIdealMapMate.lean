module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquare

/-!
# `λ_g` as the mate of `κ_g`, in the spelling of the cube of the relative squares

`AlgebraicGeometry.Space.homEquiv_spaceModuleAdj_thickeningIdealMap` says that the map of
pulled-back ideals `λ_g : t₁^*𝒥₁ ⟶ t₂^*𝒥₂` of a morphism `g : U'₂ ⟶ U'₁` of affine first order
thickenings of `U` corresponds under `t₁^* ⊣ t₁_*` to `κ_g ≫ g_*(η) ≫ (g_*t₂_* ≅ t₁_*)`. It is
written with the represented spaces (`AlgebraicGeometry.Space.representedSpaceMap`), whereas the
cube of the relative squares of `Coh_{X/B}` (`AlgebraicGeometry.Space.cubeIdealTranspose` at
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealTranspose`) has its bottom face
written with `AlgebraicGeometry.schemeSpaceFunctor`. This file restates the identity in the
spelling of the cube, which is the hypothesis `hlam` of
`Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq`
(`AlgebraicGeometry.Space.homEquiv_spaceModuleAdj_schemeSpaceFunctor_thickeningIdealMap`, and at
the relative squares
`AlgebraicGeometry.Space.CoherentSituation.relativeSquare_homEquiv_thickeningIdealMap`).

The two spellings are definitionally equal, but a definitional check between them under the
projections `Adjunction.unit`, `Iso.hom`, `NatTrans.app` or a composition unfolds the morphisms of
small étale ringed topoi and is very slow. So the identity is transported once, for variable
algebraic spaces, morphisms, modules and maps given with their identifications
(`AlgebraicGeometry.Space.homEquiv_spaceModuleAdj_eq_comp_map_unit_comp_of_heq`, proved by
substitution), and the identifications are checked one at a time outside any projection.

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

/-- **The mate identity of a map of pulled-back modules, transported along equal data.** Let
`t₁ : T ⟶ T₁`, `t₂ : T ⟶ T₂`, `γ : T₂ ⟶ T₁` with `t₂ ≫ γ = t₁`, `κ : N₁ ⟶ γ_*N₂` and
`λ : t₁^*N₁ ⟶ t₂^*N₂` (inverse images in the four-field reading of
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`) satisfy: `λ`, read through the two
spellings of the inverse images, corresponds under `t₁^* ⊣ t₁_*` to
`κ ≫ γ_*(η) ≫ (γ_*t₂_* ≅ t₁_*)`, the comparison being given as `c`. Then the same holds for data
`t'ₖ`, `γ'`, `N'ₖ`, `κ'`, `λ'` heterogeneously equal to these, with the comparison
`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq` for any proof of `t'₂ ≫ γ' = t'₁`. -/
theorem homEquiv_spaceModuleAdj_eq_comp_map_unit_comp_of_heq
    {T T₁ T₂ T' T₁' T₂' : AlgebraicSpaces B S hS} (eT : T = T') (eT₁ : T₁ = T₁')
    (eT₂ : T₂ = T₂') {t₁ : T ⟶ T₁} {t₂ : T ⟶ T₂} {γ : T₂ ⟶ T₁} (ht : t₂ ≫ γ = t₁)
    {t₁' : T' ⟶ T₁'} {t₂' : T' ⟶ T₂'} {γ' : T₂' ⟶ T₁'} (ht' : t₂' ≫ γ' = t₁')
    (e₁ : t₁ ≍ t₁') (e₂ : t₂ ≍ t₂') (eγ : γ ≍ γ')
    {N₁ : spaceModules T₁} {N₂ : spaceModules T₂} {N₁' : spaceModules T₁'} {N₂' : spaceModules T₂'}
    (eN₁ : N₁ ≍ N₁') (eN₂ : N₂ ≍ N₂')
    {κ : N₁ ⟶ (smallEtaleRingedToposHom B S hS γ).pushforwardModules.obj N₂}
    {κ' : N₁' ⟶ (smallEtaleRingedToposHom B S hS γ').pushforwardModules.obj N₂'} (hκ : κ ≍ κ')
    {lam : (smallEtaleRingedToposHom B S hS t₁).toRingedToposModulesHom.pullbackModules.obj N₁ ⟶
      (smallEtaleRingedToposHom B S hS t₂).toRingedToposModulesHom.pullbackModules.obj N₂}
    {lam' : (smallEtaleRingedToposHom B S hS t₁').toRingedToposModulesHom.pullbackModules.obj N₁' ⟶
      (smallEtaleRingedToposHom B S hS t₂').toRingedToposModulesHom.pullbackModules.obj N₂'}
    (hlam : lam ≍ lam')
    {s₁ : (smallEtaleRingedToposHom B S hS t₁).toModulesHom.pullbackModules.obj N₁ ⟶
      (smallEtaleRingedToposHom B S hS t₁).toRingedToposModulesHom.pullbackModules.obj N₁}
    (hs₁ : s₁ = eqToHom (congrArg (fun F => F.obj N₁)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom t₁)))
    {s₂ : (smallEtaleRingedToposHom B S hS t₂).toRingedToposModulesHom.pullbackModules.obj N₂ ⟶
      (smallEtaleRingedToposHom B S hS t₂).toModulesHom.pullbackModules.obj N₂}
    (hs₂ : s₂ = eqToHom (congrArg (fun F => F.obj N₂)
      (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom t₂)).symm)
    {c : (smallEtaleRingedToposHom B S hS t₂).pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS γ).pushforwardModules ≅
      (smallEtaleRingedToposHom B S hS t₁).pushforwardModules}
    (hc : c = modulePushforwardCompIsoOfEq t₂ γ t₁ ht)
    {r : (smallEtaleRingedToposHom B S hS t₁).toRingedToposModulesHom.pullbackModules.obj N₁ ⟶
      (smallEtaleRingedToposHom B S hS t₂).toModulesHom.pullbackModules.obj N₂}
    (hr : r = lam ≫ s₂)
    (H : (spaceModuleAdj t₁).homEquiv _ _ (s₁ ≫ r) =
      κ ≫ (smallEtaleRingedToposHom B S hS γ).pushforwardModules.map
          ((spaceModuleAdj t₂).unit.app N₂) ≫ c.hom.app _) :
    (spaceModuleAdj t₁').homEquiv _ _
        (eqToHom (congrArg (fun F => F.obj N₁')
          (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom t₁')) ≫ lam' ≫
        eqToHom (congrArg (fun F => F.obj N₂')
          (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom t₂')).symm) =
      κ' ≫ (smallEtaleRingedToposHom B S hS γ').pushforwardModules.map
          ((spaceModuleAdj t₂').unit.app N₂') ≫
        (modulePushforwardCompIsoOfEq t₂' γ' t₁' ht').hom.app _ := by
  subst eT eT₁ eT₂
  cases e₁
  cases e₂
  cases eγ
  cases eN₁
  cases eN₂
  cases hκ
  cases hlam
  subst hr hs₁ hs₂
  obtain rfl : c = modulePushforwardCompIsoOfEq t₂ γ t₁ ht' := hc
  exact H

section Spelling

variable {U U' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (h : U ⟶ U')
  (hiso : IsIso (Subfunctor.toRange ((schemeSpaceFunctor B S hS).map h).hom))
  (hfo : IsFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).obj U')
    (Subfunctor.range ((schemeSpaceFunctor B S hS).map h).hom))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- The pulled-back ideal `t^*𝒥` of a first order thickening `t : U ⟶ U'`, in the spelling of
`AlgebraicGeometry.schemeSpaceFunctor` (the source of
`AlgebraicGeometry.Space.thickeningIdealMap`), is the one in the spelling of the represented
spaces. -/
theorem pullbackModules_obj_idealOfThickening_schemeSpaceFunctor_eq :
    (smallEtaleRingedToposHom B S hS
        ((schemeSpaceFunctor B S hS).map h)).toRingedToposModulesHom.pullbackModules.obj
        (smallEtaleRingedToposHomFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map h)
          hiso hfo).idealOfThickening.I =
      (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS h)).toRingedToposModulesHom.pullbackModules.obj
        (affineThickeningIdeal h hiso hfo).I :=
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

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₁)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'₂)] in
/-- `κ_g : 𝒥₁ ⟶ g_*𝒥₂` (`AlgebraicGeometry.Space.thickeningIdealPushforwardMap`), with `g_*` in
the spelling of the represented spaces and in that of `AlgebraicGeometry.schemeSpaceFunctor`. -/
theorem thickeningIdealPushforwardMap_heq_schemeSpaceFunctor :
    @HEq ((affineThickeningIdeal h₁ hiso₁ hfo₁).I ⟶
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).pushforwardModules.obj
          (affineThickeningIdeal h₂ hiso₂ hfo₂).I)
      (thickeningIdealPushforwardMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂)
      (((affineThickeningIdeal h₁ hiso₁ hfo₁).I :
          spaceModules ((schemeSpaceFunctor B S hS).obj U'₁)) ⟶
        (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map g)).pushforwardModules.obj
          (affineThickeningIdeal h₂ hiso₂ hfo₂).I)
      (thickeningIdealPushforwardMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂) :=
  HEq.rfl

/-- `λ_g : t₁^*𝒥₁ ⟶ t₂^*𝒥₂` (`AlgebraicGeometry.Space.thickeningIdealMap`), with `tₖ^*𝒥ₖ` in the
spelling of the represented spaces and in that of `AlgebraicGeometry.schemeSpaceFunctor`. -/
theorem thickeningIdealMap_heq_representedSpaceMap :
    @HEq ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h₁)).toRingedToposModulesHom.pullbackModules.obj
          (affineThickeningIdeal h₁ hiso₁ hfo₁).I ⟶
        (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS h₂)).toRingedToposModulesHom.pullbackModules.obj
          (affineThickeningIdeal h₂ hiso₂ hfo₂).I)
      (thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂)
      ((smallEtaleRingedToposHom B S hS
          ((schemeSpaceFunctor B S hS).map h₁)).toRingedToposModulesHom.pullbackModules.obj
          (affineThickeningIdeal h₁ hiso₁ hfo₁).I ⟶
        (smallEtaleRingedToposHom B S hS
          ((schemeSpaceFunctor B S hS).map h₂)).toRingedToposModulesHom.pullbackModules.obj
          (affineThickeningIdeal h₂ hiso₂ hfo₂).I)
      (thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂) :=
  HEq.rfl

/-- **`λ_g` is the mate of `κ_g`, in the spelling of `AlgebraicGeometry.schemeSpaceFunctor`.**
`AlgebraicGeometry.Space.homEquiv_spaceModuleAdj_thickeningIdealMap` for the morphisms
`(schemeSpaceFunctor B S hS).map hₖ`, `(schemeSpaceFunctor B S hS).map g` of algebraic spaces,
with `λ_g` read through the identifications
`AlgebraicGeometry.Space.pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom`
of the inverse images and `g_*t₂_* ≅ t₁_*` for any proof `ht` of the commutativity: the
hypothesis `hlam` of `Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq`
for the adjunctions `AlgebraicGeometry.Space.spaceModuleAdj`. -/
theorem homEquiv_spaceModuleAdj_schemeSpaceFunctor_thickeningIdealMap
    (ht : (schemeSpaceFunctor B S hS).map h₂ ≫ (schemeSpaceFunctor B S hS).map g =
      (schemeSpaceFunctor B S hS).map h₁) :
    (spaceModuleAdj ((schemeSpaceFunctor B S hS).map h₁)).homEquiv _ _
        (eqToHom (congrArg (fun F => F.obj (affineThickeningIdeal h₁ hiso₁ hfo₁).I)
          (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom
            ((schemeSpaceFunctor B S hS).map h₁))) ≫
        CategoryStruct.comp
          (X := (smallEtaleRingedToposHom B S hS
            ((schemeSpaceFunctor B S hS).map h₁)).toRingedToposModulesHom.pullbackModules.obj
            (affineThickeningIdeal h₁ hiso₁ hfo₁).I)
          (Y := (smallEtaleRingedToposHom B S hS
            ((schemeSpaceFunctor B S hS).map h₂)).toRingedToposModulesHom.pullbackModules.obj
            (affineThickeningIdeal h₂ hiso₂ hfo₂).I)
          (thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂)
          (eqToHom (congrArg (fun F => F.obj (affineThickeningIdeal h₂ hiso₂ hfo₂).I)
            (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom
              ((schemeSpaceFunctor B S hS).map h₂))).symm)) =
      CategoryStruct.comp
        (Y := (smallEtaleRingedToposHom B S hS
          ((schemeSpaceFunctor B S hS).map g)).pushforwardModules.obj
          (affineThickeningIdeal h₂ hiso₂ hfo₂).I)
        (thickeningIdealPushforwardMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂)
        ((smallEtaleRingedToposHom B S hS
            ((schemeSpaceFunctor B S hS).map g)).pushforwardModules.map
          ((spaceModuleAdj ((schemeSpaceFunctor B S hS).map h₂)).unit.app
            (affineThickeningIdeal h₂ hiso₂ hfo₂).I) ≫
        (modulePushforwardCompIsoOfEq ((schemeSpaceFunctor B S hS).map h₂)
          ((schemeSpaceFunctor B S hS).map g) ((schemeSpaceFunctor B S hS).map h₁)
          ht).hom.app _) := by
  refine homEquiv_spaceModuleAdj_eq_comp_map_unit_comp_of_heq
    (t₁ := representedSpaceMap B S hS h₁) (t₂ := representedSpaceMap B S hS h₂)
    (γ := representedSpaceMap B S hS g) (N₁ := (affineThickeningIdeal h₁ hiso₁ hfo₁).I)
    (N₂ := (affineThickeningIdeal h₂ hiso₂ hfo₂).I)
    (lam := thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂)
    (s₂ := (representedThickeningIdealPullbackSpellingIso h₂ hiso₂ hfo₂).hom) ?_ ?_ ?_
    ((representedSpaceMap_comp B S hS h₂ g).trans (congrArg (representedSpaceMap B S hS) hg))
    ht ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (homEquiv_spaceModuleAdj_thickeningIdealMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂)
  · rfl
  · rfl
  · rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact HEq.rfl
  · exact thickeningIdealPushforwardMap_heq_schemeSpaceFunctor h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂
  · exact thickeningIdealMap_heq_representedSpaceMap h₁ h₂ g hg hiso₁ hfo₁ hiso₂ hfo₂ hh₁ hh₂
  · exact representedThickeningIdealPullbackSpellingIso_inv_eq h₁ hiso₁ hfo₁
  · exact representedThickeningIdealPullbackSpellingIso_hom_eq h₂ hiso₂ hfo₂
  · rfl
  · exact eq_of_heq (heq_comp
      (pullbackModules_obj_idealOfThickening_schemeSpaceFunctor_eq h₁ hiso₁ hfo₁)
      (pullbackModules_obj_idealOfThickening_schemeSpaceFunctor_eq h₂ hiso₂ hfo₂) rfl HEq.rfl
      HEq.rfl)

end IdealMapMate

namespace CoherentSituation

variable {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T'₁ T'₂ : SchemesOver D.Y} (h₁ : ξ.T ⟶ T'₁) (h₂ : ξ.T ⟶ T'₂)
  (g : T'₂ ⟶ T'₁) (hg : h₂ ≫ g = h₁)
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₁.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]

/-- **`λ_g` is the mate of `κ_g` on the bottom of the cube of the relative squares.** For
morphisms `h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` of affine first order thickenings with
`h₂ ≫ g = h₁`, the map `λ_g` of the pulled-back ideals of `T ⊂ T'ₖ`, read through the
identifications of the inverse images, corresponds under `t₁^* ⊣ t₁_*` to
`κ_g ≫ g_*(η) ≫ (g_*t₂_* ≅ t₁_*)`, where `tₖ` and `g` are the morphisms of the bottom of the cube
of `AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealTranspose` and `ht` is any proof
of `t₂ ≫ g = t₁`: the hypothesis `hlam` of
`Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq` for that cube. -/
theorem relativeSquare_homEquiv_thickeningIdealMap
    (ht : (schemeSpaceFunctor B S hS).map h₂.left ≫ (schemeSpaceFunctor B S hS).map g.left =
      (schemeSpaceFunctor B S hS).map h₁.left) :
    (spaceModuleAdj ((schemeSpaceFunctor B S hS).map h₁.left)).homEquiv _ _
        (eqToHom (congrArg (fun F => F.obj (affineThickeningIdeal h₁.left
            (isIso_toRange_testSchemeMap h₁ hh₁)
            (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)).I)
          (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom
            ((schemeSpaceFunctor B S hS).map h₁.left))) ≫
        CategoryStruct.comp
          (X := (smallEtaleRingedToposHom B S hS
            ((schemeSpaceFunctor B S hS).map h₁.left)).toRingedToposModulesHom.pullbackModules.obj
            (affineThickeningIdeal h₁.left (isIso_toRange_testSchemeMap h₁ hh₁)
              (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)).I)
          (Y := (smallEtaleRingedToposHom B S hS
            ((schemeSpaceFunctor B S hS).map h₂.left)).toRingedToposModulesHom.pullbackModules.obj
            (affineThickeningIdeal h₂.left (isIso_toRange_testSchemeMap h₂ hh₂)
              (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I)
          (thickeningIdealMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
            (isIso_toRange_testSchemeMap h₁ hh₁)
            (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
            (isIso_toRange_testSchemeMap h₂ hh₂)
            (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)
            hh₁ hh₂)
          (eqToHom (congrArg (fun F => F.obj (affineThickeningIdeal h₂.left
              (isIso_toRange_testSchemeMap h₂ hh₂)
              (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I)
            (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom
              ((schemeSpaceFunctor B S hS).map h₂.left))).symm)) =
      CategoryStruct.comp
        (Y := (smallEtaleRingedToposHom B S hS
          ((schemeSpaceFunctor B S hS).map g.left)).pushforwardModules.obj
          (affineThickeningIdeal h₂.left (isIso_toRange_testSchemeMap h₂ hh₂)
            (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I)
        (thickeningIdealPushforwardMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
          (isIso_toRange_testSchemeMap h₁ hh₁)
          (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
          (isIso_toRange_testSchemeMap h₂ hh₂)
          (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂))
        ((smallEtaleRingedToposHom B S hS
            ((schemeSpaceFunctor B S hS).map g.left)).pushforwardModules.map
          ((spaceModuleAdj ((schemeSpaceFunctor B S hS).map h₂.left)).unit.app
            (affineThickeningIdeal h₂.left (isIso_toRange_testSchemeMap h₂ hh₂)
              (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I) ≫
        (modulePushforwardCompIsoOfEq ((schemeSpaceFunctor B S hS).map h₂.left)
          ((schemeSpaceFunctor B S hS).map g.left) ((schemeSpaceFunctor B S hS).map h₁.left)
          ht).hom.app _) :=
  homEquiv_spaceModuleAdj_schemeSpaceFunctor_thickeningIdealMap h₁.left h₂.left g.left
    (left_comp_left_eq_of_comp_eq g hg)
    (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
    (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)
    hh₁ hh₂ ht

end CoherentSituation

end AlgebraicGeometry.Space
