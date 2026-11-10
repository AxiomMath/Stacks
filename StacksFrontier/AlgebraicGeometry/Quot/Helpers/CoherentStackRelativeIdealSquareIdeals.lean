module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealTransposeIdeals
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleIdealPushforwardTranspose
public import StacksFrontier.Deformation.ToposThickening.Helpers.RelativeBaseIdealMapTranspose

/-!
# The map of `κ_g` on the relative bases is `j^♯` on the ideals: the proof

For morphisms `h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` of affine first order thickenings
with `h₂ ≫ g = h₁`, the map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g`
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealTranspose`) is `j^♯` on the induced
maps of ideals of the relative squares
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealTranspose_idealMaps`).

The proof is the instance, at the relative squares of `h₁` and `h₂`, of the statement for arbitrary
ringed topoi `Deformation.ToposThickening.isoConjugateMap_comp_map_idealMap_comp_incl_of_heq`,
whose input on the cube is `CategoryTheory.Adjunction.homEquiv_symm_comp_map_comp_of_unit_maps`
for the adjunctions `f'ₖ^* ⊣ f'ₖ_*` with `κ_g` being `g^♯` on the ideals
(`AlgebraicGeometry.Space.thickeningIdealPushforwardMap_comp_map_incl`). Every hypothesis of
that statement is proved by a term whose type determines its variables, and the identifications
of the variables with their values are proved by reflexivity one at a time. Used in the
functoriality of the obstruction classes of `Coh_{X/B}` (second proof of Stacks 08WA).

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

-- Local priority 10000: the instance context of `CoherentStackRelativeIdealSquare`, whose
-- statement is proved here; the searches through `relBaseTop`/`relBaseBottom` take 1-3 s each.
attribute [local instance 10000] relBaseTop_hasSheafCompose_forget_ringCat
  relBaseTop_hasSheafCompose_forget₂_commRingCat relBaseTop_hasSheafCompose_forget_addCommGrpCat
  relBaseBottom_hasSheafCompose_forget_ringCat relBaseBottom_hasSheafCompose_forget₂_commRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T'₁ T'₂ : SchemesOver D.Y} (h₁ : ξ.T ⟶ T'₁) (h₂ : ξ.T ⟶ T'₂)
  (g : T'₂ ⟶ T'₁) (hg : h₂ ≫ g = h₁)
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))

/-- **The map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g` is `j^♯` on the ideals**: followed by `j_*` of the
induced map of ideals of the relative square of `h₂` and the inclusion of its ideal, it is the
induced map of ideals of the relative square of `h₁`, the inclusion of its ideal and
`j^♯ : O_{X_{T'₁}} ⟶ j_*O_{X_{T'₂}}`. -/
theorem relativeSquareIdealTranspose_idealMaps :
    RelativeSquareIdealTransposeIdealMaps h₁ h₂ g hg hh₁ hh₂ := by
  refine ⟨?_⟩
  have hcube := Adjunction.homEquiv_symm_comp_map_comp_of_unit_maps
    (spaceModuleAdj (D.relativeSquareSituation.projection T'₁))
    (spaceModuleAdj (D.relativeSquareSituation.projection T'₂)) _ _ _ _ _ _ _ _ _
    (unitStructureMap_comp_map_unitStructureMap_comp_modulePushforwardCompIsoOfEq
      (D.relativeSquareSituation.projection T'₂) ((schemeSpaceFunctor B S hS).map g.left)
      (D.relativeSquareSituation.relativeMap g ≫ D.relativeSquareSituation.projection T'₁)
      (D.relativeSquareSituation.relativeMap_comp_projection g).symm)
    (unitStructureMap_comp_map_unitStructureMap_comp_modulePushforwardCompIsoOfEq
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.projection T'₁)
      (D.relativeSquareSituation.relativeMap g ≫ D.relativeSquareSituation.projection T'₁) rfl)
    _ _ _
    (thickeningIdealPushforwardMap_comp_map_incl h₁.left h₂.left g.left
      (left_comp_left_eq_of_comp_eq g hg)
      (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
      (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂))
  refine isoConjugateMap_comp_map_idealMap_comp_incl_of_heq (Z₁ := ?Z₁) (c₁ := ?c₁) (c₂ := ?c₂)
    (Z₂ := ?Z₂) rfl rfl HEq.rfl rfl rfl HEq.rfl HEq.rfl rfl rfl rfl rfl rfl rfl rfl rfl HEq.rfl
    HEq.rfl rfl hcube rfl HEq.rfl
    rfl rfl HEq.rfl rfl HEq.rfl HEq.rfl rfl rfl HEq.rfl rfl HEq.rfl HEq.rfl HEq.rfl
    (ThickeningTargetMorphism.jSharpUnit_eq_unitStructureMap (relativeThickeningTarget h₁ h₂ g hg))
  case Z₁ => exact D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h₁ hh₁
  case c₁ => exact (Functor.congr_obj
    (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom
      (D.relativeSquareSituation.projection T'₁)) _).symm
  case c₂ => exact (Functor.congr_obj
    (pullbackModules_toModulesHom_eq_pullbackModules_toRingedToposModulesHom
      (D.relativeSquareSituation.projection T'₂)) _)
  case Z₂ => exact D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h₂ hh₂

end AlgebraicGeometry.Space.CoherentSituation

end
