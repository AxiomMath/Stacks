module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.CoefficientMap
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.DifferenceExt
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackObstructionNaturality
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquareIdeal
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeIdealSquareTranspose

/-!
# The ideal maps of the relative squares of `Coh_{X/B}`

For morphisms `h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` of affine first order thickenings
with `h₂ ≫ g = h₁`, this file defines the map `λ : f̃₁^*t̃₁^*𝒥̃₁ ⟶ f̃₂^*t̃₂^*𝒥̃₂` of the
pulled-back ideals of the relative squares induced by `λ_g : t₁^*𝒥₁ ⟶ t₂^*𝒥₂`
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap`) and the map
`f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g`
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealTranspose`). The map `λ` satisfies
the ideal-square compatibility as soon as the second map is `j^♯` on the ideals
(`AlgebraicGeometry.Space.CoherentSituation.relativeIdealSquareCompatible_of_comp_idealMap`): the
other hypothesis of
`Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_transpose`, on the
reductions, is the cube comparison of Stacks 03LU
(`Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq`).

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap`: the map `λ`.
* `AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealTranspose`: the map of `κ_g`.

This is used in the functoriality of the obstruction classes of `Coh_{X/B}` (second proof of
Stacks 08WA). This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u

namespace AlgebraicGeometry.Space.QuotientSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotientSituation B S hS) {T T' : SchemesOver D.Y} (h : T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- The pullback of the ideal `𝒥̃` of the relative base along `f̃'` through the two four-field
readings of `f̃'`, the second written with the ideal of the thickening of the relative base. -/
theorem relBaseRight_pullbackIdeal_eq :
    (pullbackModules (relBaseRight
        (smallEtaleRingedToposHom B S hS (D.projection T'))).toModulesHom).obj
        (D.relativeSquareThickeningFirstOrderThickening h hh).idealOfThickening.I =
      (relBaseRight (smallEtaleRingedToposHom B S hS
          (D.projection T'))).toRingedToposModulesHom.pullbackModules.obj
        (relBaseThickeningFirstOrderThickening
          (f' := smallEtaleRingedToposHom B S hS (D.projection T'))
          (D.testSchemeFirstOrderThickening h hh)).idealOfThickening.I :=
  congrArg
    (fun F => F.obj (D.relativeSquareThickeningFirstOrderThickening h hh).idealOfThickening.I)
    (RingedToposHom.pullbackModules_toRingedToposModulesHom
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))).symm

end AlgebraicGeometry.Space.QuotientSituation

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

-- Local priority 10000: instance search reaches these through `relBaseTop`/`relBaseBottom` slowly.
attribute [local instance 10000] relBaseTop_hasSheafCompose_forget_ringCat
  relBaseTop_hasSheafCompose_forget₂_commRingCat relBaseTop_hasSheafCompose_forget_addCommGrpCat
  relBaseBottom_hasSheafCompose_forget_ringCat relBaseBottom_hasSheafCompose_forget₂_commRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T'₁ T'₂ : SchemesOver D.Y} (h₁ : ξ.T ⟶ T'₁) (h₂ : ξ.T ⟶ T'₂)
  (g : T'₂ ⟶ T'₁) (hg : h₂ ≫ g = h₁)
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₁.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]

/-- **`λ : f̃₁^*t̃₁^*𝒥̃₁ ⟶ f̃₂^*t̃₂^*𝒥̃₂`**: the map `λ_g : t₁^*𝒥₁ ⟶ t₂^*𝒥₂` of the ideals of
`T ⊂ T'ₖ` pulled back along `X_T ⟶ T`, read through
`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso`. -/
def relativeSquareIdealMap :
    D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₁ hh₁ ⟶
      D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₂ hh₂ :=
  (D.relativeSquareSituation.relativeSquareBasePullbackIdealIso h₁ hh₁).hom ≫
    ((smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.projection ξ.T)).toRingedToposModulesHom.pullbackModules).map
      (thickeningIdealMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
        (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
        (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)
        hh₁ hh₂) ≫
    (D.relativeSquareSituation.relativeSquareBasePullbackIdealIso h₂ hh₂).inv

/-- The defining equation of `AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap`:
`λ = R₁ ≫ π^*(λ_g) ≫ R₂⁻¹`, with `Rₖ` the isomorphisms
`AlgebraicGeometry.Space.QuotientSituation.relativeSquareBasePullbackIdealIso` and
`π : X_T ⟶ T`. -/
theorem relativeSquareIdealMap_eq :
    type_of% (relativeSquareIdealMap.eq_1 h₁ h₂ g hg hh₁ hh₂) :=
  relativeSquareIdealMap.eq_1 h₁ h₂ g hg hh₁ hh₂

/-- **The map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g`** for `X_g : X_{T'₂} ⟶ X_{T'₁}`, on the pullbacks
`f̃'ₖ^*𝒥̃ₖ` of the ideals of the relative bases: `AlgebraicGeometry.Space.cubeIdealTranspose` for
`κ_g : 𝒥₁ ⟶ g_*𝒥₂` (`AlgebraicGeometry.Space.thickeningIdealPushforwardMap`). -/
def relativeSquareIdealTranspose :
    (pullbackModules (relBaseRight (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.projection T'₁))).toModulesHom).obj
        (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₁
          hh₁).idealOfThickening.I ⟶
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
        ((pullbackModules (relBaseRight (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.projection T'₂))).toModulesHom).obj
          (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₂
            hh₂).idealOfThickening.I) :=
  cubeIdealTranspose (D.relativeSquareSituation.relativeMap g)
    (D.relativeSquareSituation.projection T'₂) (D.relativeSquareSituation.projection T'₁)
    ((schemeSpaceFunctor B S hS).map g.left)
    (D.relativeSquareSituation.relativeMap g ≫ D.relativeSquareSituation.projection T'₁) rfl
    (D.relativeSquareSituation.relativeMap_comp_projection g).symm
    (thickeningIdealPushforwardMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
      (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
      (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂))
    (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h₁ hh₁)
    (relBasePullbackIdealIso
      (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h₁.left))
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'₁))
      (D.relativeSquareSituation.testSchemeFirstOrderThickening h₁ hh₁))
    (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h₂ hh₂)
    (relBasePullbackIdealIso
      (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h₂.left))
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'₂))
      (D.relativeSquareSituation.testSchemeFirstOrderThickening h₂ hh₂))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₁.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)] in
/-- The defining equation of
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealTranspose`. -/
theorem relativeSquareIdealTranspose_eq :
    relativeSquareIdealTranspose h₁ h₂ g hg hh₁ hh₂ =
      cubeIdealTranspose (D.relativeSquareSituation.relativeMap g)
        (D.relativeSquareSituation.projection T'₂) (D.relativeSquareSituation.projection T'₁)
        ((schemeSpaceFunctor B S hS).map g.left)
        (D.relativeSquareSituation.relativeMap g ≫ D.relativeSquareSituation.projection T'₁) rfl
        (D.relativeSquareSituation.relativeMap_comp_projection g).symm
        (thickeningIdealPushforwardMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
          (isIso_toRange_testSchemeMap h₁ hh₁)
          (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
          (isIso_toRange_testSchemeMap h₂ hh₂)
          (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂))
        (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h₁ hh₁)
        (relBasePullbackIdealIso
          (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h₁.left))
          (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'₁))
          (D.relativeSquareSituation.testSchemeFirstOrderThickening h₁ hh₁))
        (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h₂ hh₂)
        (relBasePullbackIdealIso
          (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h₂.left))
          (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'₂))
          (D.relativeSquareSituation.testSchemeFirstOrderThickening h₂ hh₂)) :=
  rfl

end AlgebraicGeometry.Space.CoherentSituation
