module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealTransposeIdeals
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeThickeningTargetBridge

/-!
# The map of `κ_g` on the ideals, read through `X_g`

For morphisms `h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` of affine first order thickenings
with `h₂ ≫ g = h₁`,
`AlgebraicGeometry.Space.CoherentSituation.RelativeSquareIdealTransposeIdealMaps` says that the
map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g` is `j^♯` on the induced maps of ideals of the relative
squares, for `j` the morphism of the thickened targets
`AlgebraicGeometry.Space.CoherentSituation.relativeThickeningTarget`. This file states that
equation with `j` replaced by the morphism of small étale ringed topoi of `X_g` and `j^♯` by its
unit-module structure map.

## Main results

* `relativeSquareIdealTranspose_comp_map_eq_comp_unitStructureMap`: the map of `κ_g` on the
  ideals of the relative squares is the unit-module structure map of `X_g`.

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

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

-- Local priority 10000: the searches through `relBaseTop`/`relBaseBottom` take 1-3 s each
-- otherwise.
attribute [local instance 10000] relBaseTop_hasSheafCompose_forget_ringCat
  relBaseTop_hasSheafCompose_forget₂_commRingCat relBaseTop_hasSheafCompose_forget_addCommGrpCat
  relBaseBottom_hasSheafCompose_forget_ringCat relBaseBottom_hasSheafCompose_forget₂_commRingCat

-- Local priority 10000: without these the sheafification instances of the small étale
-- topoi are searched at an undetermined universe and elaboration is stuck on universe constraints.
attribute [local instance 10000] smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T'₁ T'₂ : SchemesOver D.Y} (h₁ : ξ.T ⟶ T'₁) (h₂ : ξ.T ⟶ T'₂)
  (g : T'₂ ⟶ T'₁) (hg : h₂ ≫ g = h₁)
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₁.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₁.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)] in
/-- **The map of `κ_g` is the structure map of `X_g` on the ideals**: given the equation
`H : RelativeSquareIdealTransposeIdealMaps h₁ h₂ g hg hh₁ hh₂`, the same equation holds with the
morphism `j` of the thickened targets replaced by the morphism of small étale ringed topoi of `X_g`
(they are equal by definition, `relativeThickeningTarget_j`) and `j^♯` by its unit-module
structure map. -/
theorem relativeSquareIdealTranspose_comp_map_eq_comp_unitStructureMap
    (H : RelativeSquareIdealTransposeIdealMaps h₁ h₂ g hg hh₁ hh₂) :
    relativeSquareIdealTranspose h₁ h₂ g hg hh₁ hh₂ ≫
        (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
          ((MorphismOfThickenings.ofFirstOrderThickenings
              (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h₂))
              (D.relativeSquareSituation.relativeSquareThickening h₂)
              (D.relativeSquareSituation.relativeSquareLeft h₂)
              (relBaseRight (smallEtaleRingedToposHom B S hS
                (D.relativeSquareSituation.projection T'₂)))
              (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
              (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₂ hh₂)
              (D.relativeSquareSituation.relativeSquare_comm h₂)).idealMap ≫
            (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂
              hh₂).idealOfThickening.incl) =
      (MorphismOfThickenings.ofFirstOrderThickenings
          (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h₁))
          (D.relativeSquareSituation.relativeSquareThickening h₁)
          (D.relativeSquareSituation.relativeSquareLeft h₁)
          (relBaseRight (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.projection T'₁)))
          (D.relativeSquareSituation.relativeMapFirstOrderThickening h₁ hh₁)
          (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₁ hh₁)
          (D.relativeSquareSituation.relativeSquare_comm h₁)).idealMap ≫
        (D.relativeSquareSituation.relativeMapFirstOrderThickening h₁ hh₁).idealOfThickening.incl ≫
        RingedToposHom.unitStructureMap
          (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap g)) :=
  H.comp_eq.trans (congrArg (_ ≫ _ ≫ ·)
    (ThickeningTargetMorphism.jSharpUnit_eq_unitStructureMap (relativeThickeningTarget h₁ h₂ g hg)))

end AlgebraicGeometry.Space.CoherentSituation

end
