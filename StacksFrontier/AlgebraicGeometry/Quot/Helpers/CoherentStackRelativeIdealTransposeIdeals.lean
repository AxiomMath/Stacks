module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquare

/-!
# The map of `κ_g` on the relative bases is `j^♯` on the ideals: the statement

For morphisms `h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` of affine first order thickenings
with `h₂ ≫ g = h₁`,
`AlgebraicGeometry.Space.CoherentSituation.RelativeSquareIdealTransposeIdealMaps` says that the
map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g`
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealTranspose`) is `j^♯` on the induced
maps of ideals of the relative squares.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.RelativeSquareIdealTransposeIdealMaps`: the map of
  `κ_g` on the relative bases is `j^♯` on the induced maps of ideals.

## Implementation notes

The proposition is recorded as a one-field structure, elaborated once here in the instance
context of `CoherentStackRelativeIdealSquare`, so that its proof and its use compare it
syntactically.

## References

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

-- Local priority 10000: the instance context of `CoherentStackRelativeIdealSquare`; the searches
-- through `relBaseTop`/`relBaseBottom` take 1-3 s each otherwise.
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

/-- **The map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g` is `j^♯` on the ideals**: followed by `j_*` of the
induced map of ideals of the relative square of `h₂` and the inclusion of its ideal, it is the
induced map of ideals of the relative square of `h₁`, the inclusion of its ideal and
`j^♯ : O_{X_{T'₁}} ⟶ j_*O_{X_{T'₂}}`. -/
structure RelativeSquareIdealTransposeIdealMaps : Prop where
  /-- The compatibility with the induced maps of ideals. -/
  comp_eq :
    relativeSquareIdealTranspose h₁ h₂ g hg hh₁ hh₂ ≫
        (relativeThickeningTarget h₁ h₂ g hg).j.pushforwardModules.map
          ((MorphismOfThickenings.ofFirstOrderThickenings
              (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h₂))
              (D.relativeSquareSituation.relativeSquareThickening h₂)
              (D.relativeSquareSituation.relativeSquareLeft h₂)
              (relBaseRight (smallEtaleRingedToposHom B S hS
                (D.relativeSquareSituation.projection T'₂)))
              (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
              (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₂ hh₂)
              (D.relativeSquareSituation.relativeSquare_comm h₂)).idealMap ≫
            (D.relativeSquareSituation.relativeMapFirstOrderThickening
              h₂ hh₂).idealOfThickening.incl) =
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
        (relativeThickeningTarget h₁ h₂ g hg).jSharpUnit

end AlgebraicGeometry.Space.CoherentSituation

end
