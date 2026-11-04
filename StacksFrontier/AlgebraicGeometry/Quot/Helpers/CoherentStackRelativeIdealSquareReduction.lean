module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquare
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ModulePullbackSquareCubeSideRelativeSquare
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeSquareBasePullbackIdealIsoCubeSide
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeSquareCubeMatePremise
public import StacksFrontier.Deformation.ToposThickening.Helpers.IdealSquareCompatibleOfCube

/-!
# The reductions of the pulled-back ideals of the relative squares of `Coh_{X/B}`

For morphisms `h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` of affine first order thickenings
with `h₂ ≫ g = h₁`, the map `λ : f̃₁^*t̃₁^*𝒥̃₁ ⟶ f̃₂^*t̃₂^*𝒥̃₂` of the pulled-back ideals of the
relative squares induced by `λ_g : t₁^*𝒥₁ ⟶ t₂^*𝒥₂`
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap`) satisfies the ideal-square
compatibility as soon as the map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g`
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealTranspose`) is `j^♯` on the ideals
(`AlgebraicGeometry.Space.CoherentSituation.relativeIdealSquareCompatible_of_comp_idealMap`): the
other hypothesis of
`Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_transpose`, on the
reductions, is the cube comparison of Stacks 03LU
(`Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq`), applied in
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap_reduction_aux`.

All spaces of the cube are spelled through `AlgebraicGeometry.schemeSpaceFunctor`, the spelling of
`λ_g` (`AlgebraicGeometry.Space.thickeningIdealMap`) and of the relative squares.

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

-- Local priority 10000: at the default priority, the searches through `relBaseTop`/`relBaseBottom`
-- for these instances take 1-3 s each.
attribute [local instance 10000] relBaseTop_hasSheafCompose_forget_ringCat
  relBaseTop_hasSheafCompose_forget₂_commRingCat relBaseTop_hasSheafCompose_forget_addCommGrpCat
  relBaseBottom_hasSheafCompose_forget_ringCat relBaseBottom_hasSheafCompose_forget₂_commRingCat

-- Local priority 10000: the searches through `smallEtaleRingedTopos` for these instances make up
-- most of the elaboration of the pieces of the cube (`relBasePullbackIdealIso` at
-- `affineThickeningIdeal`: 67.7k heartbeats without, 16.9k with); pinned at the universe `u`, they
-- also keep the coefficient universe off the universe-polymorphic sheafification instances.
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
/-- `AlgebraicGeometry.Space.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj` at
the cube of the relative squares of `h₁` and `h₂`, with every space given explicitly. -/
theorem relativeSquareIdealMap_reduction_aux :
    type_of% (homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj
      (V := D.relativeSquareSituation.space ξ.T) (W := D.relativeSquareSituation.space T'₂)
      (X := D.relativeSquareSituation.space T'₁)
      (T := (schemeSpaceFunctor B S hS).obj ξ.T.left)
      (T₂ := (schemeSpaceFunctor B S hS).obj T'₂.left)
      (T₁ := (schemeSpaceFunctor B S hS).obj T'₁.left)
      (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
      (D.relativeSquareSituation.relativeMap h₁) (relativeMap_comp_of_comp_eq g hg)
      (D.relativeSquareSituation.projection ξ.T) (D.relativeSquareSituation.projection T'₂)
      (D.relativeSquareSituation.projection T'₁)
      ((schemeSpaceFunctor B S hS).map h₂.left) ((schemeSpaceFunctor B S hS).map g.left)
      ((schemeSpaceFunctor B S hS).map h₁.left)
      ((((schemeSpaceFunctor B S hS).map_comp h₂.left g.left).symm.trans
        (congrArg (schemeSpaceFunctor B S hS).map (left_comp_left_eq_of_comp_eq g hg))))
      (D.relativeSquareSituation.relativeMap g ≫ D.relativeSquareSituation.projection T'₁) rfl
      (D.relativeSquareSituation.relativeMap_comp_projection g).symm
      (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₁.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h₁) rfl
      (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₂.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h₂) rfl) :=
  homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj
      (V := D.relativeSquareSituation.space ξ.T) (W := D.relativeSquareSituation.space T'₂)
      (X := D.relativeSquareSituation.space T'₁)
      (T := (schemeSpaceFunctor B S hS).obj ξ.T.left)
      (T₂ := (schemeSpaceFunctor B S hS).obj T'₂.left)
      (T₁ := (schemeSpaceFunctor B S hS).obj T'₁.left)
      (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
      (D.relativeSquareSituation.relativeMap h₁) (relativeMap_comp_of_comp_eq g hg)
      (D.relativeSquareSituation.projection ξ.T) (D.relativeSquareSituation.projection T'₂)
      (D.relativeSquareSituation.projection T'₁)
      ((schemeSpaceFunctor B S hS).map h₂.left) ((schemeSpaceFunctor B S hS).map g.left)
      ((schemeSpaceFunctor B S hS).map h₁.left)
      ((((schemeSpaceFunctor B S hS).map_comp h₂.left g.left).symm.trans
        (congrArg (schemeSpaceFunctor B S hS).map (left_comp_left_eq_of_comp_eq g hg))))
      (D.relativeSquareSituation.relativeMap g ≫ D.relativeSquareSituation.projection T'₁) rfl
      (D.relativeSquareSituation.relativeMap_comp_projection g).symm
      (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₁.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h₁) rfl
      (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₂.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h₂) rfl

/-- `AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap_reduction_aux` at the ideals
`t_k^*𝒥_k`, `κ_g` and `λ_g`: the cube comparison, from its remaining hypotheses. -/
theorem relativeSquareIdealMap_reduction_of_mate :
    type_of% (relativeSquareIdealMap_reduction_aux h₁ h₂ g hg
    (affineThickeningIdeal h₁.left (isIso_toRange_testSchemeMap h₁ hh₁)
      (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)).I
    (affineThickeningIdeal h₂.left (isIso_toRange_testSchemeMap h₂ hh₂)
      (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I
    (thickeningIdealPushforwardMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
      (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
      (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂))
    (thickeningIdealMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
      (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
      (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)
      hh₁ hh₂)
    _ rfl _ rfl _ rfl) :=
  relativeSquareIdealMap_reduction_aux h₁ h₂ g hg
    (affineThickeningIdeal h₁.left (isIso_toRange_testSchemeMap h₁ hh₁)
      (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)).I
    (affineThickeningIdeal h₂.left (isIso_toRange_testSchemeMap h₂ hh₂)
      (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I
    (thickeningIdealPushforwardMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
      (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
      (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂))
    (thickeningIdealMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
      (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
      (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)
      hh₁ hh₂)
    _ rfl _ rfl _ rfl

/-- **`λ_g` is the mate of `κ_g` on the bottom of the cube of the relative squares**, as the
hypothesis of `CoherentSituation.relativeSquareIdealMap_reduction_of_mate`:
`CoherentSituation.relativeSquare_homEquiv_thickeningIdealMap` read through
`Space.premise_homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj`. -/
theorem relativeSquare_homEquiv_thickeningIdealMap_premise :
    premise (relativeSquareIdealMap_reduction_of_mate h₁ h₂ g hg hh₁ hh₂) := by
  have hH := relativeSquare_homEquiv_thickeningIdealMap h₁ h₂ g hg hh₁ hh₂
    (((schemeSpaceFunctor B S hS).map_comp h₂.left g.left).symm.trans
      (congrArg (schemeSpaceFunctor B S hS).map (left_comp_left_eq_of_comp_eq g hg)))
  refine premise_homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq_spaceModuleAdj
      (V := D.relativeSquareSituation.space ξ.T) (W := D.relativeSquareSituation.space T'₂)
      (X := D.relativeSquareSituation.space T'₁)
      (T := (schemeSpaceFunctor B S hS).obj ξ.T.left)
      (T₂ := (schemeSpaceFunctor B S hS).obj T'₂.left)
      (T₁ := (schemeSpaceFunctor B S hS).obj T'₁.left)
      (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
      (D.relativeSquareSituation.relativeMap h₁) (relativeMap_comp_of_comp_eq g hg)
      (D.relativeSquareSituation.projection ξ.T) (D.relativeSquareSituation.projection T'₂)
      (D.relativeSquareSituation.projection T'₁)
      ((schemeSpaceFunctor B S hS).map h₂.left) ((schemeSpaceFunctor B S hS).map g.left)
      ((schemeSpaceFunctor B S hS).map h₁.left)
      ((((schemeSpaceFunctor B S hS).map_comp h₂.left g.left).symm.trans
        (congrArg (schemeSpaceFunctor B S hS).map (left_comp_left_eq_of_comp_eq g hg))))
      (D.relativeSquareSituation.relativeMap g ≫ D.relativeSquareSituation.projection T'₁) rfl
      (D.relativeSquareSituation.relativeMap_comp_projection g).symm
      (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₁.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h₁) rfl
      (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₂.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h₂) rfl
    (affineThickeningIdeal h₁.left (isIso_toRange_testSchemeMap h₁ hh₁)
      (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)).I
    (affineThickeningIdeal h₂.left (isIso_toRange_testSchemeMap h₂ hh₂)
      (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I
    (thickeningIdealPushforwardMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
      (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
      (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂))
    (thickeningIdealMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
      (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
      (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)
      hh₁ hh₂)
    (t₁' := (schemeSpaceFunctor B S hS).map h₁.left)
    (t₂' := (schemeSpaceFunctor B S hS).map h₂.left)
    (γ' := (schemeSpaceFunctor B S hS).map g.left)
    (N₁' := (affineThickeningIdeal h₁.left (isIso_toRange_testSchemeMap h₁ hh₁)
        (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)).I)
    (N₂' := (affineThickeningIdeal h₂.left (isIso_toRange_testSchemeMap h₂ hh₂)
        (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I)
    (κ' := thickeningIdealPushforwardMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
      (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
      (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂))
    (lam' := thickeningIdealMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
      (isIso_toRange_testSchemeMap h₁ hh₁) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
      (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)
      hh₁ hh₂)
    hH ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first | exact rfl | exact HEq.rfl

/-- **The cube comparison for the relative squares of `h₁` and `h₂`**: the reductions of the
pulled-back ideals carry the map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g` to `i₁_*λ`, read through Stacks
03LU (`Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq` at the cube
of the relative squares). It is `CoherentSituation.relativeSquareIdealMap_reduction_of_mate` at the
mate of `λ_g` (`CoherentSituation.relativeSquare_homEquiv_thickeningIdealMap_premise`), the
comparisons of Stacks 03LU around the sides, the isomorphisms `R_k` and their identifications
`CoherentSituation.relativeSquareBasePullbackIdealIso_hom_eq_cubeSide`. -/
theorem relativeSquareIdealMap_reduction :
    type_of% (relativeSquareIdealMap_reduction_of_mate h₁ h₂ g hg hh₁ hh₂
    (relativeSquare_homEquiv_thickeningIdealMap_premise h₁ h₂ g hg hh₁ hh₂)
    (modulePullbackSquare B S hS (V := D.relativeSquareSituation.space ξ.T)
      (W := D.relativeSquareSituation.space T'₁)
      (X := (schemeSpaceFunctor B S hS).obj ξ.T.left)
      (Z := (schemeSpaceFunctor B S hS).obj T'₁.left)
      (e := D.relativeSquareSituation.relativeMap h₁)
      (l := D.relativeSquareSituation.projection T'₁)
      (r := D.relativeSquareSituation.projection ξ.T) (q := (schemeSpaceFunctor B S hS).map h₁.left)
      (k := D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₁.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h₁) rfl)
    (modulePullbackSquare B S hS (V := D.relativeSquareSituation.space ξ.T)
      (W := D.relativeSquareSituation.space T'₂)
      (X := (schemeSpaceFunctor B S hS).obj ξ.T.left)
      (Z := (schemeSpaceFunctor B S hS).obj T'₂.left)
      (e := D.relativeSquareSituation.relativeMap h₂)
      (l := D.relativeSquareSituation.projection T'₂)
      (r := D.relativeSquareSituation.projection ξ.T) (q := (schemeSpaceFunctor B S hS).map h₂.left)
      (k := D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₂.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h₂) rfl)
    (modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app_of_toRingedToposModulesHom
      (V := D.relativeSquareSituation.space ξ.T) (W := D.relativeSquareSituation.space T'₁)
      (T := (schemeSpaceFunctor B S hS).obj ξ.T.left)
      (T' := (schemeSpaceFunctor B S hS).obj T'₁.left)
      (D.relativeSquareSituation.projection ξ.T) (D.relativeSquareSituation.relativeMap h₁)
      (D.relativeSquareSituation.projection T'₁) ((schemeSpaceFunctor B S hS).map h₁.left)
      (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₁.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h₁) rfl
      (affineThickeningIdeal h₁.left (isIso_toRange_testSchemeMap h₁ hh₁)
        (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)).I)
    (modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app_of_toRingedToposModulesHom
      (V := D.relativeSquareSituation.space ξ.T) (W := D.relativeSquareSituation.space T'₂)
      (T := (schemeSpaceFunctor B S hS).obj ξ.T.left)
      (T' := (schemeSpaceFunctor B S hS).obj T'₂.left)
      (D.relativeSquareSituation.projection ξ.T) (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.projection T'₂) ((schemeSpaceFunctor B S hS).map h₂.left)
      (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₂.left)
      (D.relativeSquareSituation.relativeMap_comp_projection h₂) rfl
      (affineThickeningIdeal h₂.left (isIso_toRange_testSchemeMap h₂ hh₂)
        (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I)
    (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h₁ hh₁)
    (D.relativeSquareSituation.relativeSquareRelBasePullbackIdealIso h₁ hh₁)
    (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h₂ hh₂)
    (D.relativeSquareSituation.relativeSquareRelBasePullbackIdealIso h₂ hh₂)
    (D.relativeSquareSituation.relativeSquareBasePullbackIdealIsoPullback h₁ hh₁)
    (D.relativeSquareSituation.relativeSquareBasePullbackIdealIsoPullback h₂ hh₂)
    (D.relativeSquareSituation.relativeSquareBasePullbackIdealIso h₁ hh₁)
    (D.relativeSquareSituation.relativeSquareBasePullbackIdealIso h₂ hh₂)
    (relativeSquareBasePullbackIdealIso_hom_eq_cubeSide h₁ hh₁)
    (relativeSquareBasePullbackIdealIso_hom_eq_cubeSide h₂ hh₂)) :=
  relativeSquareIdealMap_reduction_of_mate h₁ h₂ g hg hh₁ hh₂
      (relativeSquare_homEquiv_thickeningIdealMap_premise h₁ h₂ g hg hh₁ hh₂)
      (modulePullbackSquare B S hS (V := D.relativeSquareSituation.space ξ.T)
        (W := D.relativeSquareSituation.space T'₁)
        (X := (schemeSpaceFunctor B S hS).obj ξ.T.left)
        (Z := (schemeSpaceFunctor B S hS).obj T'₁.left)
        (e := D.relativeSquareSituation.relativeMap h₁)
        (l := D.relativeSquareSituation.projection T'₁)
        (r := D.relativeSquareSituation.projection ξ.T)
        (q := (schemeSpaceFunctor B S hS).map h₁.left)
        (k := D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₁.left)
        (D.relativeSquareSituation.relativeMap_comp_projection h₁) rfl)
      (modulePullbackSquare B S hS (V := D.relativeSquareSituation.space ξ.T)
        (W := D.relativeSquareSituation.space T'₂)
        (X := (schemeSpaceFunctor B S hS).obj ξ.T.left)
        (Z := (schemeSpaceFunctor B S hS).obj T'₂.left)
        (e := D.relativeSquareSituation.relativeMap h₂)
        (l := D.relativeSquareSituation.projection T'₂)
        (r := D.relativeSquareSituation.projection ξ.T)
        (q := (schemeSpaceFunctor B S hS).map h₂.left)
        (k := D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₂.left)
        (D.relativeSquareSituation.relativeMap_comp_projection h₂) rfl)
      (modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app_of_toRingedToposModulesHom
        (V := D.relativeSquareSituation.space ξ.T) (W := D.relativeSquareSituation.space T'₁)
        (T := (schemeSpaceFunctor B S hS).obj ξ.T.left)
        (T' := (schemeSpaceFunctor B S hS).obj T'₁.left)
        (D.relativeSquareSituation.projection ξ.T) (D.relativeSquareSituation.relativeMap h₁)
        (D.relativeSquareSituation.projection T'₁) ((schemeSpaceFunctor B S hS).map h₁.left)
        (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₁.left)
        (D.relativeSquareSituation.relativeMap_comp_projection h₁) rfl
        (affineThickeningIdeal h₁.left (isIso_toRange_testSchemeMap h₁ hh₁)
          (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)).I)
      (modulePullbackSquare_hom_app_eq_cubeSideIso_hom_app_of_toRingedToposModulesHom
        (V := D.relativeSquareSituation.space ξ.T) (W := D.relativeSquareSituation.space T'₂)
        (T := (schemeSpaceFunctor B S hS).obj ξ.T.left)
        (T' := (schemeSpaceFunctor B S hS).obj T'₂.left)
        (D.relativeSquareSituation.projection ξ.T) (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.projection T'₂) ((schemeSpaceFunctor B S hS).map h₂.left)
        (D.relativeSquareSituation.projection ξ.T ≫ (schemeSpaceFunctor B S hS).map h₂.left)
        (D.relativeSquareSituation.relativeMap_comp_projection h₂) rfl
        (affineThickeningIdeal h₂.left (isIso_toRange_testSchemeMap h₂ hh₂)
          (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I)
      (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h₁ hh₁)
      (D.relativeSquareSituation.relativeSquareRelBasePullbackIdealIso h₁ hh₁)
      (D.relativeSquareSituation.relBaseRight_pullbackIdeal_eq h₂ hh₂)
      (D.relativeSquareSituation.relativeSquareRelBasePullbackIdealIso h₂ hh₂)
      (D.relativeSquareSituation.relativeSquareBasePullbackIdealIsoPullback h₁ hh₁)
      (D.relativeSquareSituation.relativeSquareBasePullbackIdealIsoPullback h₂ hh₂)
      (D.relativeSquareSituation.relativeSquareBasePullbackIdealIso h₁ hh₁)
      (D.relativeSquareSituation.relativeSquareBasePullbackIdealIso h₂ hh₂)
      (relativeSquareBasePullbackIdealIso_hom_eq_cubeSide h₁ hh₁)
      (relativeSquareBasePullbackIdealIso_hom_eq_cubeSide h₂ hh₂)

end AlgebraicGeometry.Space.CoherentSituation
