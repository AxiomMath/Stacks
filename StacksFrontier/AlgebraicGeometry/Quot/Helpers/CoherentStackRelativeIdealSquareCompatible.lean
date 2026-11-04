module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquareReduction
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackTestRelativeIdealSquare
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeThickeningTargetBridge
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeSquareIdealTransposeUnitStructureMap
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleThickeningTargetJBridge
public import StacksFrontier.Deformation.ToposThickening.Helpers.IdealSquareCompatibleOfCubeObjects
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.RelativeSquareIdealMapSpellingHeq
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleModuleMapHeq
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.ModuleTransposeSets
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.TransposeCompatible

/-!
# The ideal-square compatibility of the relative squares of `Coh_{X/B}` from the ideal maps

For morphisms `h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` of affine first order thickenings
with `h₂ ≫ g = h₁`, the map `λ` of the pulled-back ideals of the relative squares
(`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap`) satisfies the ideal-square
compatibility as soon as the map `f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g` is `j^♯` on the ideals
(`AlgebraicGeometry.Space.CoherentSituation.relativeIdealSquareCompatible_of_comp_idealMap`), and
so for all affine first order thickenings
(`AlgebraicGeometry.Space.CoherentSituation.relativeIdealSquareCompatible_of_idealMaps`). The
reduction hypothesis is the cube comparison
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap_reduction`, read along `j = X_g`
by the lemma
`Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_transpose_of_j_eq`.

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

attribute [local instance 10000] relBaseTop_hasSheafCompose_forget_ringCat
  relBaseTop_hasSheafCompose_forget₂_commRingCat relBaseTop_hasSheafCompose_forget_addCommGrpCat
  relBaseBottom_hasSheafCompose_forget_ringCat relBaseBottom_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
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

variable (hfl₁ : IsFlat B S hS (D.projection T'₁).hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)

/-- Composites `f ≫ m ≫ g` and `f' ≫ m' ≫ g'` are heterogeneously equal when their middle
objects are equal and their factors are heterogeneously equal. -/
theorem comp_comp_heq_of_heq {C : Type*} [Category C] {X Y A B A' B' : C} {f : X ⟶ A}
    {m : A ⟶ B} {g : B ⟶ Y} {f' : X ⟶ A'} {m' : A' ⟶ B'} {g' : B' ⟶ Y} (eA : A = A')
    (eB : B = B') (hf : f ≍ f') (hm : m ≍ m') (hg : g ≍ g') : f ≫ m ≫ g ≍ f' ≫ m' ≫ g' := by
  subst eA eB
  cases hf
  cases hm
  cases hg
  rfl

set_option maxHeartbeats 0 in
-- The `refine` against `idealSquareCompatible_of_transpose_of_j_eq` unifies its many explicit
-- arguments and closes the `rfl`/`HEq` side goals by unfolding very large module terms.
/-- **The ideal-square compatibility of `λ` from the ideal maps.** If the map
`f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `κ_g` is `j^♯` on the ideals
(`AlgebraicGeometry.Space.CoherentSituation.RelativeSquareIdealTransposeIdealMaps`), then
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap` satisfies the ideal-square
compatibility of the relative squares of `h₁` and `h₂`. -/
theorem relativeIdealSquareCompatible_of_comp_idealMap
    (H₁ : RelativeSquareIdealTransposeIdealMaps h₁ h₂ g hg hh₁ hh₂) :
    RelativeIdealSquareCompatible h₁ h₂ g hg hh₁ hh₂ hfl₁ hfl₂
      (relativeSquareIdealMap h₁ h₂ g hg hh₁ hh₂) := by
  refine ThickeningTargetMorphism.idealSquareCompatible_of_transpose_of_j_eq
    (relativeThickeningTarget h₁ h₂ g hg)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h₁ hh₁)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
    (D.relativeSquareSituation.relativeSquareThickening h₁)
    (D.relativeSquareSituation.relativeSquareLeft h₁)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'₁)))
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₁ hh₁)
    (D.relativeSquareSituation.relativeSquare_comm h₁)
    (isFlat_relBaseRight_smallEtaleRingedToposHom (D.relativeSquareSituation.projection T'₁) hfl₁)
    (D.relativeSquareSituation.isStrict_relativeSquare h₁ hh₁)
    (D.relativeSquareSituation.relativeSquareThickening h₂)
    (D.relativeSquareSituation.relativeSquareLeft h₂)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'₂)))
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₂ hh₂)
    (D.relativeSquareSituation.relativeSquare_comm h₂)
    (isFlat_relBaseRight_smallEtaleRingedToposHom (D.relativeSquareSituation.projection T'₂) hfl₂)
    (D.relativeSquareSituation.isStrict_relativeSquare h₂ hh₂)
    (smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h₁)
      (relativeMap_comp_of_comp_eq g hg))
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap g))
    (relativeThickeningTarget_j h₁ h₂ g hg)
    (relativeSquareIdealMap h₁ h₂ g hg hh₁ hh₂) (relativeSquareIdealTranspose h₁ h₂ g hg hh₁ hh₂)
    ((modulePushforwardCompIsoOfEq (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h₁)
      (relativeMap_comp_of_comp_eq g hg)).hom.app _) ?hc ?H₁ ?H₂
  case hc =>
    exact restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_eq_eqToHom_comp
      (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
      (D.relativeSquareSituation.relativeMap h₁) (relativeMap_comp_of_comp_eq g hg) _
  case H₂ =>
    apply ThickeningTargetMorphism.homEquiv_comp_map_eq_comp_of_heq
    case hcube => exact relativeSquareIdealMap_reduction h₁ h₂ g hg hh₁ hh₂
    case eA₁ => rfl
    case eA₂ => rfl
    case eB₁ => rfl
    case eB₂ => rfl
    case eB'₂ => rfl
    case ha₁ => rfl
    case ha₂ => rfl
    case hw₁ => exact HEq.rfl
    case hw₂ => exact HEq.rfl
    case hm =>
      refine HEq.trans ?_ (heq_of_eq (relativeSquareIdealMap_eq h₁ h₂ g hg hh₁ hh₂).symm)
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) HEq.rfl ?_
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) ?_ HEq.rfl
      exact toRingedToposModulesHom_pullbackModules_map_heq rfl HEq.rfl
        (toRingedToposModulesHom_pullbackModules_obj_idealOfThickening_heq rfl rfl HEq.rfl _ _ _ _
          HEq.rfl)
        (toRingedToposModulesHom_pullbackModules_obj_idealOfThickening_heq rfl rfl HEq.rfl _ _ _ _
          HEq.rfl)
        HEq.rfl
    case hν =>
      refine HEq.trans ?_ (heq_of_eq (relativeSquareIdealTranspose_eq h₁ h₂ g hg hh₁ hh₂).symm)
      unfold cubeIdealTranspose isoConjugateMap
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) HEq.rfl ?_
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) HEq.rfl ?_
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) HEq.rfl ?_
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) HEq.rfl ?_
      refine CategoryTheory.Functor.map_heq_map _ (by rfl) (by rfl) ?_
      refine CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) HEq.rfl ?_
      exact CategoryTheory.comp_heq_comp (by rfl) (by rfl) (by rfl) HEq.rfl HEq.rfl
    case c₀ =>
      exact (modulePushforwardCompIsoOfEq (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h₁)
        (relativeMap_comp_of_comp_eq g hg)).hom.app _
    case hc => exact HEq.rfl
    case hc₀ => rfl
  case H₁ =>
    exact relativeSquareIdealTranspose_comp_map_eq_comp_unitStructureMap h₁ h₂ g hg hh₁ hh₂ H₁

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₁.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)] in
/-- **The ideal-square compatibility of `λ` from the ideal maps, for all affine first order
thickenings.** The property
`AlgebraicGeometry.Space.CoherentSituation.RelativeIdealSquareCompatibleOfIdealMaps` holds for `D`:
`AlgebraicGeometry.Space.CoherentSituation.relativeIdealSquareCompatible_of_comp_idealMap` holds at
each morphism of affine first order thickenings. -/
theorem relativeIdealSquareCompatible_of_idealMaps (D : CoherentSituation B S hS) :
    RelativeIdealSquareCompatibleOfIdealMaps D :=
  fun h₁ h₂ g hg hh₁ hh₂ _ _ _ hfl₁ hfl₂ H =>
    relativeIdealSquareCompatible_of_comp_idealMap h₁ h₂ g hg hh₁ hh₂ hfl₁ hfl₂ H

end AlgebraicGeometry.Space.CoherentSituation
