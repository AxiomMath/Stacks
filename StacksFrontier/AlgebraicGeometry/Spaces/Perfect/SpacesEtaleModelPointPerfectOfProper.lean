module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelAffineBaseChangeToPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointNoetherianModels
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelPushforwardComparison

/-!
# Perfectness of `RΓ` for proper flat morphisms of finite presentation, on the point

Let `f : X ⟶ T` be a proper, flat morphism of finite presentation of algebraic spaces with
`T = Spec R` affine. This file proves affine base change for `𝒪_X ⊗_R M` on the models of the
spaces-étale sites and with it removes that input from
`isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_noetherianModels`: `Rf_*E` is perfect
on the point `(pt, R)` for every perfect `E`, given the descent of perfect objects along limits of
algebraic spaces (the essential surjectivity half of Stacks 09RJ). The direct images on the models
are compared with those on the small étale sites by
`AlgebraicGeometry.Space.spacesEtaleModelModulesPushforwardIso` (Stacks 03G1).

## Main results

* `AlgebraicGeometry.Space.nonempty_pushforwardPullbackToBaseRingIso_of_isPullback`: for a
  cartesian square `X = X₀ ×_{T₀} T` over affines, `g_*(𝒪_X ⊗_R M) ≅ 𝒪_{X₀} ⊗_{R₀} M` on the
  models, naturally in `M`.
* `AlgebraicGeometry.Space.isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper`:
  the point form of Stacks 0CTM, given the descent of perfect objects.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}}

/-- **Affine base change for `𝒪_X ⊗_R M` on the spaces-étale models.** For a cartesian square
`X = X₀ ×_{T₀} T` of algebraic spaces over a morphism `j : T ⟶ T₀` of affine schemes,
`g_*(𝒪_X ⊗_R M) ≅ 𝒪_{X₀} ⊗_{R₀} M` naturally in the `R`-module `M`, with `M` read as an
`R₀`-module along `Γ(j)`: affine base change in degree zero (Stacks 07U8) at the quasi-coherent
`𝒪_T ⊗_R M`, read on the models through a comparison `eP` of the direct images along `g` under
the equivalences of Stacks 03G1. -/
theorem nonempty_pushforwardPullbackToBaseRingIso_of_isPullback {S : Scheme.{u}}
    {hS : B.Contains S} {X X₀ : AlgebraicSpaces B S hS} {T T₀ : BigFppfOver B S hS}
    (f : X ⟶ schemeSpace T) (f₀ : X₀ ⟶ schemeSpace T₀) (g : X ⟶ X₀) (j : T ⟶ T₀)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (sq : IsPullback g.hom f.hom f₀.hom (yoneda.map j))
    (eP : (spacesEtaleModelHom B S hS g).pushforwardTopos ⋙
        (spacesEtaleModelModulesEquiv B S hS X₀).functor ≅
      (spacesEtaleModelModulesEquiv B S hS X).functor ⋙ modulePushforward B S hS g) :
    Nonempty (((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos) ⋙
        (spacesEtaleModelHom B S hS g).pushforwardTopos ≅
      (ModuleCat.restrictScalars.{u} (baseRingMapOfHom T j) ⋙
        (baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse) ⋙
        (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)).pullbackTopos) := by
  have w : f ≫ schemeSpaceMap j = g ≫ f₀ := ObjectProperty.hom_ext _ sq.w.symm
  have hj : IsAffineHom B S hS (schemeSpaceMap j).hom := by
    have := hT
    have := hT₀
    exact isAffineHom_yoneda_map_of_isAffineHom _ inferInstance
  have sq' : IsPullback f g (schemeSpaceMap j) f₀ :=
    IsPullback.of_map (ObjectProperty.ι _) w sq.flip
  exact ⟨pushforwardPullbackToBaseRingIsoOfComparison f f₀ g j hT hT₀ sq'.w eP
    (isIso_moduleBaseChangeMap_app_of_isAffineHom sq' hj)⟩

section Perfect

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

/-- **The point form of Stacks 0CTM, given the descent of perfect objects.** Over any base scheme,
let `f : X ⟶ T` be proper, flat and of finite presentation with `T` affine. If perfect objects
descend along approximating systems over `Spec ℤ` (`hdescent`, the essential surjectivity half of
Stacks 09RJ), then `Rf_*E` is perfect on the point `(pt, Γ(T, 𝒪_T))` for every perfect `E`. -/
theorem isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hdescent : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I), ChartsBounded B _ hZ D.system →
      ∀ E : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).Modules,
        (spacesEtaleModelRingedTopos B _ hZ
          ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩).toRingedSite.IsPerfect E →
        ∃ (i : I) (_ : D.base ≤ i) (Eᵢ : DerivedCategory (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).Modules),
          (spacesEtaleModelRingedTopos B _ hZ
            ⟨D.system.obj (op i), D.algebraicSpace i⟩).toRingedSite.IsPerfect Eᵢ ∧
          Nonempty ((derivedPullback (spacesEtaleModelHom B _ hZ
            (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B _ hZ) ⟶
                ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ≅ E))
    {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (f : X ⟶ schemeSpace T) (hf : IsProper B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (hflat : IsFlat B S hS f.hom)
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E) :=
  isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_noetherianModels hZ hdescent
    (fun _ _ _ _ f f₀ g j hT hT₀ sq =>
      nonempty_pushforwardPullbackToBaseRingIso_of_isPullback f f₀ g j hT hT₀ sq
        (spacesEtaleModelModulesPushforwardIso B _ hZ g))
    hT f hf hfp hflat E hE

end Perfect

end AlgebraicGeometry.Space

end
