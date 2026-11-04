module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleAffineUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointCoproducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelToPointPullback

/-!
# Affine base change for `𝒪_X ⊗_R M` on the spaces-étale models

Consider a cartesian square

```
X ---f---> T
|g          |j
v           v
X₀ --f₀--> T₀
```

of algebraic spaces with `T = Spec R` and `T₀ = Spec R₀` affine schemes. Then
`g_*(𝒪_X ⊗_R M) ≅ 𝒪_{X₀} ⊗_{R₀} M` naturally in the `R`-module `M`, where on the right `M` is
read as an `R₀`-module along `Γ(j) : R₀ ⟶ R`. On the small étale sites this is the chain

`g_*(𝒪_X ⊗_R M) ≅ g_*f^*(𝒪_T ⊗_R M) ≅ f₀^*j_*(𝒪_T ⊗_R M) ≅ f₀^*(𝒪_{T₀} ⊗_{R₀} M) ≅ 𝒪_{X₀} ⊗_{R₀} M`

of `AlgebraicGeometry.Space.baseRingTensorModulePullbackIso`, affine base change in degree zero
(Stacks 07U8, the base change map `AlgebraicGeometry.Space.moduleBaseChangeMap` being invertible
at the quasi-coherent `𝒪_T ⊗_R M`) and
`AlgebraicGeometry.Space.pushforwardBaseRingTensorIso`. It is read on the models of the
spaces-étale sites through the inverse images to points
(`AlgebraicGeometry.Space.pullbackToBaseRingIso`) and an identification of the direct images on
the models with the direct images on the small étale sites under the equivalences of Stacks 03G1.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardPullbackToBaseRingIsoOfComparison`: the isomorphism, given
  the identification of the direct images along `g` and the invertibility of the base change map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X₀ : AlgebraicSpaces B S hS} {T T₀ : BigFppfOver B S hS}

/-- **`g_*(𝒪_X ⊗_R M) ≅ 𝒪_{X₀} ⊗_{R₀} M` on the spaces-étale models**, naturally in the
`R`-module `M`, for a commutative square `X = X₀ ×_{T₀} T` over affine `T = Spec R` and
`T₀ = Spec R₀`, given an identification `eP` of the direct image along `g` on the models with
the one on the small étale sites, and the invertibility `hbc` of the base change map
`f₀^*j_*F ⟶ g_*f^*F` at quasi-coherent `F`. -/
def pushforwardPullbackToBaseRingIsoOfComparison
    (f : X ⟶ schemeSpace T) (f₀ : X₀ ⟶ schemeSpace T₀) (g : X ⟶ X₀) (j : T ⟶ T₀)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (w : f ≫ schemeSpaceMap j = g ≫ f₀)
    (eP : (spacesEtaleModelHom B S hS g).pushforwardTopos ⋙
        (spacesEtaleModelModulesEquiv B S hS X₀).functor ≅
      (spacesEtaleModelModulesEquiv B S hS X).functor ⋙ modulePushforward B S hS g)
    (hbc : ∀ F : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2,
      F.IsQuasicoherentOnSite → IsIso ((moduleBaseChangeMap (schemeSpaceMap j) f₀ g f w).app F)) :
    ((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos) ⋙
        (spacesEtaleModelHom B S hS g).pushforwardTopos ≅
      (ModuleCat.restrictScalars.{u} (baseRingMapOfHom T j) ⋙
        (baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse) ⋙
        (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)).pullbackTopos :=
  let e₀ := spacesEtaleModelModulesEquiv B S hS X₀
  let tT := baseRingTensorModule B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T)))
  let _tT₀ := baseRingTensorModule B S hS (schemeSpace T₀) (baseRingHomOfMap (𝟙 (schemeSpace T₀)))
  let r := ModuleCat.restrictScalars.{u} (baseRingMapOfHom T j)
  haveI : IsIso (Functor.whiskerLeft tT (moduleBaseChangeMap (schemeSpaceMap j) f₀ g f w)) :=
    haveI : ∀ M, IsIso ((Functor.whiskerLeft tT
        (moduleBaseChangeMap (schemeSpaceMap j) f₀ g f w)).app M) := fun M =>
      hbc _ (isQuasicoherentOnSite_baseRingTensorModule B S hS _ _ M)
    NatIso.isIso_of_isIso_app _
  let bc : tT ⋙ modulePushforward B S hS (schemeSpaceMap j) ⋙ modulePullback B S hS f₀ ≅
      tT ⋙ modulePullback B S hS f ⋙ modulePushforward B S hS g :=
    asIso (Functor.whiskerLeft tT (moduleBaseChangeMap (schemeSpaceMap j) f₀ g f w))
  let iso : (((baseRingPointModulesEquiv (R := baseRing B S hS T)).inverse ⋙
        (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f)).pullbackTopos) ⋙
        (spacesEtaleModelHom B S hS g).pushforwardTopos) ⋙ e₀.functor ≅
      ((r ⋙ (baseRingPointModulesEquiv (R := baseRing B S hS T₀)).inverse) ⋙
        (spacesEtaleModelToBaseRing B S hS X₀ (baseRingHomOfMap f₀)).pullbackTopos) ⋙
        e₀.functor :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eP ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackToBaseRingIso B S hS X (baseRingHomOfMap f)) _ ≪≫
      Functor.isoWhiskerRight (baseRingTensorModulePullbackIso B S hS f).symm _ ≪≫
      Functor.associator _ _ _ ≪≫ bc.symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardBaseRingTensorIso T j hT hT₀).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft r (baseRingTensorModulePullbackIso B S hS f₀) ≪≫
      Functor.isoWhiskerLeft r (pullbackToBaseRingIso B S hS X₀ (baseRingHomOfMap f₀)).symm
  ((e₀.fullyFaithfulFunctor.whiskeringRight (ModuleCat.{u} (baseRing B S hS T))).preimageIso iso)

end AlgebraicGeometry.Space

end
