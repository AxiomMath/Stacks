module

public import
  StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackKernelIdentification
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackTrivial

/-!
# The kernel square of the pullback unit

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` and `h₂ : T ⟶ T'₂`
first order thickenings, and `g : T'₂ ⟶ T'` a morphism under `T`. This file defines the kernel
and quotient maps of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` and proves that the unit, on the
extensions attached to a lift and to its pullback, restricts on the kernels to the kernel map.
For retractions `r`, `r₂ = g ≫ r` it states the condition that the kernel map, read on `X_T`, is
the map `λ_g` of coefficient modules.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftPullbackKernelMap`: the kernel map of
  the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftPullbackQuotientMap`: the quotient map
  of the unit, `i_*𝒢 ≅ Ψ₀ i₂_*𝒢 ≅ (X_g)_* i₂_*𝒢`.
* `AlgebraicGeometry.Space.CoherentSituation.retractionPushforwardCompIso`: `ρ_*(X_g)_* ≅ ρ₂_*`
  for the retractions `ρ = X_r` and `ρ₂ = X_{r₂}`.
* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLiftPullbackKernelCompatible`: the kernel
  map, read on `X_T`, is `λ_g`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_f_comp_pullbackUnit_eq`: the
  kernel square of the unit, with the kernel map.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

-- Below priority 10000, typeclass search for
-- `(smallEtaleRingedTopos X).J.HasSheafCompose (forget RingCat)` exceeds 1000 heartbeats.
attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat

universe e u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y}
  {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)

/-- **The kernel map of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`**: on the kernels `I ⊗ i_*𝒢` and
`I₂ ⊗ i₂_*𝒢`, `I ⊗ (i_*𝒢 ≅ Ψ₀ i₂_*𝒢)` followed by the comparison of the map of square-zero ideals
(`Deformation.ToposThickening.ThickeningTargetMorphism.restrictIdealTensorMapOver`). -/
abbrev thickeningLiftPullbackKernelMap :=
  (smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
      (relativeMap_comp_of_comp_eq g hg)).restrictIdealTensorMapOver
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
    (F₁ := (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h))).obj ξ.F)
    (F₂ := (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F)
    ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
      (relativeMap_comp_of_comp_eq g hg)).inv.app ξ.F)

/-- **The quotient map of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`**: `i_*𝒢 ≅ Ψ₀ i₂_*𝒢 ≅ (X_g)_* i₂_*𝒢`. -/
abbrev thickeningLiftPullbackQuotientMap :=
  (structureRestrict (smallEtaleRingedToposHom B S hS
    (D.relativeSquareSituation.relativeMap h))).map
      ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
        (relativeMap_comp_of_comp_eq g hg)).inv.app ξ.F) ≫
    ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
      (relativeMap_comp_of_comp_eq g hg)).restrictIso
      ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F)).inv


/-- **The kernel square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`**, with the kernel map
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftPullbackKernelMap`. -/
theorem thickeningLiftExtension_f_comp_pullbackUnit_eq (L : D.ThickeningLift ξ h) :
    type_of% ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
      (relativeMap_comp_of_comp_eq g hg)).f_comp_eq_restrictIdealTensorMapOver_comp
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
      (F₁ := (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h))).obj ξ.F)
      (F₂ := (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F)
      ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
        (relativeMap_comp_of_comp_eq g hg)).inv.app ξ.F)
      (thickeningLiftExtension h hh L) (extensionActionMap_thickeningLiftExtension hh L)
      (thickeningLiftExtension h₂ hh₂ (L.pullback g hg))
      (extensionActionMap_thickeningLiftExtension hh₂ (L.pullback g hg))
      (thickeningLiftPullbackUnit hh hh₂ g hg L)
      (thickeningLiftPullbackUnit_comp_map_g_comp_restrictIso_hom hh hh₂ g hg L)) :=
  (smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
      (relativeMap_comp_of_comp_eq g hg)).f_comp_eq_restrictIdealTensorMapOver_comp
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
    (F₁ := (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h))).obj ξ.F)
    (F₂ := (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F) _ _
    (extensionActionMap_thickeningLiftExtension hh L) _
    (extensionActionMap_thickeningLiftExtension hh₂ (L.pullback g hg)) _
    (thickeningLiftPullbackUnit_comp_map_g_comp_restrictIso_hom hh hh₂ g hg L)


variable {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hgr : r₂ = g ≫ r)

/-- `ρ_*(X_g)_* ≅ ρ₂_*` for the retractions `ρ = X_r` and `ρ₂ = X_{r₂}`, `r₂ = g ≫ r`. -/
abbrev retractionPushforwardCompIso :=
  pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap g)
      (D.relativeSquareSituation.relativeMap r) ≪≫
    eqToIso (congrArg (fun x : D.relativeSquareSituation.space T'₂ ⟶
        D.relativeSquareSituation.space ξ.T =>
      (smallEtaleRingedToposHom B S hS x).pushforwardModules) (relativeMap_comp_of_eq_comp g hgr))

variable (hfl : IsFlat B S hS (D.projection T').hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]

/-- **The kernel map of the unit, read on `X_T`, is `λ_g`**: through `ρ_*(X_g)_* ≅ ρ₂_*` and the
identifications `ρ_*(I ⊗ i_*𝒢) ≅ 𝒢 ⊗ f_T^*𝒥` of the kernels, `ρ_*` of the kernel map is the map
`AlgebraicGeometry.Space.CoherentSituation.thickeningCoefficientMap` of coefficient modules. -/
structure ThickeningLiftPullbackKernelCompatible : Prop where
  /-- The kernel map read on `X_T`. -/
  comp_eq :
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map
        (thickeningLiftPullbackKernelMap hh hh₂ g hg) ≫
      (retractionPushforwardCompIso g hgr).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj (thickeningKernel h₂ hh₂ hfl₂)) =
    (thickeningKernelRetractionIso h r hr hh hfl).hom ≫ thickeningCoefficientMap g hg hh hh₂ ≫
      (thickeningKernelRetractionIso h₂ r₂ hr₂ hh₂ hfl₂).inv


end AlgebraicGeometry.Space.CoherentSituation

end
