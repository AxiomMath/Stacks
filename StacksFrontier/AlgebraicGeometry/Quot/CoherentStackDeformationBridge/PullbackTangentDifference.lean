module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackLiftDifference
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentNaturality

/-!
# The difference from the trivial lift along `Spec A[N] ⟶ Spec A[M]`, from the kernel condition

Let `x = (Spec A, ℱ)` be an object of `Coh_{X/B}` over a chart, with `Y` final and `X → B` flat,
and `f : M ⟶ N` a map of modules. The difference from the trivial lift is natural along
`Spec A[N] ⟶ Spec A[M]`
(`AlgebraicGeometry.Space.CoherentSituation.TangentLiftDifferencePullback`) as soon as, for every
lift across `Spec A ⊂ Spec A[M]`, the kernel map of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` is the
coefficient map `λ_g` read on `X_A`
(`AlgebraicGeometry.Space.CoherentSituation.tangentLiftDifferencePullback_of_kernel`): this is
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback_of_kernel` at the
split thickenings `Spec A ⊂ Spec A[M]`, `Spec A ⊂ Spec A[N]` with their retractions.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  (hY : IsTerminal D.Y)
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : CoherentObject D}
  (hx : (coherentCFG D).val.p.obj x = Deformation.Artin.algebraOver A B S hS toS hA)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)] (hflat : IsFlat B S hS D.f.hom)

section Generic

variable {M N : Deformation.Artin.SiteModule A B} (f : M ⟶ N)
  {hePM : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))}
  {heTM : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space
      (D.thickeningTestScheme hY
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))).O))}
  {hePN : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))}
  {heTN : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space
      (D.thickeningTestScheme hY
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)))).O))}
  {heX : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O))}

/-- **The difference from the trivial lift along `Spec A[N] ⟶ Spec A[M]`**, for any `Ext`
structures, given the kernel condition `h₁` of
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback_of_kernel` at the
split thickenings `Spec A ⊂ Spec A[M]`, `Spec A ⊂ Spec A[N]` with their retractions. -/
theorem thickeningLiftDifference_pullback_thickeningTestSchemeMap_of_kernel
    (h₁ : ∀ (L : D.ThickeningLift x (D.thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))
        (τ₁ : (thickeningLiftShortComplex _ (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)) L).X₁ ⟶
          (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
            (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
              (hS := hS) (toS := toS) (hA := hA) f)))).pushforwardModules.obj
            (thickeningLiftShortComplex _ (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
              (L.pullback (D.thickeningTestSchemeMap hY
                  (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                    (hA := hA) f))
                (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
                  (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                    (hA := hA) f)))).X₁),
      (thickeningLiftShortComplex _ (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)) L).f ≫
          thickeningLiftPullbackUnit (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
            (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
              (hS := hS) (toS := toS) (hA := hA) f))
            (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
              (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                (hA := hA) f)) L =
        τ₁ ≫ (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
            (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
              (hS := hS) (toS := toS) (hA := hA) f)))).pushforwardModules.map
          (thickeningLiftShortComplex _ (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
            (L.pullback (D.thickeningTestSchemeMap hY
                (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                  (hA := hA) f))
              (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
                (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                  (hA := hA) f)))).f →
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
          (thickeningTestRetraction hY hx M))).pushforwardModules.map τ₁ ≫
          (retractionPushforwardCompIso
            (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
              (hS := hS) (toS := toS) (hA := hA) f))
            (thickeningTestSchemeMap_comp_thickeningTestRetraction hY hx f)).hom.app
            (thickeningLiftShortComplex _ (D.isFirstOrderThickening_thickeningTestMap hY x hx
                (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
              (L.pullback (D.thickeningTestSchemeMap hY
                  (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                    (hA := hA) f))
                (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
                  (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                    (hA := hA) f)))).X₁ =
        (thickeningLiftKernelIso (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
            (D.isFlat_projection_of_isFlat hflat _) L).hom ≫
          thickeningCoefficientMap
            (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
              (hS := hS) (toS := toS) (hA := hA) f))
            (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
              (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                (hA := hA) f))
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)) ≫
          (thickeningLiftKernelIso (thickeningTestMap_comp_thickeningTestRetraction hY hx N)
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
            (D.isFlat_projection_of_isFlat hflat _)
            (L.pullback (D.thickeningTestSchemeMap hY
                (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                  (hA := hA) f))
              (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
                (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                  (hA := hA) f)))).inv)
    (c : D.ThickeningLiftClass x (D.thickeningTestMap hY x hx
      (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))) :
    thickeningLiftDifference _ (thickeningTestRetraction hY hx N)
        (thickeningTestMap_comp_thickeningTestRetraction hY hx N)
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
        (D.isFlat_projection_of_isFlat hflat _)
        (ThickeningLiftClass.pullback (D.thickeningTestSchemeMap hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f))
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f)) c) =
      (thickeningLiftDifference _ (thickeningTestRetraction hY hx M)
          (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFlat_projection_of_isFlat hflat _) c).comp
        (Abelian.Ext.mk₀ (thickeningCoefficientMap
          (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
            (hS := hS) (toS := toS) (hA := hA) f))
          (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
            (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
              (hA := hA) f))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))))
        (add_zero 1) :=
  thickeningLiftDifference_pullback_of_kernel _ _ _ _
    (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
    (thickeningTestMap_comp_thickeningTestRetraction hY hx N)
    (thickeningTestSchemeMap_comp_thickeningTestRetraction hY hx f) _ _ h₁ c

end Generic

/-- **The difference from the trivial lift is natural along `Spec A[N] ⟶ Spec A[M]`**, given that
for every lift `L` across `Spec A ⊂ Spec A[M]` the kernel map of the unit (any map of kernels
making the kernel square commute) is the coefficient map read on `X_A` through the retractions
(`h₁`, the kernel condition of
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass_pullback`). -/
theorem tangentLiftDifferencePullback_of_thickeningTestKernel
    {M N : Deformation.Artin.SiteModule A B} (f : M ⟶ N)
    (h₁ : ∀ (L : D.ThickeningLift x (D.thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))
        (τ₁ : (thickeningLiftShortComplex _ (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)) L).X₁ ⟶
          (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
            (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
              (hS := hS) (toS := toS) (hA := hA) f)))).pushforwardModules.obj
            (thickeningLiftShortComplex _ (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
              (L.pullback (D.thickeningTestSchemeMap hY
                  (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                    (hA := hA) f))
                (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
                  (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                    (hA := hA) f)))).X₁),
      (thickeningLiftShortComplex _ (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)) L).f ≫
          thickeningLiftPullbackUnit (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
            (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
              (hS := hS) (toS := toS) (hA := hA) f))
            (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
              (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                (hA := hA) f)) L =
        τ₁ ≫ (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
            (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
              (hS := hS) (toS := toS) (hA := hA) f)))).pushforwardModules.map
          (thickeningLiftShortComplex _ (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
            (L.pullback (D.thickeningTestSchemeMap hY
                (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                  (hA := hA) f))
              (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
                (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                  (hA := hA) f)))).f →
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
          (thickeningTestRetraction hY hx M))).pushforwardModules.map τ₁ ≫
          (retractionPushforwardCompIso
            (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
              (hS := hS) (toS := toS) (hA := hA) f))
            (thickeningTestSchemeMap_comp_thickeningTestRetraction hY hx f)).hom.app
            (thickeningLiftShortComplex _ (D.isFirstOrderThickening_thickeningTestMap hY x hx
                (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
              (L.pullback (D.thickeningTestSchemeMap hY
                  (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                    (hA := hA) f))
                (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
                  (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                    (hA := hA) f)))).X₁ =
        (thickeningLiftKernelIso (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
            (D.isFlat_projection_of_isFlat hflat _) L).hom ≫
          thickeningCoefficientMap
            (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
              (hS := hS) (toS := toS) (hA := hA) f))
            (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
              (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                (hA := hA) f))
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N)) ≫
          (thickeningLiftKernelIso (thickeningTestMap_comp_thickeningTestRetraction hY hx N)
            (D.isFirstOrderThickening_thickeningTestMap hY x hx
              (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
            (D.isFlat_projection_of_isFlat hflat _)
            (L.pullback (D.thickeningTestSchemeMap hY
                (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                  (hA := hA) f))
              (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
                (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
                  (hA := hA) f)))).inv) :
    TangentLiftDifferencePullback hY hx hflat f := by
  delta TangentLiftDifferencePullback
  intro c
  with_reducible
    exact thickeningLiftDifference_pullback_thickeningTestSchemeMap_of_kernel hY hx hflat f h₁ c

end AlgebraicGeometry.Space.CoherentSituation

end
