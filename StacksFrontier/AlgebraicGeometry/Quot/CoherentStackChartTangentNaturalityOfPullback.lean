module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentNaturality

/-!
# Naturality of the tangent identification over a chart, from the generic pullback of differences

Let `x = (Spec A, ℱ)` be an object of `Coh_{X/B}` over a chart, with `Y` final and `X → B` flat,
and `f : M ⟶ N` a map of modules. The test thickenings `Spec A ⊂ Spec A[M]` and
`Spec A ⊂ Spec A[N]` are split by the retractions `Spec A[M] ⟶ Spec A`, `Spec A[N] ⟶ Spec A`,
which are compatible with `Spec A[N] ⟶ Spec A[M]`
(`thickeningTestSchemeMap_comp_thickeningTestRetraction`), and both test schemes are flat over
`Y`. So the naturality of the difference from the trivial lift along any morphism of split first
order thickenings compatible with the retractions gives its naturality along
`Spec A[N] ⟶ Spec A[M]` (`TangentLiftDifferencePullback`), and hence the naturality of the tangent
identification `T_x(M) ≃ Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)` in `M`.

This is the naturality of the tangent spaces in the second proof of Stacks 08WA. The naturality
along a general morphism of split thickenings is the hypothesis `hgen` here, in the shape of
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback`.

## Main results

* `thickeningLiftDifference_pullback_thickeningTestSchemeMap`: the naturality of the difference
  from the trivial lift along `Spec A[N] ⟶ Spec A[M]`, for any `Ext` structures.
* `tangentLiftDifferencePullback_of_pullback`: the same, with the `Ext` groups of
  `tangentLiftDifference`.
* `chartTangentEquiv_map`: the naturality of the tangent identification in `M`.

## Implementation notes

As in `AlgebraicGeometry.Space.CoherentSituation.tangentLiftDifference_pullback`, the `Ext`
structures are carried as variables and the body of
`AlgebraicGeometry.Space.CoherentSituation.TangentLiftDifferencePullback` is crossed with
`with_reducible`.

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

/-- **The difference from the trivial lift is natural along `Spec A[N] ⟶ Spec A[M]`**, for any
`Ext` structures, from its naturality along morphisms of split first order thickenings
compatible with the retractions (`hgen`, the shape of
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback`): the retractions
of `Spec A ⊂ Spec A[M]` and `Spec A ⊂ Spec A[N]` are compatible with `Spec A[N] ⟶ Spec A[M]`
(`thickeningTestSchemeMap_comp_thickeningTestRetraction`), and both test schemes are flat over
`Y`. -/
theorem thickeningLiftDifference_pullback_thickeningTestSchemeMap
    (hgen : ∀ {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
      (r : T' ⟶ ξ.T) (hr : h ≫ r = 𝟙 ξ.T)
      (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
      (hfl : IsFlat B S hS (D.projection T').hom)
      (r₂ : T'₂ ⟶ ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
      (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
      (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
      (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (_ : r₂ = g ≫ r)
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]
      (c : D.ThickeningLiftClass ξ h),
      thickeningLiftDifference h₂ r₂ hr₂ hh₂ hfl₂ (ThickeningLiftClass.pullback g hg c) =
        (thickeningLiftDifference h r hr hh hfl c).comp
          (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1))
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
  hgen (thickeningTestRetraction hY hx M) (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
    (D.isFirstOrderThickening_thickeningTestMap hY x hx
      (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
    (D.isFlat_projection_of_isFlat hflat _)
    (thickeningTestRetraction hY hx N) (thickeningTestMap_comp_thickeningTestRetraction hY hx N)
    (D.isFirstOrderThickening_thickeningTestMap hY x hx
      (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))
    (D.isFlat_projection_of_isFlat hflat _)
    (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
      (hS := hS) (toS := toS) (hA := hA) f))
    (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
      (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
        (hA := hA) f))
    (thickeningTestSchemeMap_comp_thickeningTestRetraction hY hx f) c

end Generic

/-- **The difference from the trivial lift is natural along `Spec A[N] ⟶ Spec A[M]`**, with the
`Ext` groups of `AlgebraicGeometry.Space.CoherentSituation.tangentLiftDifference`, from its
naturality along morphisms of split first order thickenings compatible with the retractions
(`hgen`, the shape of
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback`). -/
theorem tangentLiftDifferencePullback_of_pullback {M N : Deformation.Artin.SiteModule A B}
    (f : M ⟶ N)
    (hgen : ∀ {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
      (r : T' ⟶ ξ.T) (hr : h ≫ r = 𝟙 ξ.T)
      (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
      (hfl : IsFlat B S hS (D.projection T').hom)
      (r₂ : T'₂ ⟶ ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
      (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
      (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
      (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (_ : r₂ = g ≫ r)
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]
      (c : D.ThickeningLiftClass ξ h),
      thickeningLiftDifference h₂ r₂ hr₂ hh₂ hfl₂ (ThickeningLiftClass.pullback g hg c) =
        (thickeningLiftDifference h r hr hh hfl c).comp
          (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1)) :
    TangentLiftDifferencePullback hY hx hflat f := by
  delta TangentLiftDifferencePullback
  intro c
  with_reducible
    exact thickeningLiftDifference_pullback_thickeningTestSchemeMap hY hx hflat f hgen c

variable (hRS : Deformation.Artin.SatisfiesRSStar B S hS (coherentCFG D).val.p (coherentCFG D).2)

/-- **The tangent identification is natural along a map of modules**: the image of a tangent
vector under `f : M ⟶ N` goes to its class in `Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)` followed by `f`, from
the naturality of the difference from the trivial lift along morphisms of split first order
thickenings compatible with the retractions (`hgen`, the shape of
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback`). -/
theorem chartTangentEquiv_map {M N : Deformation.Artin.SiteModule A B} (f : M ⟶ N)
    (hgen : ∀ {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
      (r : T' ⟶ ξ.T) (hr : h ≫ r = 𝟙 ξ.T)
      (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
      (hfl : IsFlat B S hS (D.projection T').hom)
      (r₂ : T'₂ ⟶ ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
      (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
      (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
      (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) (_ : r₂ = g ≫ r)
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
      [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]
      (c : D.ThickeningLiftClass ξ h),
      thickeningLiftDifference h₂ r₂ hr₂ hh₂ hfl₂ (ThickeningLiftClass.pullback g hg c) =
        (thickeningLiftDifference h r hr hh hfl c).comp
          (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1))
    (t : (Deformation.Artin.tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx
      (coherentCFG D).2 hRS).functor.obj M) :
    chartTangentEquiv hY hx N hflat hRS
        ((Deformation.Artin.tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx
          (coherentCFG D).2 hRS).functor.map f t) =
      D.extGroupMap x (D.chartRingEquiv x hx) f.hom 1 (chartTangentEquiv hY hx M hflat hRS t) :=
  chartTangentEquiv_map_of_tangentLiftDifferencePullback hY hx hflat hRS f
    (tangentLiftDifferencePullback_of_pullback hY hx hflat f hgen) t

end AlgebraicGeometry.Space.CoherentSituation

end
