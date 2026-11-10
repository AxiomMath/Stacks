module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackExtClass
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentN1b

/-!
# The class of a pulled-back lift on `X_T` (N1)

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'`, `h₂ : T ⟶ T'₂` split
first order thickenings with retractions `r`, `r₂ = g ≫ r` and `g : T'₂ ⟶ T'` under `T`. The class
on `X_T` of the pullback along `g` of a lift is the class of the lift followed by
`λ_g : 𝒢 ⊗ f_T^*𝒥 ⟶ 𝒢 ⊗ f_T^*𝒥₂`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass_pullback`), given that the
kernel map of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` is `λ_g` on `X_T`; hence so is the difference from
the trivial lift
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback_of_kernel`).
This is one application of
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass_eq_comp_of_hom` with the kernel
square
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_f_comp_pullbackUnit_eq_comp`,
the reduction square
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_g_comp_pullbackQuotientMap`
and the quotient square
`Space.CoherentSituation.map_pullbackQuotientMap_comp_hom_app_eq_thickeningLiftQuotientIso`.

This module is a helper and carries no `@[stacks]` attribute.

## Implementation notes

The kernel condition is taken for every map `τ₁` of kernels making the kernel square commute (there
is one, the kernel map of the unit), so that it is stated without spelling that map. The quotient
map of the unit is identified with the spelling of the quotient square by two heterogeneous
equalities, the second through `objectToposModule ξ = ξ.F` as an argument of a function
(`CategoryTheory.heq_apply_of_eq`): comparing the two composites directly does not finish within
the default budget.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
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

universe e u

namespace CategoryTheory

/-- Values of a dependent function at equal arguments are heterogeneously equal. -/
theorem heq_apply_of_eq {α : Sort*} {β : α → Sort*} (F : ∀ a, β a) {a b : α} (h : a = b) :
    HEq (F a) (F b) := by
  subst h
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y}
  {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
  {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hgr : r₂ = g ≫ r)
  (hfl : IsFlat B S hS (D.projection T').hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))] in
/-- The quotient map of the unit, as the composite through which it is defined. -/
theorem thickeningLiftPullbackQuotientMap_heq_comp_F :
    HEq (thickeningLiftPullbackQuotientMap g hg)
      ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h))).map
        ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).inv.app ξ.F) ≫
      ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F)).inv) :=
  HEq.rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))] in
/-- The composite of `thickeningLiftPullbackQuotientMap_heq_comp_F` at `objectToposModule ξ`
instead of `ξ.F`. -/
theorem thickeningLiftPullbackQuotientComp_heq_objectToposModule :
    HEq ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h))).map
        ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).inv.app ξ.F) ≫
      ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F)).inv)
      ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h))).map
        ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).inv.app (objectToposModule ξ)) ≫
      ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj (objectToposModule ξ))).inv) :=
  heq_apply_of_eq (fun M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O) =>
    (structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h))).map
        ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).inv.app M) ≫
      ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj M)).inv)
    (rfl : ξ.F = objectToposModule ξ)

include hgr in
omit [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
    [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))] in
/-- **The class on `X_T` of the pullback of a lift is the class of the lift followed by `λ_g`**,
given that the kernel map of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` (any map of kernels making the
kernel square commute) is `λ_g` read on `X_T` (`h₁`). -/
theorem thickeningLiftExtClass_pullback (L : D.ThickeningLift ξ h)
    (h₁ : ∀ τ₁ : (thickeningLiftShortComplex h hh L).X₁ ⟶
        (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
            (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).X₁,
      (thickeningLiftShortComplex h hh L).f ≫ thickeningLiftPullbackUnit hh hh₂ g hg L =
          τ₁ ≫ (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
              (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).f →
        (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map τ₁ ≫
            (retractionPushforwardCompIso g hgr).hom.app
              (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).X₁ =
          (thickeningLiftKernelIso hr hh hfl L).hom ≫ thickeningCoefficientMap g hg hh hh₂ ≫
            (thickeningLiftKernelIso hr₂ hh₂ hfl₂ (L.pullback g hg)).inv) :
    thickeningLiftExtClass h₂ r₂ hr₂ hh₂ hfl₂ (L.pullback g hg) =
      (thickeningLiftExtClass h r hr hh hfl L).comp
        (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1) :=
  thickeningLiftExtClass_eq_comp_of_hom hr hr₂ hh hh₂ hfl hfl₂ g
    (retractionPushforwardCompIso g hgr) L (L.pullback g hg)
    (thickeningCoefficientMap g hg hh hh₂) _ (thickeningLiftPullbackUnit hh hh₂ g hg L)
    (thickeningLiftPullbackQuotientMap g hg)
    (thickeningLiftExtension_f_comp_pullbackUnit_eq_comp hh hh₂ g hg L)
    (thickeningLiftExtension_g_comp_pullbackQuotientMap hh hh₂ g hg L)
    (h₁ _ (thickeningLiftExtension_f_comp_pullbackUnit_eq_comp hh hh₂ g hg L))
    (map_pullbackQuotientMap_comp_hom_app_eq_thickeningLiftQuotientIso hr hr₂ hh hh₂ g hg hgr L
      (retractionPushforwardCompIso g hgr) rfl (thickeningLiftPullbackQuotientMap g hg)
      (eq_of_heq ((thickeningLiftPullbackQuotientMap_heq_comp_F g hg).trans
        (thickeningLiftPullbackQuotientComp_heq_objectToposModule g hg))))

include hgr in
/-- **The difference from the trivial lift along `g` is the difference followed by `λ_g`**, given
the kernel condition of `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass_pullback`
for every lift (`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback`). -/
theorem thickeningLiftDifference_pullback_of_kernel
    (h₁ : ∀ (L : D.ThickeningLift ξ h) (τ₁ : (thickeningLiftShortComplex h hh L).X₁ ⟶
        (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.obj
            (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).X₁),
      (thickeningLiftShortComplex h hh L).f ≫ thickeningLiftPullbackUnit hh hh₂ g hg L =
          τ₁ ≫ (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
              (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).f →
        (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map τ₁ ≫
            (retractionPushforwardCompIso g hgr).hom.app
              (thickeningLiftShortComplex h₂ hh₂ (L.pullback g hg)).X₁ =
          (thickeningLiftKernelIso hr hh hfl L).hom ≫ thickeningCoefficientMap g hg hh hh₂ ≫
            (thickeningLiftKernelIso hr₂ hh₂ hfl₂ (L.pullback g hg)).inv)
    (c : D.ThickeningLiftClass ξ h) :
    thickeningLiftDifference h₂ r₂ hr₂ hh₂ hfl₂ (ThickeningLiftClass.pullback g hg c) =
      (thickeningLiftDifference h r hr hh hfl c).comp
        (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1) :=
  thickeningLiftDifference_pullback hr hr₂ hh hh₂ hfl hfl₂ g hg
    (fun L => thickeningLiftExtClass_pullback hh hh₂ g hg hr hr₂ hgr hfl hfl₂ L (h₁ L)) c

end AlgebraicGeometry.Space.CoherentSituation

end
