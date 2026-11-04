module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartData
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAxiomHelpers.CoherentTangentLiftClasses
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.DifferenceExt
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.CoefficientMap
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartCoefficientNaturality

/-!
# The tangent identification `T_x(M) ≃ Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)` over a chart

Let `x = (Spec A, ℱ)` be an object of `Coh_{X/B}` over a chart, with `X → B` flat. A lift of
`x` to the trivial square-zero extension `A[M]` is a lift of `ℱ` across
`X_A ⊂ X_{A[M]}`; the retraction `Spec A[M] ⟶ Spec A` gives the trivial lift, and the difference
from it in the principal homogeneous structure of Stacks 08VW, part (2), is a class in
`Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)`. This is the identification `T_x(M) = Ext¹(ℱ, ℱ ⊗ f^*M̃)` used in the
second proof of Stacks 08WA.

This module is a helper and carries no `@[stacks]` attribute.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.thickeningTestRetraction`: the retraction
  `Spec A[M] ⟶ Spec A` as a morphism of test schemes.
* `AlgebraicGeometry.Space.CoherentSituation.tangentLiftDifference`: the bijection between lift
  classes of `ℱ` to `X_{A[M]}` and `Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)`.
* `AlgebraicGeometry.Space.CoherentSituation.chartTangentEquiv`: the tangent identification.
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
  (M : Deformation.Artin.SiteModule A B)

/-- **The retraction `Spec A[M] ⟶ Spec A`**, as a morphism of test schemes over a final `Y`. -/
def thickeningTestRetraction :
    D.thickeningTestScheme hY
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M) ⟶ x.T :=
  CostructuredArrow.homMk (Deformation.Artin.squareZeroRetraction A B S hS toS hA M ≫
    eqToHom hx.symm) (hY.hom_ext _ _)

/-- The retraction is a retraction of `Spec A ⊂ Spec A[M]`. -/
theorem thickeningTestMap_comp_thickeningTestRetraction :
    D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M) ≫
      thickeningTestRetraction hY hx M = 𝟙 x.T := by
  apply CostructuredArrow.hom_ext
  show (eqToHom hx ≫ Deformation.Artin.squareZeroArrow A B S hS toS hA M) ≫
    Deformation.Artin.squareZeroRetraction A B S hS toS hA M ≫ eqToHom hx.symm = 𝟙 _
  rw [Category.assoc, ← Category.assoc (Deformation.Artin.squareZeroArrow A B S hS toS hA M),
    Deformation.Artin.squareZeroArrow_comp_squareZeroRetraction, Category.id_comp,
    eqToHom_trans, eqToHom_refl]

/-- The retractions are compatible with the morphism `Spec A[N] ⟶ Spec A[M]` of a module map
`M ⟶ N`. -/
theorem thickeningTestSchemeMap_comp_thickeningTestRetraction
    {M N : Deformation.Artin.SiteModule A B} (f : M ⟶ N) :
    thickeningTestRetraction hY hx N =
      D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
        (hS := hS) (toS := toS) (hA := hA) f) ≫ thickeningTestRetraction hY hx M := by
  apply CostructuredArrow.hom_ext
  show Deformation.Artin.squareZeroRetraction A B S hS toS hA N ≫ eqToHom hx.symm =
    Deformation.Artin.squareZeroOverMap A B S hS toS f ≫
      Deformation.Artin.squareZeroRetraction A B S hS toS hA M ≫ eqToHom hx.symm
  rw [← Category.assoc, Deformation.Artin.squareZeroOverMap_comp_squareZeroRetraction]

section Transport

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)]
  [HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O))]
  [HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)]

/-- `Ext¹(𝒢, 𝒢 ⊗ f_T^*𝒥) ≃ Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)` for the thickening `Spec A ⊂ Spec A[M]`,
through the identification of coefficients `p^*t^*𝒥 ⊗ ℱ ≅ ℱ ⊗ p^*M̃`. -/
def tangentExtTransport (M : Deformation.Artin.SiteModule A B) :
    Abelian.Ext.{u + 1} (objectToposModule x) (thickeningCoefficient x
        (D.thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))) 1 ≃
      D.extGroup x (D.chartRingEquiv x hx) M.obj 1 :=
  (extCompIsoAddEquiv (tangentCoefficientIso hY hx M) 1).toEquiv.trans
    (D.extGroupAbelianExtEquiv x (D.chartRingEquiv x hx) M.obj 1).symm.toEquiv

variable {M N : Deformation.Artin.SiteModule A B} (fMN : M ⟶ N)

/-- **The transport of `Ext` classes is natural in the module.** -/
theorem tangentExtTransport_comp_mk₀ (z : Abelian.Ext.{u + 1} (objectToposModule x)
    (thickeningCoefficient x (D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
      (D.isFirstOrderThickening_thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))) 1) :
    tangentExtTransport hY hx N (z.comp (Abelian.Ext.mk₀ (thickeningCoefficientMap
        (D.thickeningTestSchemeMap hY (Deformation.Artin.squareZeroModuleThickeningHom (S := S)
          (hS := hS) (toS := toS) (hA := hA) fMN))
        (thickeningTestMap_comp_thickeningTestSchemeMap (hx := hx) hY
          (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
            (hA := hA) fMN))
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) N))))
        (add_zero 1)) =
      D.extGroupMap x (D.chartRingEquiv x hx) fMN.hom 1 (tangentExtTransport hY hx M z) := by
  apply (D.extGroupAbelianExtEquiv x (D.chartRingEquiv x hx) N.obj 1).injective
  refine (Eq.trans ?_
    (D.extGroupAbelianExtEquiv_extGroupMap x (D.chartRingEquiv x hx) fMN.hom 1 _).symm)
  refine (AddEquiv.apply_symm_apply _ _).trans (Eq.trans ?_ (congrArg (fun w => Abelian.Ext.comp w
    (Abelian.Ext.mk₀ (D.extCoefficientModuleMap x (D.chartRingEquiv x hx) fMN.hom)) (add_zero 1))
    (AddEquiv.apply_symm_apply _ _)).symm)
  exact Abelian.Ext.comp_mk₀_comp_mk₀_of_comp_eq z _ _ _ _
    ((eq_whisker (thickeningCoefficientMap_thickeningTestSchemeMap_eq hY hx
        (Deformation.Artin.squareZeroModuleThickeningHom (S := S) (hS := hS) (toS := toS)
          (hA := hA) fMN)) _).trans <|
      (tangentCoefficientIso_hom_naturality hY hx fMN).trans
      (congrArg ((tangentCoefficientIso hY hx M).hom ≫ ·)
        (sheafTensor_map_eq_extCoefficientModuleMap hx fMN.hom)))

end Transport

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)] (hflat : IsFlat B S hS D.f.hom)

/-- **The difference from the trivial lift, on `X_A`**: the bijection between the classes of
lifts of `ℱ` to `X_{A[M]}` and `Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)`. -/
def tangentLiftDifference :
    D.ThickeningLiftClass x (D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)) ≃
      D.extGroup x (D.chartRingEquiv x hx) M.obj 1 :=
  haveI := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap (D.thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)))
  haveI := HasExt.standard (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space
      (D.thickeningTestScheme hY
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M)))).O))
  haveI := HasExt.standard (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2)
  letI : HasExt.{u + 1} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x.T)).O)) :=
    inferInstanceAs (HasExt.{u + 1} (Modules.{u, u} B S hS (D.space x.T).1 (D.space x.T).2))
  (thickeningLiftDifference _ (thickeningTestRetraction hY hx M)
      (thickeningTestMap_comp_thickeningTestRetraction hY hx M)
      (D.isFirstOrderThickening_thickeningTestMap hY x hx
        (Deformation.Artin.squareZeroModuleThickening (toS := toS) (hA := hA) M))
      (D.isFlat_projection_of_isFlat hflat _)).trans (tangentExtTransport hY hx M)

variable (hRS : Deformation.Artin.SatisfiesRSStar B S hS (coherentCFG D).val.p (coherentCFG D).2)

/-- **The tangent identification `T_x(M) ≃ Ext¹_{X_A}(ℱ, ℱ ⊗ f^*M̃)`** at an object of
`Coh_{X/B}` over a chart, for `X → B` flat: a tangent vector is a class of lifts of `x` to
`A[M]`, that is a class of lifts of `ℱ` to `X_{A[M]}`, and it goes to its difference from the
trivial lift. -/
def chartTangentEquiv :
    ((Deformation.Artin.tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx
        (coherentCFG D).2 hRS).functor.obj M : Type _) ≃
      D.extGroup x (D.chartRingEquiv x hx) M.obj 1 :=
  ((Deformation.Artin.tangentFunctor A B S hS toS hA (coherentCFG D).val.p x hx
      (coherentCFG D).2 hRS).liftEquiv M).trans
    ((D.fiberLiftClassEquiv hY (b := eqToHom hx ≫
        Deformation.Artin.squareZeroArrow A B S hS toS hA M)).trans
      (tangentLiftDifference hY hx M hflat))




end AlgebraicGeometry.Space.CoherentSituation

end
