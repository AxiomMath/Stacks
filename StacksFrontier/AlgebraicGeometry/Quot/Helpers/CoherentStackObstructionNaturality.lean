module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartObstruction
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.Pullback
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleObstructionDescentNaturality

/-!
# The obstruction to lifting an object of `Coh_{X/B}`, as a descended class of Stacks 08MF

For an object `ξ = (T, 𝒢)` of `Coh_{X/Y}` and a first order thickening `h : T ⟶ T'` with
`X_{T'} ⟶ T'` flat, the obstruction of Stacks 08VW, part (1), on `X_T`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningObstructionOnBase`) is the class
`o(i_*𝒢, i_*(f̃^*t̃^*𝒥̃) ⊗ i_*𝒢, 1)` of Stacks 08MF descended along `i : X_T ⊂ X_{T'}`. This file
records that identification in the spelling of
`Deformation.ToposThickening.thickenedModulesFunctor` and with the universe levels of the descent
written out, which is the form taken by the naturality of these classes along a morphism of
thickenings (Stacks 0CYF), `Deformation.ToposThickening.ThickeningTargetMorphism.`
`extDescentAddEquiv_symm_existenceObstructionClass_basePullbackIdeal`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.`
  `thickeningLiftObstruction_eq_existenceObstructionClass`.
* `AlgebraicGeometry.Space.CoherentSituation.`
  `thickeningObstructionOnBase_eq_extDescentAddEquiv_symm`.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe e e' u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

section Bridge

variable {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hfl : IsFlat B S hS (D.projection T').hom)
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
  [HasExt.{e'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]

omit [HasExt.{e'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))] in
include hh hfl in
/-- **The class of Stacks 08VW, part (1), in the spelling of
`Deformation.ToposThickening.thickenedModulesFunctor`.** -/
theorem thickeningLiftObstruction_eq_existenceObstructionClass :
    thickeningLiftObstruction.{e} h hh hfl =
      existenceObstructionClass.{u, u + 1, u, u, u + 1, u, e}
        (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h))).obj (objectToposModule ξ)) _
        (basePullbackIdealTensorIso
          (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
          (D.relativeSquareSituation.relativeSquareThickening h)
          (D.relativeSquareSituation.relativeSquareLeft h)
          (relBaseRight (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.projection T')))
          (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
          (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
          (D.relativeSquareSituation.relativeSquare_comm h)
          (isFlat_relBaseRight_smallEtaleRingedToposHom _ hfl)
          (D.relativeSquareSituation.isStrict_relativeSquare h hh)
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h))).obj (objectToposModule ξ))).inv :=
  rfl

include hh hfl in
/-- **The obstruction on `X_T` is the class of Stacks 08VW, part (1), descended along
`X_T ⊂ X_{T'}`**, with the universe levels of `Deformation.ToposThickening.extDescentAddEquiv`
written out. -/
theorem thickeningObstructionOnBase_eq_extDescentAddEquiv_symm :
    thickeningObstructionOnBase.{e, e'} h hh hfl =
      (extDescentAddEquiv.{u, u + 1, u, u + 1, u, e', e}
        (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
        (objectToposModule ξ) (D.relativeSquareSituation.relativeSquareBasePullbackIdeal h hh)
          2).symm (thickeningLiftObstruction.{e} h hh hfl) :=
  rfl

end Bridge

section Instances

variable {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')

/-! The sites of the bases of the relative squares are the small étale site of `X_{T'}`; instance
search reaches its sheaf compositions through `Deformation.ToposThickening.relBaseTop` and
`Deformation.ToposThickening.relBaseBottom` only slowly, so they are recorded here. -/

/-- The topology of `relBaseTop` for the projection `X_{T'} ⟶ T'`, the small étale topology of
`X_{T'}`, has sheaf composition along the forgetful functor of rings. -/
theorem relBaseTop_hasSheafCompose_forget_ringCat :
    (relBaseTop (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.projection T'))).J.HasSheafCompose (forget RingCat.{u}) :=
  inferInstanceAs
    ((SmallEtale.topology B S hS (D.relativeSquareSituation.space T').1).HasSheafCompose
      (forget RingCat.{u}))

/-- The topology of `relBaseTop` for the projection `X_{T'} ⟶ T'` has sheaf composition along the
forgetful functor from commutative rings to rings. -/
theorem relBaseTop_hasSheafCompose_forget₂_commRingCat :
    (relBaseTop (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.projection T'))).J.HasSheafCompose
        (forget₂ CommRingCat.{u} RingCat.{u}) :=
  inferInstanceAs
    ((SmallEtale.topology B S hS (D.relativeSquareSituation.space T').1).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}))

/-- The topology of `relBaseTop` for the projection `X_{T'} ⟶ T'` has sheaf composition along the
forgetful functor of abelian groups. -/
theorem relBaseTop_hasSheafCompose_forget_addCommGrpCat :
    (relBaseTop (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.projection T'))).J.HasSheafCompose (forget AddCommGrpCat.{u}) :=
  inferInstanceAs
    ((SmallEtale.topology B S hS (D.relativeSquareSituation.space T').1).HasSheafCompose
      (forget AddCommGrpCat.{u}))

/-- The topology of `relBaseBottom` for `h` and the projection `X_{T'} ⟶ T'`, the small étale
topology of `X_{T'}`, has sheaf composition along the forgetful functor of rings. -/
theorem relBaseBottom_hasSheafCompose_forget_ringCat :
    (relBaseBottom (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'))).J.HasSheafCompose
        (forget RingCat.{u}) :=
  inferInstanceAs
    ((SmallEtale.topology B S hS (D.relativeSquareSituation.space T').1).HasSheafCompose
      (forget RingCat.{u}))

/-- The topology of `relBaseBottom` for `h` and the projection `X_{T'} ⟶ T'` has sheaf composition
along the forgetful functor from commutative rings to rings. -/
theorem relBaseBottom_hasSheafCompose_forget₂_commRingCat :
    (relBaseBottom (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T'))).J.HasSheafCompose
        (forget₂ CommRingCat.{u} RingCat.{u}) :=
  inferInstanceAs
    ((SmallEtale.topology B S hS (D.relativeSquareSituation.space T').1).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}))

end Instances

-- Local priority 10000: instance search reaches these through `relBaseTop`/`relBaseBottom` slowly.
attribute [local instance 10000] relBaseTop_hasSheafCompose_forget_ringCat
  relBaseTop_hasSheafCompose_forget₂_commRingCat relBaseTop_hasSheafCompose_forget_addCommGrpCat
  relBaseBottom_hasSheafCompose_forget_ringCat relBaseBottom_hasSheafCompose_forget₂_commRingCat

section Naturality

variable {ξ : CoherentObject D} {T'₁ T'₂ : SchemesOver D.Y} (h₁ : ξ.T ⟶ T'₁) (h₂ : ξ.T ⟶ T'₂)
  (g : T'₂ ⟶ T'₁) (hg : h₂ ≫ g = h₁)
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (hhg : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map g.left))
  (hfl₁ : IsFlat B S hS (D.projection T'₁).hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₁)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₁)).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
  [HasExt.{e'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]

/-- The morphism of thickened small étale ringed topoi of `X_g : X_{T'₂} ⟶ X_{T'₁}`, relating
those of `X_{h₁}` and `X_{h₂}`. -/
abbrev relativeThickeningTarget :=
  smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
    (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h₁)
    (relativeMap_comp_of_comp_eq g hg)

/-- **The ideal-square compatibility for `X_{T'₂} ⟶ X_{T'₁}`** of a map
`λ : f̃₁^*t̃₁^*𝒥̃₁ ⟶ f̃₂^*t̃₂^*𝒥̃₂` (`Deformation.ToposThickening.ThickeningTargetMorphism.`
`IdealSquareCompatible` for the relative squares of `h₁`, `h₂`). -/
def RelativeIdealSquareCompatible
    (lam : D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₁ hh₁ ⟶
      D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₂ hh₂) : Prop :=
  (relativeThickeningTarget h₁ h₂ g hg).IdealSquareCompatible
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
      (relativeMap_comp_of_comp_eq g hg)) lam

include hhg in
/-- **The descended classes of the relative squares along `X_{T'₂} ⟶ X_{T'₁}`, from the
ideal-square compatibility.** -/
theorem extDescentAddEquiv_symm_existenceObstructionClass_eq_comp_of_relativeIdealSquare
    (lam : D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₁ hh₁ ⟶
      D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₂ hh₂)
    (H : RelativeIdealSquareCompatible h₁ h₂ g hg hh₁ hh₂ hfl₁ hfl₂ lam) :
    (extDescentAddEquiv.{u, u + 1, u, u + 1, u, e', e}
        (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
        (objectToposModule ξ) (D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₂ hh₂)
          2).symm
        (existenceObstructionClass.{u, u + 1, u, u, u + 1, u, e}
          (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h₂))).obj (objectToposModule ξ)) _
          (basePullbackIdealTensorIso
            (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h₂))
            (D.relativeSquareSituation.relativeSquareThickening h₂)
            (D.relativeSquareSituation.relativeSquareLeft h₂)
            (relBaseRight (smallEtaleRingedToposHom B S hS
              (D.relativeSquareSituation.projection T'₂)))
            (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
            (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₂ hh₂)
            (D.relativeSquareSituation.relativeSquare_comm h₂)
            (isFlat_relBaseRight_smallEtaleRingedToposHom
              (D.relativeSquareSituation.projection T'₂) hfl₂)
            (D.relativeSquareSituation.isStrict_relativeSquare h₂ hh₂)
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
              (D.relativeSquareSituation.relativeMap h₂))).obj (objectToposModule ξ))).inv) =
      ((extDescentAddEquiv.{u, u + 1, u, u + 1, u, e', e}
        (D.relativeSquareSituation.relativeMapFirstOrderThickening h₁ hh₁)
        (objectToposModule ξ) (D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₁ hh₁)
          2).symm
        (existenceObstructionClass.{u, u + 1, u, u, u + 1, u, e}
          (D.relativeSquareSituation.relativeMapFirstOrderThickening h₁ hh₁)
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h₁))).obj (objectToposModule ξ)) _
          (basePullbackIdealTensorIso
            (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h₁))
            (D.relativeSquareSituation.relativeSquareThickening h₁)
            (D.relativeSquareSituation.relativeSquareLeft h₁)
            (relBaseRight (smallEtaleRingedToposHom B S hS
              (D.relativeSquareSituation.projection T'₁)))
            (D.relativeSquareSituation.relativeMapFirstOrderThickening h₁ hh₁)
            (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h₁ hh₁)
            (D.relativeSquareSituation.relativeSquare_comm h₁)
            (isFlat_relBaseRight_smallEtaleRingedToposHom
              (D.relativeSquareSituation.projection T'₁) hfl₁)
            (D.relativeSquareSituation.isStrict_relativeSquare h₁ hh₁)
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
              (D.relativeSquareSituation.relativeMap h₁))).obj (objectToposModule ξ))).inv)).comp
        (Abelian.Ext.mk₀ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O).flip.obj
            (objectToposModule ξ)).map lam)) (add_zero 2) :=
  extDescentAddEquiv_symm_existenceObstructionClass_smallEtale
    (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
    (D.relativeSquareSituation.relativeMap h₁) (relativeMap_comp_of_comp_eq g hg)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h₁ hh₁)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h₂ hh₂)
    (D.relativeSquareSituation.relativeMapFirstOrderThickening g hhg)
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
    (objectToposModule ξ) lam H

include hhg in
/-- **The obstructions on `X_T` along a morphism of thickenings, from the ideal-square
compatibility.** -/
theorem thickeningObstructionOnBase_eq_comp_of_idealSquareCompatible
    (lam : D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₁ hh₁ ⟶
      D.relativeSquareSituation.relativeSquareBasePullbackIdeal h₂ hh₂)
    (H : RelativeIdealSquareCompatible h₁ h₂ g hg hh₁ hh₂ hfl₁ hfl₂ lam) :
    thickeningObstructionOnBase.{e, e'} h₂ hh₂ hfl₂ =
      (thickeningObstructionOnBase.{e, e'} h₁ hh₁ hfl₁).comp
        (Abelian.Ext.mk₀ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O).flip.obj
            (objectToposModule ξ)).map lam)) (add_zero 2) :=
  extDescentAddEquiv_symm_existenceObstructionClass_eq_comp_of_relativeIdealSquare h₁ h₂ g hg
    hh₁ hh₂ hhg hfl₁ hfl₂ lam H

end Naturality

section Chart

variable (hY : IsTerminal D.Y)
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
  {T₁ : Deformation.Artin.SquareZeroThickening A B S hS toS hA A₁}
  {T₂ : Deformation.Artin.SquareZeroThickening A B S hS toS hA A₂}

/-- **A surjective morphism of square-zero thickenings of `A` is a first order thickening**
`Spec A₂ ⟶ Spec A₁`: its kernel lies in the square-zero kernel of `A₁ → A`. -/
theorem isFirstOrderThickening_thickeningTestSchemeMap
    (f : Deformation.Artin.SquareZeroThickening.Hom T₁ T₂) (hf : Function.Surjective f.ringHom) :
    Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (D.thickeningTestSchemeMap hY f).left) := by
  have hle : RingHom.ker f.ringHom ≤ RingHom.ker T₁.q := fun a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    rw [← f.overBase, RingHom.comp_apply, ha, map_zero]
  have hsq : RingHom.ker (CommRingCat.ofHom f.ringHom).hom ^ 2 = ⊥ :=
    le_bot_iff.1 ((pow_le_pow_left' hle 2).trans T₁.squareZeroSurjection.2.le)
  change Stacks.Thickenings.IsFirstOrderThickening
    (B.inclusion.map (thickeningOverMap f).left)
  exact Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom f.ringHom) hf hsq

end Chart

end AlgebraicGeometry.Space.CoherentSituation

end
