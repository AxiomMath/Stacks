module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.AffineTheta
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.RingHeart
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.TensorColimit

/-!
# Extension of scalars along a directed system of rings, read over the base ring

For ring maps `f : R ⟶ A` and `β : A ⟶ A'`, the map `A ⊗_R M ⟶ A' ⊗_R M` induced by `β` is a
natural transformation of functors of `R`-modules, and for a directed system of `R`-algebras
`A_i` with colimit `A` the `R`-modules `A_i ⊗_R M` have `A ⊗_R M` as their filtered colimit.

## Main definitions

* `Stacks.LimitHomDescent.Affine.resExt`: `M ↦ A ⊗_R M`, as an `R`-module.
* `Stacks.LimitHomDescent.Affine.tau`: the map `A ⊗_R M ⟶ A' ⊗_R M` of a factorisation
  `f ≫ β = f'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ChangeOfRings TensorProduct

universe u

namespace Stacks.LimitHomDescent.Affine

variable {R A A' : CommRingCat.{u}}

/-- `M ↦ A ⊗_R M`, read as an `R`-module. -/
abbrev resExt (f : R ⟶ A) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ModuleCat.extendScalars.{u, u, u} f.hom ⋙ ModuleCat.restrictScalars.{u} f.hom

/-- The map `A ⊗_R M ⟶ A' ⊗_R M`, natural in `M`: `x ↦ 1 ⊗_A x` followed by
`A' ⊗_A (A ⊗_R M) ≅ A' ⊗_R M`. -/
def tau₀ (f : R ⟶ A) (β : A ⟶ A') : resExt f ⟶ resExt (f ≫ β) :=
  Functor.whiskerLeft (ModuleCat.extendScalars.{u, u, u} f.hom)
      (Functor.whiskerRight (ModuleCat.extendRestrictScalarsAdj.{u, u, u} β.hom).unit
        (ModuleCat.restrictScalars.{u} f.hom)) ≫
    Functor.whiskerLeft (ModuleCat.extendScalars.{u, u, u} f.hom)
      (Functor.associator (ModuleCat.extendScalars.{u, u, u} β.hom)
        (ModuleCat.restrictScalars.{u} β.hom) (ModuleCat.restrictScalars.{u} f.hom)).hom ≫
    Functor.whiskerLeft (ModuleCat.extendScalars.{u, u, u} f.hom)
      (Functor.whiskerLeft (ModuleCat.extendScalars.{u, u, u} β.hom)
        (ModuleCat.restrictScalarsComp' f.hom β.hom (f ≫ β).hom rfl).inv) ≫
    (Functor.associator (ModuleCat.extendScalars.{u, u, u} f.hom)
      (ModuleCat.extendScalars.{u, u, u} β.hom) (ModuleCat.restrictScalars.{u} (f ≫ β).hom)).inv ≫
    Functor.whiskerRight (ModuleCat.extendScalarsComp f.hom β.hom).inv
      (ModuleCat.restrictScalars.{u} (f ≫ β).hom)

/-- `tau₀ f β` sends `x` to the image of `1 ⊗_A x` under `A' ⊗_A (A ⊗_R M) ≅ A' ⊗_R M`. -/
theorem tau₀_app_apply (f : R ⟶ A) (β : A ⟶ A') (M : ModuleCat.{u} R) (x : (resExt f).obj M) :
    (tau₀ f β).app M x = (ModuleCat.extendScalarsComp f.hom β.hom).inv.app M
      ((1 : A') ⊗ₜ[A, β.hom] x) :=
  rfl

/-- **`A' ⊗_A (A ⊗_R M) ≅ A' ⊗_R M` on a pure tensor.** -/
theorem extendScalarsComp_inv_one_tmul (f : R ⟶ A) (β : A ⟶ A') (M : ModuleCat.{u} R) (a : A)
    (m : M) :
    (ModuleCat.extendScalarsComp f.hom β.hom).inv.app M
        ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} β.hom).unit.app
          ((ModuleCat.extendScalars.{u, u, u} f.hom).obj M) (a ⊗ₜ[R, f.hom] m)) =
      (β a) ⊗ₜ[R, β.hom.comp f.hom] m := by
  let Z := (ModuleCat.extendScalars.{u, u, u} f.hom).obj M
  let ι := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} β.hom).unit.app Z
  let c := ModuleCat.extendScalarsComp.{u, u} f.hom β.hom
  have s1 := ModuleCat.ExtendScalars.smul_tmul f.hom (M := M) a (1 : A) m
  rw [mul_one] at s1
  have s2 := (congrArg ι.hom s1).symm.trans (map_smul ι.hom a _)
  have s3 := (congrArg (c.inv.app M).hom
    (ModuleCat.extendScalarsComp_hom_app_one_tmul f.hom β.hom M m).symm).trans
      (ConcreteCategory.congr_hom (c.hom_inv_id_app M) _)
  have s4 := ModuleCat.ExtendScalars.smul_tmul (β.hom.comp f.hom) (M := M) (β a) (1 : A') m
  rw [mul_one] at s4
  exact ((congrArg (c.inv.app M).hom s2).trans (map_smul (c.inv.app M).hom (β a) _)).trans
    ((congrArg (fun y => (β a) • y) s3).trans s4)

/-- `tau₀ f β` sends `a ⊗ m` to `β a ⊗ m`. -/
theorem tau₀_app_tmul (f : R ⟶ A) (β : A ⟶ A') (M : ModuleCat.{u} R) (a : A) (m : M) :
    (tau₀ f β).app M (a ⊗ₜ[R, f.hom] m) = (β a) ⊗ₜ[R, β.hom.comp f.hom] m :=
  extendScalarsComp_inv_one_tmul f β M a m

/-- The map `A ⊗_R M ⟶ A' ⊗_R M` of a factorisation `f ≫ β = f'`. -/
def tau (f : R ⟶ A) (f' : R ⟶ A') (β : A ⟶ A') (hβ : f ≫ β = f') : resExt f ⟶ resExt f' := by
  subst hβ
  exact tau₀ f β

/-- `tau` of the factorisation `f ≫ β = f ≫ β` is `tau₀ f β`. -/
theorem tau_rfl (f : R ⟶ A) (β : A ⟶ A') : tau f (f ≫ β) β rfl = tau₀ f β := rfl

/-- `tau f f' β hβ` sends `a ⊗ m` to `β a ⊗ m`. -/
theorem tau_app_tmul (f : R ⟶ A) (f' : R ⟶ A') (β : A ⟶ A') (hβ : f ≫ β = f')
    (M : ModuleCat.{u} R) (a : A) (m : M) :
    (tau f f' β hβ).app M (a ⊗ₜ[R, f.hom] m) = (β a) ⊗ₜ[R, f'.hom] m := by
  subst hβ
  exact tau₀_app_tmul f β M a m

/-- `A ⊗_R -` and the maps `tau` are the functions `x ↦ (β ⊗ 1) x` on the underlying tensor
products. -/
theorem tau_app_eq_rTensor (f : R ⟶ A) (f' : R ⟶ A') (β : A ⟶ A') (hβ : f ≫ β = f')
    (M : ModuleCat.{u} R)
    (βl : (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of A A) →ₗ[R]
      (ModuleCat.restrictScalars f'.hom).obj (ModuleCat.of A' A'))
    (hβl : ∀ a, βl a = β a) (x : (resExt f).obj M) :
    (tau f f' β hβ).app M x = βl.rTensor M x := by
  refine LinearMap.congr_fun (g := βl.rTensor M) (TensorProduct.ext' fun a m => ?_) x
  refine (tau_app_tmul f f' β hβ M a m).trans ?_
  rw [LinearMap.rTensor_tmul, hβl]
  rfl

/-- The maps `tau` compose: `tau` along `β'` after `tau` along `β` is `tau` along `β ≫ β'`. -/
theorem tau_comp_app {A'' : CommRingCat.{u}} (f : R ⟶ A) (f' : R ⟶ A') (f'' : R ⟶ A'')
    (β : A ⟶ A') (β' : A' ⟶ A'') (β'' : A ⟶ A'') (hβ : f ≫ β = f') (hβ' : f' ≫ β' = f'')
    (hβ'' : f ≫ β'' = f'') (hb : β ≫ β' = β'') (M : ModuleCat.{u} R) (x : (resExt f).obj M) :
    (tau f' f'' β' hβ').app M ((tau f f' β hβ).app M x) = (tau f f'' β'' hβ'').app M x := by
  subst hb
  refine LinearMap.congr_fun
    (f := ((tau f' f'' β' hβ').app M).hom.comp ((tau f f' β hβ).app M).hom)
    (g := ((tau f f'' (β ≫ β') hβ'').app M).hom) (TensorProduct.ext' fun a m => ?_) x
  exact ((congrArg ((tau f' f'' β' hβ').app M).hom (tau_app_tmul f f' β hβ M a m)).trans
    (tau_app_tmul f' f'' β' hβ' M (β a) m)).trans (tau_app_tmul f f'' (β ≫ β') hβ'' M a m).symm

/-- **Transposing along extension of scalars carries `tau₀` to extension of scalars along `β`.**
For `u : P ⟶ A ⊗_R M` (an `R`-linear map), the transpose of `u` followed by
`A ⊗_R M ⟶ A' ⊗_R M` is `A' ⊗_A -` of the transpose of `u`, read through
`A' ⊗_A (A ⊗_R -) ≅ A' ⊗_R -`. -/
theorem homEquiv_symm_comp_tau₀ (f : R ⟶ A) (β : A ⟶ A') {P M : ModuleCat.{u} R}
    (u : P ⟶ (resExt f).obj M) :
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (f ≫ β).hom).homEquiv _ _).symm
        (u ≫ (tau₀ f β).app M) =
      (ModuleCat.extendScalarsComp f.hom β.hom).hom.app P ≫
        (ModuleCat.extendScalars.{u, u, u} β.hom).map
          (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom).homEquiv _ _).symm u) ≫
        (ModuleCat.extendScalarsComp f.hom β.hom).inv.app M := by
  refine ModuleCat.ExtendScalars.hom_ext (fun p => ?_)
  have hL := congrArg (fun w => ModuleCat.Hom.hom w p)
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (f ≫ β).hom).homEquiv _ _ |>.apply_symm_apply
      (u ≫ (tau₀ f β).app M))
  have hu := congrArg (fun w => ModuleCat.Hom.hom w p)
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom).homEquiv _ _ |>.apply_symm_apply u)
  have h3 := ModuleCat.extendScalarsComp_hom_app_one_tmul f.hom β.hom P p
  refine hL.trans ((tau₀_app_apply f β M (u p)).trans ?_)
  refine (congrArg (fun y => (ModuleCat.extendScalarsComp f.hom β.hom).inv.app M
    ((1 : A') ⊗ₜ[A, β.hom] y)) hu.symm).trans ?_
  exact (congrArg (fun y => (ModuleCat.extendScalarsComp f.hom β.hom).inv.app M
    ((ModuleCat.extendScalars.{u, u, u} β.hom).map
      (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom).homEquiv _ _).symm u) y)) h3).symm

end Stacks.LimitHomDescent.Affine

end
