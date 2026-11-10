module

public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction

/-!
# The cartesian condition over rings identified with the rings of sections

`Stacks.PresheafOfModules.restrictionBaseChange` is the base-change comparison
`R(Y) ⊗_{R(X)} M(X) ⟶ M(Y)` of a restriction map of a presheaf of modules, stated over the rings
of sections of the coefficient presheaf.  The algebraic geometry of the library often computes
those rings only up to a canonical identification — the regular functions on an étale chart of an
algebraic space against the global functions of the corresponding object of a fibred category,
for instance — and needs the comparison over the identified rings, as a `LinearMap.liftBaseChange`.
This file passes from one to the other.

## Main results

* `Stacks.PresheafOfModules.bijective_liftBaseChange_of_bijective_restrictionBaseChange`: if the
  comparison over the rings of sections is bijective, so is the comparison over any rings
  identified with them compatibly with the scalar actions and the restriction map of the rings.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u v w

namespace Stacks.PresheafOfModules

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- **The base-change comparison of a restriction map, read over rings identified with the rings of
sections.**  Let `M` be a presheaf of modules over a presheaf of commutative rings `R` and let
`f : X ⟶ Y`.  If the base-change comparison `R(Y) ⊗_{R(X)} M(X) ⟶ M(Y)` of the restriction map is
bijective, then so is the comparison `Bc ⊗_A M(X) ⟶ M(Y)` of any `A`-linear map agreeing with the
restriction map, for commutative rings `A` and `Bc` identified with `R(X)` and `R(Y)` compatibly
with the scalar actions and with the restriction of `R` along `f`.

The two tensor products are identified on pure tensors by `b ⊗ m ↦ fB⁻¹ b ⊗ m`, which is
well defined in both directions by the compatibility `halg` of the ring identifications. -/
theorem bijective_liftBaseChange_of_bijective_restrictionBaseChange
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (hM : Function.Bijective (restrictionBaseChange M f))
    (A Bc : Type*) [CommRing A] [CommRing Bc] [Algebra A Bc]
    [Module A (M.obj X)] [Module A (M.obj Y)] [Module Bc (M.obj Y)]
    [IsScalarTower A Bc (M.obj Y)]
    (fA : (R.obj X : Type u) ≃+* A) (hfA : ∀ (c : R.obj X) (m : M.obj X), fA c • m = c • m)
    (fB : (R.obj Y : Type u) ≃+* Bc) (hfB : ∀ (c : R.obj Y) (m : M.obj Y), fB c • m = c • m)
    (halg : ∀ c : A, algebraMap A Bc c = fB ((R.map f).hom (fA.symm c)))
    (r : M.obj X →ₗ[A] M.obj Y) (hr : ∀ s, r s = M.map f s) :
    Function.Bijective (r.liftBaseChange Bc) := by
  let := (R.map f).hom.toAlgebra
  have h2 : ∀ (a : A) (m : M.obj X), a • m = fA.symm a • m := fun a m => by
    rw [← hfA, RingEquiv.apply_symm_apply]
  let E : Bc ⊗[A] M.obj X →+ (R.obj Y : Type u) ⊗[R.obj X] M.obj X :=
    TensorProduct.liftAddHom
      { toFun := fun b =>
          { toFun := fun m => (fB.symm b : R.obj Y) ⊗ₜ[R.obj X] m
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' := fun m m' => TensorProduct.tmul_add _ _ _ }
        map_zero' := by
          ext m
          change (fB.symm 0 : R.obj Y) ⊗ₜ[R.obj X] m = 0
          rw [map_zero, TensorProduct.zero_tmul]
        map_add' := fun b b' => by
          ext m
          change (fB.symm (b + b') : R.obj Y) ⊗ₜ[R.obj X] m =
            (fB.symm b : R.obj Y) ⊗ₜ[R.obj X] m + (fB.symm b' : R.obj Y) ⊗ₜ[R.obj X] m
          rw [map_add, TensorProduct.add_tmul] }
      (fun a b m => by
        change (fB.symm (a • b) : R.obj Y) ⊗ₜ[R.obj X] m =
          (fB.symm b : R.obj Y) ⊗ₜ[R.obj X] (a • m)
        have h1 : fB.symm (a • b) = fA.symm a • fB.symm b := by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg, RingEquiv.symm_apply_apply]
          rfl
        rw [h1, h2]
        exact TensorProduct.smul_tmul _ _ _)
  let E' : (R.obj Y : Type u) ⊗[R.obj X] M.obj X →+ Bc ⊗[A] M.obj X :=
    TensorProduct.liftAddHom
      { toFun := fun c =>
          { toFun := fun m => fB c ⊗ₜ[A] m
            map_zero' := TensorProduct.tmul_zero _ _
            map_add' := fun m m' => TensorProduct.tmul_add _ _ _ }
        map_zero' := by
          ext m
          change fB 0 ⊗ₜ[A] m = 0
          rw [map_zero, TensorProduct.zero_tmul]
        map_add' := fun b b' => by
          ext m
          change fB (b + b') ⊗ₜ[A] m = fB b ⊗ₜ[A] m + fB b' ⊗ₜ[A] m
          rw [map_add, TensorProduct.add_tmul] }
      (fun c s m => by
        change fB (c • s) ⊗ₜ[A] m = fB s ⊗ₜ[A] (c • m)
        have h1 : fB (c • s) = fA c • fB s := by
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg, RingEquiv.symm_apply_apply]
          rfl
        rw [h1, ← hfA]
        exact TensorProduct.smul_tmul _ _ _)
  have hE'E : ∀ z, E' (E z) = z := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      change fB (fB.symm b) ⊗ₜ[A] m = b ⊗ₜ[A] m
      rw [RingEquiv.apply_symm_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  have hEE' : ∀ z, E (E' z) = z := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul c m =>
      change (fB.symm (fB c) : R.obj Y) ⊗ₜ[R.obj X] m = c ⊗ₜ[R.obj X] m
      rw [RingEquiv.symm_apply_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  have key : ∀ z, r.liftBaseChange Bc z = restrictionBaseChange M f (E z) := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      rw [LinearMap.liftBaseChange_tmul]
      refine Eq.trans ?_ (restrictionBaseChange_tmul M f (fB.symm b) m).symm
      rw [hr]
      refine Eq.trans ?_ (hfB (fB.symm b) (M.map f m))
      rw [RingEquiv.apply_symm_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']; exact (map_add _ _ _).symm
  have hEb : Function.Bijective E :=
    ⟨fun z z' hzz' => by rw [← hE'E z, ← hE'E z', hzz'], fun z => ⟨E' z, hEE' z⟩⟩
  have hfun : (r.liftBaseChange Bc : Bc ⊗[A] M.obj X → M.obj Y) =
      (restrictionBaseChange M f : _ → _) ∘ E := funext key
  rw [hfun]
  exact hM.comp hEb

end Stacks.PresheafOfModules
