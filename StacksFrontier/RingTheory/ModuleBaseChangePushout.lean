module

public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of a module across a pushout of rings

Let

```
R  ⟶ S
↓     ↓
R' ⟶ S'
```

be a pushout square of commutative rings, `M` an `S`-module and `N` an `S'`-module, and let
`ℓ : M ⟶ N` be an `S`-linear map exhibiting `N` as the base change `S' ⊗_S M` of `M`.  Then `ℓ`
also exhibits `N` as the base change `R' ⊗_R M` of `M` along the left-hand side of the square.

## Main results

* `Algebra.IsPushout.isBaseChange_restrictScalars`: `N` is the base change of `M` to `R'`.
* `Algebra.IsPushout.bijective_liftBaseChange` and
  `Algebra.IsPushout.bijective_liftBaseChange_of_eq`: the comparison map `R' ⊗_R M ⟶ N` is
  bijective.

## Implementation notes

The comparison map agrees with the composite identification
`R' ⊗_R M ≃ M ⊗_R R' ≃ M ⊗_S S' ≃ S' ⊗_S M ≃ N`, whose middle step is
`IsBaseChange.tensorEquiv` for the pushout and whose outer steps are `TensorProduct.comm`.
-/

@[expose] public section

open TensorProduct

universe u

namespace Algebra.IsPushout

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
  [IsScalarTower R S S'] [IsScalarTower R R' S'] [h : Algebra.IsPushout R S R' S']
  {M N : Type*} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [AddCommGroup N] [Module S' N] [Module S N] [Module R' N] [Module R N]
  [IsScalarTower S S' N] [IsScalarTower R' S' N] [IsScalarTower R R' N] [IsScalarTower R S N]

/-- The comparison `M ⊗_S S' ≃ M ⊗_R R'` of `IsBaseChange.tensorEquiv` sends `m ⊗ (r : R')` to
`m ⊗ r`, where `R' ⟶ S'` is the right-hand side of the pushout square. -/
private theorem tensorEquiv_tmul_algebraMap (m : M) (r : R') :
    h.out.tensorEquiv M (m ⊗ₜ[S] (algebraMap R' S' r)) = m ⊗ₜ[R] r := by
  have hr : (algebraMap R' S' r) = (IsScalarTower.toAlgHom R R' S').toLinearMap r := rfl
  rw [hr, IsBaseChange.tensorEquiv, LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul,
    IsBaseChange.equiv_symm_apply, AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- If `N` is the base change of `M` from `S` to `S'`, the comparison `R' ⊗_R M ⟶ N` of the
left-hand side of the square is bijective. -/
theorem bijective_liftBaseChange (ℓ : M →ₗ[S] N) (hℓ : IsBaseChange S' ℓ) :
    Function.Bijective (LinearMap.liftBaseChange R' (ℓ.restrictScalars R)) := by
  have hcomp : ∀ x : R' ⊗[R] M,
      LinearMap.liftBaseChange R' (ℓ.restrictScalars R) x =
        hℓ.equiv (_root_.TensorProduct.comm S M S'
          ((h.out.tensorEquiv M).symm (_root_.TensorProduct.comm R R' M x))) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r m =>
      rw [LinearMap.liftBaseChange_tmul, LinearMap.restrictScalars_apply,
        _root_.TensorProduct.comm_tmul,
        (LinearEquiv.symm_apply_eq _).2 (tensorEquiv_tmul_algebraMap m r).symm,
        _root_.TensorProduct.comm_tmul, IsBaseChange.equiv_tmul, IsScalarTower.algebraMap_smul]
    | add x y hx hy => simp [hx, hy]
  rw [funext hcomp]
  exact hℓ.equiv.bijective.comp ((_root_.TensorProduct.comm S M S').bijective.comp
    ((h.out.tensorEquiv M).symm.bijective.comp (_root_.TensorProduct.comm R R' M).bijective))

/-- If `N` is the base change of `M` from `S` to `S'` along `ℓ`, and the `R`-linear map `g` agrees
with `ℓ` pointwise, the comparison `R' ⊗_R M ⟶ N` induced by `g` is bijective. -/
theorem bijective_liftBaseChange_of_eq (g : M →ₗ[R] N) (ℓ : M →ₗ[S] N)
    (hgl : ∀ x, g x = ℓ x) (hℓ : IsBaseChange S' ℓ) :
    Function.Bijective (LinearMap.liftBaseChange R' g) := by
  obtain rfl : g = ℓ.restrictScalars R := LinearMap.ext hgl
  exact bijective_liftBaseChange ℓ hℓ

/-- If `N` is the base change of `M` from `S` to `S'`, then it is the base change of `M` from `R`
to `R'`. -/
theorem isBaseChange_restrictScalars (ℓ : M →ₗ[S] N) (hℓ : IsBaseChange S' ℓ) :
    IsBaseChange R' (ℓ.restrictScalars R) :=
  IsBaseChange.of_equiv
    (LinearEquiv.ofBijective (LinearMap.liftBaseChange R' (ℓ.restrictScalars R))
      (bijective_liftBaseChange ℓ hℓ))
    fun x ↦ by simp

end Algebra.IsPushout

end
