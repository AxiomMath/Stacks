module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator

import StacksCore.Tactic.StacksAttribute

/-!
# Iterated tensor products of three modules and the threefold tensor product

Stacks 00D0: for `R`-modules `M`, `N`, `P` the homomorphisms
`f : (M ⊗_R N) ⊗_R P → M ⊗_R N ⊗_R P` and `g : M ⊗_R N ⊗_R P → M ⊗_R (N ⊗_R P)` with
`f ((x ⊗ y) ⊗ z) = x ⊗ y ⊗ z` and `g (x ⊗ y ⊗ z) = x ⊗ (y ⊗ z)` are well defined and are
isomorphisms. Here `M ⊗_R N ⊗_R P` is the threefold tensor product of Stacks 00CZ, which is
Mathlib's `PiTensorProduct` over `Fin 3`; the three modules are the family `M 0`, `M 1`, `M 2`,
and the pure tensor `x ⊗ y ⊗ z` is `PiTensorProduct.tprod R` of the tuple
`Fin.cons x (Fin.cons y (Fin.cons z finZeroElim))`.

## Main declarations

* `PiTensorProduct.tmulTmulLeftEquiv`: the isomorphism `f`.
* `PiTensorProduct.tmulTmulRightEquiv`: the isomorphism `g`.
* `PiTensorProduct.tmulTmulLeftEquiv_trans_tmulTmulRightEquiv`: `g ∘ f` is Mathlib's associator
  `TensorProduct.assoc`.
-/

@[expose] public section

add_to_stacks 00D0 "the composite g ∘ f, on pure tensors" TensorProduct.assoc_tmul

namespace PiTensorProduct

open TensorProduct Function

variable {R : Type*} {M : Fin 3 → Type*}

private lemma update_cons_zero' (x x' : M 0) (y : M 1) (z : M 2) :
    update (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim)) : (i : Fin 3) → M i) 0 x' =
      Fin.cons x' (Fin.cons y (Fin.cons z finZeroElim)) := by
  funext i; fin_cases i <;> rfl

private lemma update_cons_one' (x : M 0) (y y' : M 1) (z : M 2) :
    update (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim)) : (i : Fin 3) → M i) 1 y' =
      Fin.cons x (Fin.cons y' (Fin.cons z finZeroElim)) := by
  funext i; fin_cases i <;> rfl

private lemma update_cons_two' (x : M 0) (y : M 1) (z z' : M 2) :
    update (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim)) : (i : Fin 3) → M i) 2 z' =
      Fin.cons x (Fin.cons y (Fin.cons z' finZeroElim)) := by
  funext i; fin_cases i <;> rfl

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable (R M) in
/-- The trilinear map `(x, y, z) ↦ x ⊗ y ⊗ z` into the threefold tensor product. -/
noncomputable def tprodThree : M 0 →ₗ[R] M 1 →ₗ[R] M 2 →ₗ[R] ⨂[R] i, M i :=
  LinearMap.mk₂ R
    (fun x y =>
      { toFun := fun z => tprod R (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim)))
        map_add' := fun z z' => by
          simpa [update_cons_two'] using
            (tprod R).map_update_add (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim))) 2 z z'
        map_smul' := fun r z => by
          simpa [update_cons_two'] using
            (tprod R).map_update_smul (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim))) 2 r z })
    (fun x x' y => by
      ext z
      simpa [update_cons_zero'] using
        (tprod R).map_update_add (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim))) 0 x x')
    (fun r x y => by
      ext z
      simpa [update_cons_zero'] using
        (tprod R).map_update_smul (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim))) 0 r x)
    (fun x y y' => by
      ext z
      simpa [update_cons_one'] using
        (tprod R).map_update_add (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim))) 1 y y')
    (fun r x y => by
      ext z
      simpa [update_cons_one'] using
        (tprod R).map_update_smul (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim))) 1 r y)

variable (R M) in
/-- The multilinear map `m ↦ (m 0 ⊗ m 1) ⊗ m 2` out of `Π i : Fin 3, M i`. -/
noncomputable def tmulTmulMultilinear : MultilinearMap R M ((M 0 ⊗[R] M 1) ⊗[R] M 2) where
  toFun m := (m 0 ⊗ₜ m 1) ⊗ₜ m 2
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin 3 := Subsingleton.elim _ _
    fin_cases i <;> simp [update_of_ne, add_tmul, tmul_add]
  map_update_smul' := by
    intro inst m i r x
    obtain rfl : inst = instDecidableEqFin 3 := Subsingleton.elim _ _
    fin_cases i <;> simp [update_of_ne, smul_tmul, tmul_smul]

variable (R M) in
/-- **Stacks 00D0**, the map `f`: the isomorphism `(M ⊗_R N) ⊗_R P ≅ M ⊗_R N ⊗_R P` from the
iterated tensor product to the threefold tensor product of Stacks 00CZ, with
`f ((x ⊗ y) ⊗ z) = x ⊗ y ⊗ z` (`tmulTmulLeftEquiv_tmul`). -/
@[stacks 00D0 "the map `f`; the three modules are the family `M 0`, `M 1`, `M 2` and the
threefold tensor product is `PiTensorProduct` over `Fin 3`"]
noncomputable def tmulTmulLeftEquiv : ((M 0 ⊗[R] M 1) ⊗[R] M 2) ≃ₗ[R] ⨂[R] i, M i :=
  LinearEquiv.ofLinearMap (TensorProduct.lift (TensorProduct.lift (tprodThree R M)))
    (lift (tmulTmulMultilinear R M))
    (by
      ext m
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, comp_apply, lift.tprod,
        LinearMap.id_coe, id_eq]
      change tprod R (Fin.cons (m 0) (Fin.cons (m 1) (Fin.cons (m 2) finZeroElim))) = tprod R m
      congr 1
      funext i; fin_cases i <;> rfl)
    (by
      apply TensorProduct.ext_threefold
      intro x y z
      simp only [LinearMap.coe_comp, comp_apply, TensorProduct.lift.tmul, LinearMap.id_coe, id_eq]
      exact lift.tprod _)

@[simp]
theorem tmulTmulLeftEquiv_tmul (x : M 0) (y : M 1) (z : M 2) :
    tmulTmulLeftEquiv R M ((x ⊗ₜ y) ⊗ₜ z) =
      tprod R (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim))) := by
  simp [tmulTmulLeftEquiv, tprodThree]

@[simp]
theorem tmulTmulLeftEquiv_symm_tprod (m : (i : Fin 3) → M i) :
    (tmulTmulLeftEquiv R M).symm (tprod R m) = (m 0 ⊗ₜ m 1) ⊗ₜ m 2 := by
  simp [tmulTmulLeftEquiv, tmulTmulMultilinear]

variable (R M) in
/-- **Stacks 00D0**, the map `g`: the isomorphism `M ⊗_R N ⊗_R P ≅ M ⊗_R (N ⊗_R P)` from the
threefold tensor product of Stacks 00CZ to the iterated tensor product, with
`g (x ⊗ y ⊗ z) = x ⊗ (y ⊗ z)` (`tmulTmulRightEquiv_tprod`). -/
@[stacks 00D0 "the map `g`; the three modules are the family `M 0`, `M 1`, `M 2` and the
threefold tensor product is `PiTensorProduct` over `Fin 3`"]
noncomputable def tmulTmulRightEquiv : (⨂[R] i, M i) ≃ₗ[R] M 0 ⊗[R] (M 1 ⊗[R] M 2) :=
  (tmulTmulLeftEquiv R M).symm ≪≫ₗ TensorProduct.assoc R (M 0) (M 1) (M 2)

@[simp]
theorem tmulTmulRightEquiv_tprod (m : (i : Fin 3) → M i) :
    tmulTmulRightEquiv R M (tprod R m) = m 0 ⊗ₜ (m 1 ⊗ₜ m 2) := by
  simp [tmulTmulRightEquiv]

theorem tmulTmulRightEquiv_tprod_cons (x : M 0) (y : M 1) (z : M 2) :
    tmulTmulRightEquiv R M (tprod R (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim)))) =
      x ⊗ₜ (y ⊗ₜ z) :=
  tmulTmulRightEquiv_tprod _

@[simp]
theorem tmulTmulRightEquiv_symm_tmul (x : M 0) (y : M 1) (z : M 2) :
    (tmulTmulRightEquiv R M).symm (x ⊗ₜ (y ⊗ₜ z)) =
      tprod R (Fin.cons x (Fin.cons y (Fin.cons z finZeroElim))) := by
  simp [tmulTmulRightEquiv]

variable (R M) in
/-- **Stacks 00D0**, the composite: `g ∘ f` is the associator
`TensorProduct.assoc : (M ⊗_R N) ⊗_R P ≅ M ⊗_R (N ⊗_R P)`. -/
@[stacks 00D0 "the composite `g ∘ f` is `TensorProduct.assoc`"]
theorem tmulTmulLeftEquiv_trans_tmulTmulRightEquiv :
    tmulTmulLeftEquiv R M ≪≫ₗ tmulTmulRightEquiv R M = TensorProduct.assoc R (M 0) (M 1) (M 2) :=
  LinearEquiv.ext fun w => by simp [tmulTmulRightEquiv]

end PiTensorProduct
