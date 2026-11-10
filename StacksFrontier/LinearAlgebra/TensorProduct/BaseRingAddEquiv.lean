module

public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Transport of a tensor product along a ring isomorphism of the base

Let `ρ : R₁ ≃+* R₂` be an isomorphism of commutative rings, let `N₁`, `M₁` be `R₁`-modules and
`N₂`, `M₂` be `R₂`-modules, and let `eN : N₁ ≃+ N₂` and `eM : M₁ ≃+ M₂` be additive isomorphisms
which are semilinear along `ρ`.  Then

`N₁ ⊗_{R₁} M₁ ≃+ N₂ ⊗_{R₂} M₂`,

carrying `n ⊗ m` to `eN n ⊗ eM m`.

Only the additive structure of the result is recorded, since the two sides are modules over
different rings.

## Main definitions

* `TensorProduct.addMonoidHomOfRingEquiv`: the additive map `n ⊗ m ↦ eN n ⊗ eM m`.
* `TensorProduct.addEquivOfRingEquiv`: the additive isomorphism `n ⊗ m ↦ eN n ⊗ eM m`.

## Main results

* `TensorProduct.addEquivOfRingEquiv_tmul` and
  `TensorProduct.addEquivOfRingEquiv_symm_tmul`: the values of the isomorphism and of its
  inverse on pure tensors.
-/

@[expose] public section

namespace TensorProduct

open scoped TensorProduct

variable {R₁ R₂ N₁ N₂ M₁ M₂ : Type*} [CommRing R₁] [CommRing R₂]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup M₁] [AddCommGroup M₂]
  [Module R₁ N₁] [Module R₂ N₂] [Module R₁ M₁] [Module R₂ M₂]

/-- The biadditive map `N₁ →+ M₁ →+ N₂ ⊗[R₂] M₂` given by `(n, m) ↦ eN n ⊗ eM m`. -/
def tmulAddHomOfAddEquiv (eN : N₁ ≃+ N₂) (eM : M₁ ≃+ M₂) : N₁ →+ M₁ →+ N₂ ⊗[R₂] M₂ where
  toFun n :=
    { toFun := fun m => eN n ⊗ₜ[R₂] eM m
      map_zero' := by rw [map_zero, tmul_zero]
      map_add' := fun m m' => by rw [map_add, tmul_add] }
  map_zero' := by
    refine AddMonoidHom.ext fun m => ?_
    change eN 0 ⊗ₜ[R₂] eM m = 0
    rw [map_zero, zero_tmul]
  map_add' n n' := by
    refine AddMonoidHom.ext fun m => ?_
    change eN (n + n') ⊗ₜ[R₂] eM m = eN n ⊗ₜ[R₂] eM m + eN n' ⊗ₜ[R₂] eM m
    rw [map_add, add_tmul]

/-- `TensorProduct.tmulAddHomOfAddEquiv eN eM` sends `(n, m)` to `eN n ⊗ eM m`. -/
theorem tmulAddHomOfAddEquiv_apply (eN : N₁ ≃+ N₂) (eM : M₁ ≃+ M₂) (n : N₁) (m : M₁) :
    tmulAddHomOfAddEquiv (R₂ := R₂) eN eM n m = eN n ⊗ₜ[R₂] eM m := rfl

/-- The map of `TensorProduct.tmulAddHomOfAddEquiv` is balanced over `R₁` as soon as the two
additive isomorphisms are semilinear along `ρ`. -/
theorem tmulAddHomOfAddEquiv_balanced (ρ : R₁ ≃+* R₂) (eN : N₁ ≃+ N₂) (eM : M₁ ≃+ M₂)
    (hN : ∀ (r : R₁) (n : N₁), eN (r • n) = ρ r • eN n)
    (hM : ∀ (r : R₁) (m : M₁), eM (r • m) = ρ r • eM m) (r : R₁) (n : N₁) (m : M₁) :
    tmulAddHomOfAddEquiv (R₂ := R₂) eN eM (r • n) m =
      tmulAddHomOfAddEquiv (R₂ := R₂) eN eM n (r • m) := by
  change eN (r • n) ⊗ₜ[R₂] eM m = eN n ⊗ₜ[R₂] eM (r • m)
  rw [hN, hM, smul_tmul]

/-- The additive map `N₁ ⊗_{R₁} M₁ →+ N₂ ⊗_{R₂} M₂` carrying `n ⊗ m` to `eN n ⊗ eM m`. -/
def addMonoidHomOfRingEquiv (ρ : R₁ ≃+* R₂) (eN : N₁ ≃+ N₂) (eM : M₁ ≃+ M₂)
    (hN : ∀ (r : R₁) (n : N₁), eN (r • n) = ρ r • eN n)
    (hM : ∀ (r : R₁) (m : M₁), eM (r • m) = ρ r • eM m) :
    N₁ ⊗[R₁] M₁ →+ N₂ ⊗[R₂] M₂ :=
  liftAddHom (tmulAddHomOfAddEquiv eN eM) (tmulAddHomOfAddEquiv_balanced ρ eN eM hN hM)

/-- `TensorProduct.addMonoidHomOfRingEquiv` sends `n ⊗ m` to `eN n ⊗ eM m`. -/
@[simp]
theorem addMonoidHomOfRingEquiv_tmul (ρ : R₁ ≃+* R₂) (eN : N₁ ≃+ N₂) (eM : M₁ ≃+ M₂)
    (hN : ∀ (r : R₁) (n : N₁), eN (r • n) = ρ r • eN n)
    (hM : ∀ (r : R₁) (m : M₁), eM (r • m) = ρ r • eM m) (n : N₁) (m : M₁) :
    addMonoidHomOfRingEquiv ρ eN eM hN hM (n ⊗ₜ[R₁] m) = eN n ⊗ₜ[R₂] eM m := rfl

/-- The inverse of a semilinear additive isomorphism is semilinear along the inverse
isomorphism of the base. -/
theorem symm_semilinear (ρ : R₁ ≃+* R₂) (eN : N₁ ≃+ N₂)
    (hN : ∀ (r : R₁) (n : N₁), eN (r • n) = ρ r • eN n) (r : R₂) (n : N₂) :
    eN.symm (r • n) = ρ.symm r • eN.symm n :=
  eN.injective (by rw [eN.apply_symm_apply, hN, ρ.apply_symm_apply, eN.apply_symm_apply])

/-- **Transport of a tensor product along a ring isomorphism of the base.**  Given
`ρ : R₁ ≃+* R₂` and additive isomorphisms of the two factors semilinear along `ρ`, the two
tensor products are additively isomorphic by `n ⊗ m ↦ eN n ⊗ eM m`. -/
def addEquivOfRingEquiv (ρ : R₁ ≃+* R₂) (eN : N₁ ≃+ N₂) (eM : M₁ ≃+ M₂)
    (hN : ∀ (r : R₁) (n : N₁), eN (r • n) = ρ r • eN n)
    (hM : ∀ (r : R₁) (m : M₁), eM (r • m) = ρ r • eM m) :
    N₁ ⊗[R₁] M₁ ≃+ N₂ ⊗[R₂] M₂ where
  toFun := ⇑(addMonoidHomOfRingEquiv ρ eN eM hN hM)
  invFun := ⇑(addMonoidHomOfRingEquiv ρ.symm eN.symm eM.symm
    (symm_semilinear ρ eN hN) (symm_semilinear ρ eM hM))
  map_add' := (addMonoidHomOfRingEquiv ρ eN eM hN hM).map_add
  left_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul n m =>
      change eN.symm (eN n) ⊗ₜ[R₁] eM.symm (eM m) = n ⊗ₜ[R₁] m
      rw [eN.symm_apply_apply, eM.symm_apply_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
  right_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul n m =>
      change eN (eN.symm n) ⊗ₜ[R₂] eM (eM.symm m) = n ⊗ₜ[R₂] m
      rw [eN.apply_symm_apply, eM.apply_symm_apply]
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']

/-- `TensorProduct.addEquivOfRingEquiv` sends `n ⊗ m` to `eN n ⊗ eM m`. -/
@[simp]
theorem addEquivOfRingEquiv_tmul (ρ : R₁ ≃+* R₂) (eN : N₁ ≃+ N₂) (eM : M₁ ≃+ M₂)
    (hN : ∀ (r : R₁) (n : N₁), eN (r • n) = ρ r • eN n)
    (hM : ∀ (r : R₁) (m : M₁), eM (r • m) = ρ r • eM m) (n : N₁) (m : M₁) :
    addEquivOfRingEquiv ρ eN eM hN hM (n ⊗ₜ[R₁] m) = eN n ⊗ₜ[R₂] eM m := rfl

/-- The inverse of `TensorProduct.addEquivOfRingEquiv` sends `n ⊗ m` to
`eN.symm n ⊗ eM.symm m`. -/
@[simp]
theorem addEquivOfRingEquiv_symm_tmul (ρ : R₁ ≃+* R₂) (eN : N₁ ≃+ N₂) (eM : M₁ ≃+ M₂)
    (hN : ∀ (r : R₁) (n : N₁), eN (r • n) = ρ r • eN n)
    (hM : ∀ (r : R₁) (m : M₁), eM (r • m) = ρ r • eM m) (n : N₂) (m : M₂) :
    (addEquivOfRingEquiv ρ eN eM hN hM).symm (n ⊗ₜ[R₂] m) = eN.symm n ⊗ₜ[R₁] eM.symm m := rfl

end TensorProduct

end
