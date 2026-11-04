module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of a module along a square of ring isomorphisms

Let `α : R₁ ≃+* R₂` and `β : A₁ ≃+* A₂` be isomorphisms of rings, let `A₁` be an `R₁`-algebra and
`A₂` an `R₂`-algebra, and suppose the square commutes: `β ∘ algebraMap R₁ A₁ = algebraMap R₂ A₂ ∘
α`. Let `M` carry `R₁`- and `R₂`-module structures that correspond under `α`, and let `N` carry
`A₁`- and `A₂`-module structures that correspond under `β`. Then an `R₂`-linear map `f₂ : M →ₗ N`
and the same function read as an `R₁`-linear map `f₁` have **the same base change**: the two
comparisons

`A₁ ⊗_{R₁} M →ₗ[A₁] N`  and  `A₂ ⊗_{R₂} M →ₗ[A₂] N`

of `LinearMap.liftBaseChange` differ only by an additive bijection of their sources, so one is
bijective exactly when the other is.

## Main definitions

* `Stacks.BaseChange.congrMap` is the additive map `A₁ ⊗_{R₁} M →+ A₂ ⊗_{R₂} M` carrying `a ⊗ m`
  to `β a ⊗ m`.

## Main results

* `Stacks.BaseChange.bijective_congrMap`: that map is bijective, its inverse being the same
  construction for `α.symm` and `β.symm`.
* `Stacks.BaseChange.liftBaseChange_congrMap`: the comparison over the second pair of rings,
  precomposed with it, is the comparison over the first pair.
* `Stacks.BaseChange.bijective_liftBaseChange_iff`: **bijectivity of the base change comparison
  does not depend on which of two isomorphic spellings of the rings it is written over.**
-/

@[expose] public section

open scoped TensorProduct

universe u₁ u₂ v₁ v₂ w w'

namespace Stacks.BaseChange

variable {R₁ : Type u₁} {R₂ : Type u₂} {A₁ : Type v₁} {A₂ : Type v₂} {M : Type w} {N : Type w'}
  [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂] [Algebra R₁ A₁] [Algebra R₂ A₂]
  [AddCommGroup M] [Module R₁ M] [Module R₂ M]

/-! ### The two compatibilities, read in the other direction -/

/-- The compatibility of the two actions on `M` read for `α.symm`: they correspond under `α` in
either direction. -/
theorem smul_eq_symm_smul (α : R₁ ≃+* R₂) (hM : ∀ (r : R₁) (m : M), r • m = α r • m)
    (r : R₂) (m : M) : r • m = α.symm r • m := by
  rw [hM (α.symm r) m, α.apply_symm_apply]

/-- The commutativity of the square read for `α.symm` and `β.symm`. -/
theorem algebraMap_symm (α : R₁ ≃+* R₂) (β : A₁ ≃+* A₂)
    (hsq : ∀ r : R₁, β (algebraMap R₁ A₁ r) = algebraMap R₂ A₂ (α r)) (r : R₂) :
    β.symm (algebraMap R₂ A₂ r) = algebraMap R₁ A₁ (α.symm r) :=
  β.injective (by rw [β.apply_symm_apply, hsq, α.apply_symm_apply])

/-! ### The comparison of the two tensor products -/

section Congr

variable (α : R₁ ≃+* R₂) (β : A₁ ≃+* A₂)
  (hM : ∀ (r : R₁) (m : M), r • m = α r • m)
  (hsq : ∀ r : R₁, β (algebraMap R₁ A₁ r) = algebraMap R₂ A₂ (α r))

/-- The additive map `A₁ ⊗_{R₁} M →+ A₂ ⊗_{R₂} M` carrying `a ⊗ m` to `β a ⊗ m`. -/
def congrMap : A₁ ⊗[R₁] M →+ A₂ ⊗[R₂] M :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun a : A₁ => AddMonoidHom.mk' (fun m : M => β a ⊗ₜ[R₂] m)
        fun m m' => TensorProduct.tmul_add _ _ _)
      fun a a' => by
        refine AddMonoidHom.ext fun m => ?_
        change β (a + a') ⊗ₜ[R₂] m = β a ⊗ₜ[R₂] m + β a' ⊗ₜ[R₂] m
        rw [map_add, TensorProduct.add_tmul])
    fun r a m => by
      change β (r • a) ⊗ₜ[R₂] m = β a ⊗ₜ[R₂] (r • m)
      rw [Algebra.smul_def r a, map_mul, hsq, ← Algebra.smul_def, TensorProduct.smul_tmul, hM]

/-- The map `congrMap α β hM hsq` sends `a ⊗ m` to `β a ⊗ m`. -/
@[simp]
theorem congrMap_tmul (a : A₁) (m : M) :
    congrMap α β hM hsq (a ⊗ₜ[R₁] m) = β a ⊗ₜ[R₂] m := rfl

/-- **The comparison `congrMap` is bijective**, with inverse the same construction for `α.symm`
and `β.symm`. -/
theorem bijective_congrMap : Function.Bijective (congrMap α β hM hsq (M := M)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨congrMap α.symm β.symm (smul_eq_symm_smul α hM) (algebraMap_symm α β hsq),
      fun z => ?_, fun z => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a m => rw [congrMap_tmul, congrMap_tmul, β.symm_apply_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a m => rw [congrMap_tmul, congrMap_tmul, β.apply_symm_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

end Congr

/-! ### Transporting bijectivity of the base change comparison -/

section LiftBaseChange

variable [AddCommGroup N] [Module R₁ N] [Module R₂ N] [Module A₁ N] [Module A₂ N]
  [IsScalarTower R₁ A₁ N] [IsScalarTower R₂ A₂ N]
  (α : R₁ ≃+* R₂) (β : A₁ ≃+* A₂)
  (hM : ∀ (r : R₁) (m : M), r • m = α r • m)
  (hsq : ∀ r : R₁, β (algebraMap R₁ A₁ r) = algebraMap R₂ A₂ (α r))
  (hN : ∀ (a : A₁) (n : N), a • n = β a • n)
  (f₁ : M →ₗ[R₁] N) (f₂ : M →ₗ[R₂] N) (hf : ∀ m : M, f₁ m = f₂ m)

include hN hf in
/-- **The two base change comparisons differ only by the comparison of their sources.**  The
`A₂`-linear extension of `f₂`, precomposed with `Stacks.BaseChange.congrMap`, is the `A₁`-linear
extension of `f₁`. -/
theorem liftBaseChange_congrMap (z : A₁ ⊗[R₁] M) :
    f₂.liftBaseChange A₂ (congrMap α β hM hsq z) = f₁.liftBaseChange A₁ z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a m =>
    rw [congrMap_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, hf,
      hN a (f₂ m)]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

include α hM hsq hN hf in
/-- **Bijectivity of the base change comparison does not depend on which of two isomorphic
spellings of the rings it is written over.**  Given isomorphisms `α : R₁ ≃+* R₂`, `β : A₁ ≃+* A₂`
commuting with the two structure maps, modules whose two actions correspond under them, and one
map read over both base rings, the comparison `A₁ ⊗_{R₁} M →ₗ[A₁] N` is bijective exactly when
`A₂ ⊗_{R₂} M →ₗ[A₂] N` is. -/
theorem bijective_liftBaseChange_iff :
    Function.Bijective (f₁.liftBaseChange A₁) ↔ Function.Bijective (f₂.liftBaseChange A₂) := by
  rw [show ⇑(f₁.liftBaseChange A₁) = ⇑(f₂.liftBaseChange A₂) ∘ ⇑(congrMap α β hM hsq) from
    funext fun z => (liftBaseChange_congrMap α β hM hsq hN f₁ f₂ hf z).symm]
  exact Function.Bijective.of_comp_iff _ (bijective_congrMap α β hM hsq (M := M))

end LiftBaseChange

end Stacks.BaseChange

end
