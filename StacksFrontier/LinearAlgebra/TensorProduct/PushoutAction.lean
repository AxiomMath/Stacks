module

public import StacksFrontier.LinearAlgebra.TensorProduct.BaseChangeCancellation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The action of `A ⊗_R B` on `M ⊗_R N`, and the cancellation as an `A ⊗_R B`-linear equivalence

Let `A` and `B` be commutative algebras over a commutative ring `R`, let `M` be an `A`-module and
`N` a `B`-module, and write `T = A ⊗_R B`. The tensor product `M ⊗_R N` carries an action of `T`
in which `A` acts through `M` and `B` through `N`: `(a ⊗ b) • (m ⊗ n) = (a • m) ⊗ (b • n)`. With
that action, the `R`-linear equivalence `Stacks.TensorProductPushout.cancelBaseChange` is
`T`-linear.

## Main definitions

* `Stacks.TensorProductPushout.rightModule`: the action of `B` on `M ⊗_R N` through the right
  factor, `b • (m ⊗ n) = m ⊗ (b • n)`.
* `Stacks.TensorProductPushout.pushoutModule`: the action of `T = A ⊗_R B` on `M ⊗_R N`, obtained
  from the commuting `A`- and `B`-actions by `TensorProduct.Algebra.module`.
* `Stacks.TensorProductPushout.cancelBaseChangePushout`: the cancellation
  `(T ⊗_A M) ⊗_T (T ⊗_B N) ≃ M ⊗_R N` as a `T`-linear equivalence.

## Main results

* `Stacks.TensorProductPushout.pushoutModule_smul_tmul_tmul`: the compatibility
  `(a ⊗ b) • (m ⊗ n) = (a • m) ⊗ (b • n)`.
* `Stacks.TensorProductPushout.pushoutModule_algebraMap_apply`: the structure map
  `B → T` is `b ↦ 1 ⊗ b`.
* `Stacks.TensorProductPushout.cancelBaseChange_smul` and
  `Stacks.TensorProductPushout.cancelBaseChange_symm_smul`: `cancelBaseChange` and its inverse
  commute with the `T`-action.

## Implementation notes

None of the scalar structures used here is a global Mathlib instance, and for a good reason:
`Algebra.TensorProduct.rightAlgebra` and `TensorProduct.Algebra.module` would make the action of
`S` on `S ⊗_R S` ambiguous. They are installed with `attribute [local instance]`, and are
*named* `def`s here so that a consumer can install exactly the same ones.

`Stacks.TensorProductPushout.rightModule` is installed at a low priority. Its statement
`Module B (M ⊗[R] N)` matches *any* goal `Module ? (? ⊗[?] ?)`; at the default priority it is
picked for `Module R (M ⊗[R] N)` — where `R` acts through `N` rather than through `M` — and the
resulting structure, while equal to the canonical one, is not definitionally equal to it, which
breaks every subsequent `rfl`. At a low priority it is only ever used where nothing else applies,
which is exactly the `B`-action it is meant to supply.

The `T`-linearity is proved on the inverse map, where the induction is two levels deep
(`c = a ⊗ b` and `z = m ⊗ n`) because `Stacks.TensorProductPushout.cancelBaseChange_symm_tmul`
evaluates the inverse on a pure tensor of `M ⊗_R N`; proving it on the forward map directly would
need a six-level induction through `(T ⊗_A M) ⊗_T (T ⊗_B N)`. The forward statement is then
obtained by transporting along the equivalence, and the `T`-linear equivalence is assembled by
replacing the `map_smul'` field, so no `Module` instance is ever rewritten and the kernel sees no
`Eq.mpr`.
-/

@[expose] public noncomputable section

open TensorProduct

namespace Stacks.TensorProductPushout

universe u v w x y

variable (R : Type u) (A : Type v) (B : Type w) (M : Type x) (N : Type y)
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

/-! ### The action of `B` on `M ⊗_R N` through the right factor -/

/-- The representation of `B` on `M ⊗[R] N` by its action on the right factor: `b` acts as
`id_M ⊗ (b • ·)`. This is the ring homomorphism underlying
`Stacks.TensorProductPushout.rightModule`. -/
def rightEnd : B →+* Module.End R (M ⊗[R] N) where
  toFun b := LinearMap.lTensor M (Algebra.lsmul R R N b : N →ₗ[R] N)
  map_one' := by
    change LinearMap.lTensor M (Algebra.lsmul R R N 1 : N →ₗ[R] N) = LinearMap.id
    rw [map_one, Module.End.one_eq_id, LinearMap.lTensor_id]
  map_mul' b b' := by
    change LinearMap.lTensor M (Algebra.lsmul R R N (b * b') : N →ₗ[R] N) =
      (LinearMap.lTensor M (Algebra.lsmul R R N b : N →ₗ[R] N)).comp
        (LinearMap.lTensor M (Algebra.lsmul R R N b' : N →ₗ[R] N))
    rw [map_mul]
    exact LinearMap.lTensor_comp _ _ _
  map_zero' := by simp
  map_add' b b' := by simp

/-- The action of `B` on `M ⊗[R] N` through the right factor, `b • (m ⊗ n) = m ⊗ (b • n)`. -/
@[instance_reducible]
def rightModule : Module B (M ⊗[R] N) :=
  Module.compHom _ (rightEnd R B M N)

attribute [local instance 10] rightModule

/-- Under `Stacks.TensorProductPushout.rightModule`, `b • (m ⊗ n) = m ⊗ (b • n)`. -/
@[simp]
theorem rightModule_smul_tmul (b : B) (m : M) (n : N) :
    (b • (m ⊗ₜ[R] n) : M ⊗[R] N) = m ⊗ₜ[R] (b • n) := rfl

/-- The `R`-action on `M ⊗[R] N` factors through the `B`-action of
`Stacks.TensorProductPushout.rightModule`. -/
theorem rightModule_isScalarTower : IsScalarTower R B (M ⊗[R] N) where
  smul_assoc r b x := by
    induction x <;> simp_all [smul_assoc, TensorProduct.tmul_smul]

attribute [local instance] rightModule_isScalarTower

/-- The `A`-action on the left factor of `M ⊗[R] N` and the `B`-action on the right factor
commute. -/
@[ega "III 6.4.1" "special case"]
theorem smulCommClass_right : SMulCommClass A B (M ⊗[R] N) where
  smul_comm a b x := by
    induction x <;> simp_all [TensorProduct.smul_tmul']

attribute [local instance] smulCommClass_right

/-! ### The action of `A ⊗_R B` on `M ⊗_R N` -/

/-- The action of `A ⊗[R] B` on `M ⊗[R] N`, with `A` acting through the left factor and `B`
through the right factor: `(a ⊗ b) • (m ⊗ n) = (a • m) ⊗ (b • n)`. It is
`TensorProduct.Algebra.module` for the commuting actions `TensorProduct.leftModule` and
`Stacks.TensorProductPushout.rightModule`. -/
@[instance_reducible, ega "III 6.4.1" "special case"]
def pushoutModule : Module (A ⊗[R] B) (M ⊗[R] N) :=
  TensorProduct.Algebra.module

attribute [local instance 10] pushoutModule

/-- Under `Stacks.TensorProductPushout.pushoutModule`, a pure tensor `a ⊗ b` acts on `x` as
`a • b • x`. -/
@[simp]
theorem pushoutModule_smul_apply (a : A) (b : B) (x : M ⊗[R] N) :
    ((a ⊗ₜ[R] b : A ⊗[R] B) • x) = a • b • x := rfl

/-- For the action of `Stacks.TensorProductPushout.pushoutModule`, a pure tensor of `A ⊗[R] B`
acts on a pure tensor of `M ⊗[R] N` factor by factor: `(a ⊗ b) • (m ⊗ n) = (a • m) ⊗ (b • n)`. -/
@[simp]
theorem pushoutModule_smul_tmul_tmul (a : A) (b : B) (m : M) (n : N) :
    ((a ⊗ₜ[R] b : A ⊗[R] B) • (m ⊗ₜ[R] n) : M ⊗[R] N) = (a • m) ⊗ₜ[R] (b • n) := rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The structure map `B → A ⊗[R] B` of `Algebra.TensorProduct.rightAlgebra` is `b ↦ 1 ⊗ b`. -/
theorem pushoutModule_algebraMap_apply (b : B) :
    algebraMap B (A ⊗[R] B) b = 1 ⊗ₜ[R] b :=
  Algebra.TensorProduct.right_algebraMap_apply b

/-- The `B`-action on `M ⊗[R] N` is the restriction of the `A ⊗[R] B`-action along
`b ↦ 1 ⊗ b`. -/
theorem pushoutModule_isScalarTower : IsScalarTower B (A ⊗[R] B) (M ⊗[R] N) :=
  IsScalarTower.of_algebraMap_smul fun b x => by
    rw [pushoutModule_algebraMap_apply (A := A), pushoutModule_smul_apply, one_smul]

attribute [local instance] pushoutModule_isScalarTower

/-! ### The cancellation, `A ⊗_R B`-linearly -/

variable {M N}

/-- The inverse of `Stacks.TensorProductPushout.cancelBaseChange` commutes with the action of
`A ⊗[R] B`. -/
theorem cancelBaseChange_symm_smul (c : A ⊗[R] B) (z : M ⊗[R] N) :
    (cancelBaseChange R A B M N).symm (c • z) =
      c • (cancelBaseChange R A B M N).symm z := by
  induction c with
  | zero => rw [zero_smul, zero_smul, map_zero]
  | add c c' hc hc' => rw [add_smul, map_add, hc, hc', add_smul]
  | tmul a b =>
    induction z with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
    | tmul m n =>
      rw [pushoutModule_smul_tmul_tmul, cancelBaseChange_symm_tmul, cancelBaseChange_symm_tmul,
        TensorProduct.smul_tmul' (R := A ⊗[R] B),
        show ((a ⊗ₜ[R] b : A ⊗[R] B) • ((1 : A ⊗[R] B) ⊗ₜ[A] m) : (A ⊗[R] B) ⊗[A] M)
            = (a ⊗ₜ[R] b : A ⊗[R] B) ⊗ₜ[A] m by
          rw [TensorProduct.smul_tmul' (R := A), smul_eq_mul, mul_one]]
      refine (cancelBaseChange R A B M N).injective ?_
      rw [cancelBaseChange_one_tmul, show (1 : A ⊗[R] B) = 1 ⊗ₜ[R] 1 from
          Algebra.TensorProduct.one_def, cancelBaseChange_tmul_tmul, mul_one, mul_one]

/-- `Stacks.TensorProductPushout.cancelBaseChange` commutes with the action of `A ⊗[R] B`. -/
theorem cancelBaseChange_smul (c : A ⊗[R] B)
    (x : ((A ⊗[R] B) ⊗[A] M) ⊗[A ⊗[R] B] ((A ⊗[R] B) ⊗[B] N)) :
    cancelBaseChange R A B M N (c • x) = c • cancelBaseChange R A B M N x :=
  (cancelBaseChange R A B M N).symm.injective <| by
    rw [LinearEquiv.symm_apply_apply, cancelBaseChange_symm_smul,
      LinearEquiv.symm_apply_apply]

variable (M N)

/-- **Cancelling both base changes to `A ⊗_R B`, `A ⊗_R B`-linearly.** For commutative
`R`-algebras `A` and `B`, an `A`-module `M` and a `B`-module `N`, the tensor product over
`T = A ⊗_R B` of the base changes of `M` and of `N` to `T` is the tensor product of `M` and `N`
over `R`, as `T`-modules — `T` acting on `M ⊗_R N` by
`(a ⊗ b) • (m ⊗ n) = (a • m) ⊗ (b • n)`.

This is `Stacks.TensorProductPushout.cancelBaseChange`, which is stated `R`-linearly, with its
`map_smul'` field replaced; so the underlying function, its inverse, and all of its computation
rules are unchanged. -/
def cancelBaseChangePushout :
    ((A ⊗[R] B) ⊗[A] M) ⊗[A ⊗[R] B] ((A ⊗[R] B) ⊗[B] N) ≃ₗ[A ⊗[R] B] M ⊗[R] N :=
  { cancelBaseChange R A B M N with map_smul' := cancelBaseChange_smul R A B }

/-- `Stacks.TensorProductPushout.cancelBaseChangePushout` agrees with
`Stacks.TensorProductPushout.cancelBaseChange` as a function. -/
@[simp]
theorem cancelBaseChangePushout_apply
    (x : ((A ⊗[R] B) ⊗[A] M) ⊗[A ⊗[R] B] ((A ⊗[R] B) ⊗[B] N)) :
    cancelBaseChangePushout R A B M N x = cancelBaseChange R A B M N x := rfl

/-- The inverse of `Stacks.TensorProductPushout.cancelBaseChangePushout` agrees with the inverse
of `Stacks.TensorProductPushout.cancelBaseChange` as a function. -/
@[simp]
theorem cancelBaseChangePushout_symm_apply (z : M ⊗[R] N) :
    (cancelBaseChangePushout R A B M N).symm z = (cancelBaseChange R A B M N).symm z := rfl

variable {M N}

/-- `Stacks.TensorProductPushout.cancelBaseChangePushout` sends `(1 ⊗ m) ⊗ (1 ⊗ n)` to `m ⊗ n`. -/
theorem cancelBaseChangePushout_one_tmul (m : M) (n : N) :
    cancelBaseChangePushout R A B M N
        (((1 : A ⊗[R] B) ⊗ₜ m) ⊗ₜ ((1 : A ⊗[R] B) ⊗ₜ n)) = m ⊗ₜ n :=
  cancelBaseChange_one_tmul R A B m n

/-- The inverse of `Stacks.TensorProductPushout.cancelBaseChangePushout` sends `m ⊗ n` to
`(1 ⊗ m) ⊗ (1 ⊗ n)`. -/
theorem cancelBaseChangePushout_symm_tmul (m : M) (n : N) :
    (cancelBaseChangePushout R A B M N).symm (m ⊗ₜ n) =
      ((1 : A ⊗[R] B) ⊗ₜ m) ⊗ₜ ((1 : A ⊗[R] B) ⊗ₜ n) :=
  cancelBaseChange_symm_tmul R A B m n

/-- `Stacks.TensorProductPushout.cancelBaseChangePushout` sends `((a ⊗ b) ⊗ m) ⊗ ((a' ⊗ b') ⊗ n)`
to `((a * a') • m) ⊗ ((b * b') • n)`. -/
theorem cancelBaseChangePushout_tmul_tmul (a a' : A) (b b' : B) (m : M) (n : N) :
    cancelBaseChangePushout R A B M N (((a ⊗ₜ b) ⊗ₜ m) ⊗ₜ ((a' ⊗ₜ b') ⊗ₜ n)) =
      ((a * a') • m) ⊗ₜ ((b * b') • n) :=
  cancelBaseChange_tmul_tmul R A B a a' b b' m n

end Stacks.TensorProductPushout

end
