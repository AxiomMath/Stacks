module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import StacksCore.Tactic.StacksAttribute

/-!
# Associativity of tensor products with a bimodule in the middle

Stacks Lemma 00D2: let `A`, `B` be rings, `M` an `A`-module, `P` a `B`-module and `N` an
`(A, B)`-bimodule (Stacks 00D1: an `A`-module and a `B`-module whose actions commute,
`SMulCommClass A B N`). Then `(M ⊗_A N) ⊗_B P` and `M ⊗_A (N ⊗_B P)` are both
`(A, B)`-bimodules, and they are isomorphic, as `A`-modules and as `B`-modules via the same map.

No ring map between `A` and `B` is assumed, so this is not Mathlib's
`TensorProduct.AlgebraTensorModule.assoc`, which needs `Algebra B A` and a scalar tower on `N`.

## The bimodule structures

On `M ⊗_A N` the ring `A` acts through `M` (Mathlib's `TensorProduct.leftModule`). The ring `B`
acts through the right factor, `(x ⊗ y) b = x ⊗ y b`, as in the source's proof; Mathlib has no
instance for an action through the right factor, because when `B = A` it would form a non-defeq
diamond with `TensorProduct.leftModule`. It is `TensorProduct.rightModule` below, a definition made
a low-priority local instance in this file (low, so that for `B = A` the `A`-action through `M`
is still the one found). On `N ⊗_B P` both rings act through `N` (`TensorProduct.leftModule`),
and the outer tensor products then carry the structures obtained in the same two ways.

## Main results

* `TensorProduct.rightModule`: `S` acts on `M ⊗[R] N` through `N`.
* `TensorProduct.smulCommClass_rightModule`: the `R''`-action through `M` and the `S`-action through
  `N` commute, so `M ⊗[R] N` is a bimodule.
* `TensorProduct.smulCommClass_bimoduleAssoc_left`,
  `TensorProduct.smulCommClass_bimoduleAssoc_right`: the two triple tensor products are
  `(A, B)`-bimodules.
* `TensorProduct.bimoduleAssoc`: the `A`-linear isomorphism
  `(M ⊗_A N) ⊗_B P ≃ M ⊗_A (N ⊗_B P)`, and `TensorProduct.bimoduleAssocRight`, the same map as a
  `B`-linear isomorphism.

## References

* [StacksProject 00D2](https://stacks.math.columbia.edu/tag/00D2), Lemma 10.12.7.
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

section RightModule

variable {R S R'' M N : Type*} [CommSemiring R] [Semiring S] [Semiring R'']
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Module S N]
  [SMulCommClass R S N]

/-- `S` acts on `M ⊗[R] N` through the right factor: `s • (m ⊗ n) = m ⊗ (s • n)`.

This is `TensorProduct.leftModule` on `N ⊗[R] M` transported along `TensorProduct.comm`. It is not
an instance: for `S = R` it would be a second, non-defeq, `R`-module structure on `M ⊗[R] N`. -/
@[instance_reducible]
noncomputable def rightModule : Module S (M ⊗[R] N) :=
  (TensorProduct.comm R M N).toAddEquiv.module S

attribute [local instance low] rightModule

theorem rightModule_smul_tmul (s : S) (m : M) (n : N) : s • (m ⊗ₜ[R] n) = m ⊗ₜ[R] (s • n) := rfl

/-- The action through the left factor and the action through the right factor commute. -/
theorem smulCommClass_rightModule [Module R'' M] [SMulCommClass R R'' M] :
    SMulCommClass R'' S (M ⊗[R] N) where
  smul_comm r s x := by
    induction x with
    | tmul m n => rw [rightModule_smul_tmul, smul_tmul', smul_tmul', rightModule_smul_tmul]
    | add x y hx hy => rw [smul_add, smul_add, hx, hy, smul_add, smul_add]

end RightModule

section BimoduleAssoc

variable {A B M N P : Type*} [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup P] [Module B P]
  [AddCommGroup N] [Module A N] [Module B N] [SMulCommClass A B N]

attribute [local instance low] rightModule
attribute [local instance] smulCommClass_rightModule

omit [Module B P] in
/-- `B` acts on `M ⊗[A] N` through `N` and `A` through `M`: the actions commute, in this order. -/
theorem smulCommClass_rightModule_symm : SMulCommClass B A (M ⊗[A] N) := .symm _ _ _

omit [AddCommGroup M] [Module A M] [Module B P] in
/-- The actions of `B` and `A` on `N` commute, in this order. -/
theorem smulCommClass_symm_of_bimodule : SMulCommClass B A N := .symm _ _ _

attribute [local instance] smulCommClass_rightModule_symm smulCommClass_symm_of_bimodule


/-- **Stacks 00D2**, the bimodule structure on `(M ⊗_A N) ⊗_B P`: here `B` acts on `M ⊗_A N`
through `N`, and `A` and `B` act on the outer tensor product through its left factor. -/
@[stacks 00D2 "The `(A, B)`-bimodule structure on `(M ⊗_A N) ⊗_B P`: `A` acts through `M`, `B` \
through `N` (`TensorProduct.rightModule`), and the two actions commute."]
theorem smulCommClass_bimoduleAssoc_left : SMulCommClass A B ((M ⊗[A] N) ⊗[B] P) :=
  inferInstance

/-- **Stacks 00D2**, the bimodule structure on `M ⊗_A (N ⊗_B P)`: here `A` and `B` act on
`N ⊗_B P` through `N`, `A` acts on the outer tensor product through `M` and `B` through
`N ⊗_B P`. -/
@[stacks 00D2 "The `(A, B)`-bimodule structure on `M ⊗_A (N ⊗_B P)`: `A` acts through `M`, `B` \
through `N` (`TensorProduct.rightModule`), and the two actions commute."]
theorem smulCommClass_bimoduleAssoc_right : SMulCommClass A B (M ⊗[A] (N ⊗[B] P)) :=
  smulCommClass_rightModule

/-- The `A`-linear map `n ↦ n ⊗ p` from `N` to `N ⊗[B] P`. -/
noncomputable def tmulRightA (p : P) : N →ₗ[A] N ⊗[B] P where
  toFun n := n ⊗ₜ p
  map_add' n n' := add_tmul n n' p
  map_smul' a n := (smul_tmul' (R := B) a n p).symm

@[simp]
theorem tmulRightA_apply (p : P) (n : N) : tmulRightA (A := A) p n = n ⊗ₜ[B] p := rfl

/-- The `B`-linear map `n ↦ m ⊗ n` from `N` to `M ⊗[A] N`, with `B` acting through `N`. -/
noncomputable def tmulLeftB (m : M) : N →ₗ[B] M ⊗[A] N where
  toFun n := m ⊗ₜ n
  map_add' n n' := tmul_add m n n'
  map_smul' b n := (rightModule_smul_tmul b m n).symm

@[simp]
theorem tmulLeftB_apply (m : M) (n : N) : tmulLeftB (B := B) m n = m ⊗ₜ[A] n := rfl

/-- The forward map `(m ⊗ n) ⊗ p ↦ m ⊗ (n ⊗ p)`, as an additive map. -/
noncomputable def bimoduleAssocFun : (M ⊗[A] N) ⊗[B] P →+ M ⊗[A] (N ⊗[B] P) :=
  liftAddHom
    { toFun x :=
        { toFun p := (tmulRightA p).lTensor M x
          map_zero' := by
            induction x with
            | tmul m n => simp
            | add x y hx hy => simp_all
          map_add' p p' := by
            induction x with
            | tmul m n => simp [tmul_add]
            | add x y hx hy => simp only [map_add, hx, hy]; abel }
      map_zero' := by ext; simp
      map_add' x y := by ext; simp }
    fun b x p => by
      induction x with
      | tmul m n => simp [rightModule_smul_tmul, smul_tmul]
      | add x y hx hy => simp_all [smul_add]

@[simp]
theorem bimoduleAssocFun_tmul (m : M) (n : N) (p : P) :
    bimoduleAssocFun ((m ⊗ₜ[A] n) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] p) := rfl

/-- The inverse map `m ⊗ (n ⊗ p) ↦ (m ⊗ n) ⊗ p`, as an additive map. -/
noncomputable def bimoduleAssocInvFun : M ⊗[A] (N ⊗[B] P) →+ (M ⊗[A] N) ⊗[B] P :=
  liftAddHom
    { toFun m := ((tmulLeftB m).rTensor P).toAddMonoidHom
      map_zero' := by ext y; induction y with
        | tmul n p => simp
        | add x y hx hy => simp_all
      map_add' m m' := by ext y; induction y with
        | tmul n p => simp [add_tmul]
        | add x y hx hy => simp only [AddMonoidHom.add_apply, map_add] at *; rw [hx, hy] }
    fun a m y => by
      induction y with
      | tmul n p => rw [smul_tmul' (R := B)]; simp [smul_tmul]
      | add x y hx hy => simp_all [smul_add]

@[simp]
theorem bimoduleAssocInvFun_tmul (m : M) (n : N) (p : P) :
    bimoduleAssocInvFun (m ⊗ₜ[A] (n ⊗ₜ[B] p)) = (m ⊗ₜ[A] n) ⊗ₜ[B] p := rfl

/-- **Stacks 00D2**: for an `A`-module `M`, a `B`-module `P` and an `(A, B)`-bimodule `N`,
`(M ⊗_A N) ⊗_B P ≅ M ⊗_A (N ⊗_B P)` via `(m ⊗ n) ⊗ p ↦ m ⊗ (n ⊗ p)`, an `A`-linear isomorphism.
The same map is `B`-linear: `TensorProduct.bimoduleAssocRight`. -/
@[stacks 00D2 "The isomorphism `(M ⊗_A N) ⊗_B P ≅ M ⊗_A (N ⊗_B P)` for an `(A, B)`-bimodule \
`N`, with no ring map between `A` and `B`, as an `A`-linear isomorphism; the same map as a \
`B`-linear isomorphism is `TensorProduct.bimoduleAssocRight`."]
noncomputable def bimoduleAssoc : ((M ⊗[A] N) ⊗[B] P) ≃ₗ[A] M ⊗[A] (N ⊗[B] P) where
  toFun := bimoduleAssocFun
  invFun := bimoduleAssocInvFun
  map_add' := map_add _
  map_smul' a z := by
    induction z with
    | tmul x p =>
      induction x with
      | tmul m n => simp [smul_tmul']
      | add x y hx hy => simp_all [add_tmul, smul_add]
    | add x y hx hy => simp_all [smul_add]
  left_inv z := by
    induction z with
    | tmul x p =>
      induction x with
      | tmul m n => simp
      | add x y hx hy => simp_all [add_tmul]
    | add x y hx hy => simp_all
  right_inv z := by
    induction z with
    | tmul m y =>
      induction y with
      | tmul n p => simp
      | add x y hx hy => simp_all [tmul_add]
    | add x y hx hy => simp_all

@[simp]
theorem bimoduleAssoc_tmul (m : M) (n : N) (p : P) :
    bimoduleAssoc ((m ⊗ₜ[A] n) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] p) := rfl

@[simp]
theorem bimoduleAssoc_symm_tmul (m : M) (n : N) (p : P) :
    bimoduleAssoc.symm (m ⊗ₜ[A] (n ⊗ₜ[B] p)) = (m ⊗ₜ[A] n) ⊗ₜ[B] p := rfl

/-- **Stacks 00D2**: the isomorphism `(M ⊗_A N) ⊗_B P ≅ M ⊗_A (N ⊗_B P)` is also `B`-linear. -/
theorem bimoduleAssoc_smul_right (b : B) (z : (M ⊗[A] N) ⊗[B] P) :
    bimoduleAssoc (b • z) = b • bimoduleAssoc z := by
  induction z with
  | tmul x p =>
    rw [smul_tmul']
    induction x with
    | tmul m n => simp [rightModule_smul_tmul, smul_tmul']
    | add x y hx hy => simp_all [add_tmul, smul_add]
  | add x y hx hy => simp_all [smul_add]

/-- **Stacks 00D2**: `bimoduleAssoc` as a `B`-linear isomorphism; its underlying map is that of
the `A`-linear `bimoduleAssoc` (`bimoduleAssocRight_toAddEquiv`), so the two triple tensor
products are isomorphic as `A`-modules and as `B`-modules via the same mapping. -/
@[stacks 00D2 "The isomorphism `(M ⊗_A N) ⊗_B P ≅ M ⊗_A (N ⊗_B P)` as a `B`-linear \
isomorphism; its underlying additive equivalence is that of the `A`-linear \
`TensorProduct.bimoduleAssoc`."]
noncomputable def bimoduleAssocRight : ((M ⊗[A] N) ⊗[B] P) ≃ₗ[B] M ⊗[A] (N ⊗[B] P) where
  __ := (bimoduleAssoc (A := A) (B := B) (M := M) (N := N) (P := P)).toAddEquiv
  map_smul' := bimoduleAssoc_smul_right

theorem bimoduleAssocRight_toAddEquiv :
    (bimoduleAssocRight (A := A) (B := B) (M := M) (N := N) (P := P)).toAddEquiv =
      bimoduleAssoc.toAddEquiv := rfl

end BimoduleAssoc

end TensorProduct
