module

public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of a module along a pushout square of commutative rings

Let

    A  ⟶  B
    |      |
    A' ⟶  B'

be a pushout square of commutative rings, so that `B'` is `B ⊗_A A'`, and let `M` be a
`B`-module. Then `M` may be base changed to `A'` along `A ⟶ A'`, giving `A' ⊗_A M`, or to
`B'` along `B ⟶ B'`, giving `B' ⊗_B M`, and the canonical `A'`-linear map from the first to
the second is bijective.

Equivalently, the `A`-linear map `m ↦ 1 ⊗ m` from `M` to `B' ⊗_B M` exhibits `B' ⊗_B M` as the
base change of `M` along `A ⟶ A'`.

## Main definitions

* `Stacks.Algebra.PushoutBaseChange.can`: the canonical `A'`-linear map
  `A' ⊗_A M ⟶ B' ⊗_B M`, sending `a' ⊗ m` to `algebraMap A' B' a' ⊗ m`.
* `Stacks.Algebra.PushoutBaseChange.linearEquiv`: the resulting `A'`-linear equivalence
  `A' ⊗_A M ≃ B' ⊗_B M`.

## Main results

* `Stacks.Algebra.PushoutBaseChange.isBaseChange_mk_one`: `B' ⊗_B M` is the base change of the
  `A`-module `M` along `A ⟶ A'`.
* `Stacks.Algebra.PushoutBaseChange.bijective_can`: the canonical map is bijective.

## Implementation notes

The map `can` is defined by the universal property of `A' ⊗_A M` as a base change. It agrees on
pure tensors with the additive bijection `linearEquivAux`, the composite of `TensorProduct.comm`
on either end with `IsBaseChange.tensorEquiv` for the base change `B' = B ⊗_A A'`, an
isomorphism `M ⊗_B B' ≃ M ⊗_A A'` of `B`-modules.

## What is not done

**This file is pure commutative algebra and proves no assertion of any Stacks tag; no project
tag attribute is attached.**  It says nothing about schemes, quasi-coherent modules or
base-change morphisms of direct images; the geometric statement that consumes it is not
proved here.  In particular the bridge from a pushout square in `CommRingCat` to the
`Algebra.IsPushout` hypothesis used here is not built here either.
-/

@[expose] public section

open TensorProduct

namespace Stacks.Algebra.PushoutBaseChange

variable {A B A' B' M : Type*}
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra B B'] [Algebra A' B']
  [IsScalarTower A B B'] [IsScalarTower A A' B']
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

section Can

variable (A B A' B' M)

/-- The canonical `A'`-linear map `A' ⊗_A M ⟶ B' ⊗_B M`, obtained from the `A`-linear map
`m ↦ 1 ⊗ m` by the universal property of the base change `A' ⊗_A M`. -/
noncomputable def can : A' ⊗[A] M →ₗ[A'] B' ⊗[B] M :=
  (TensorProduct.isBaseChange (R := A) (S := A') (M := M)).lift
    ((TensorProduct.mk B B' M 1).restrictScalars A)

variable {A B A' B' M}

/-- The map `can` sends `1 ⊗ m` to `1 ⊗ m`. -/
@[simp]
lemma can_one_tmul (m : M) : can A B A' B' M ((1 : A') ⊗ₜ[A] m) = (1 : B') ⊗ₜ[B] m :=
  (TensorProduct.isBaseChange (R := A) (S := A') (M := M)).lift_eq _ m

/-- The map `can` sends `a' ⊗ m` to `algebraMap A' B' a' ⊗ m`. -/
lemma can_tmul (a' : A') (m : M) :
    can A B A' B' M (a' ⊗ₜ[A] m) = (algebraMap A' B' a') ⊗ₜ[B] m := by
  have h1 : a' ⊗ₜ[A] m = a' • ((1 : A') ⊗ₜ[A] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : a' • ((1 : B') ⊗ₜ[B] m) = (algebraMap A' B' a') ⊗ₜ[B] m := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  rw [h1, map_smul, can_one_tmul, h2]

end Can

section Bijective

variable [Algebra.IsPushout A B A' B']

variable (A B A' B' M) in
/-- An additive bijection `A' ⊗_A M ≃ B' ⊗_B M` assembled from `TensorProduct.comm` and the
base change `B' = B ⊗_A A'`. -/
noncomputable def linearEquivAux : A' ⊗[A] M ≃+ B' ⊗[B] M :=
  (TensorProduct.comm A A' M).toAddEquiv.trans
    ((((Algebra.IsPushout.out (R := A) (S := B) (R' := A') (S' := B')).tensorEquiv
        M).symm).toAddEquiv.trans (TensorProduct.comm B M B').toAddEquiv)

/-- The bijection `linearEquivAux` sends `a' ⊗ m` to `algebraMap A' B' a' ⊗ m`. -/
lemma linearEquivAux_tmul (a' : A') (m : M) :
    linearEquivAux A B A' B' M (a' ⊗ₜ[A] m) = (algebraMap A' B' a') ⊗ₜ[B] m := by
  simp [linearEquivAux, IsBaseChange.tensorEquiv, IsScalarTower.toAlgHom_apply]

/-- The map `can` agrees with the additive bijection `linearEquivAux`. -/
lemma can_eq_linearEquivAux (x : A' ⊗[A] M) :
    can A B A' B' M x = linearEquivAux A B A' B' M x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a' m => rw [can_tmul, linearEquivAux_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The canonical map `A' ⊗_A M ⟶ B' ⊗_B M` attached to a pushout square is bijective. -/
theorem bijective_can : Function.Bijective (can A B A' B' M) := by
  have h : (can A B A' B' M : A' ⊗[A] M → B' ⊗[B] M) = linearEquivAux A B A' B' M :=
    funext can_eq_linearEquivAux
  rw [h]
  exact (linearEquivAux A B A' B' M).bijective

variable (A B A' B' M) in
/-- **Base change of a module along a pushout square of commutative rings.** The canonical
`A'`-linear map `A' ⊗_A M ⟶ B' ⊗_B M` is an isomorphism. -/
noncomputable def linearEquiv : (A' ⊗[A] M) ≃ₗ[A'] (B' ⊗[B] M) :=
  LinearEquiv.ofBijective (can A B A' B' M) bijective_can

/-- The equivalence `linearEquiv` sends `a' ⊗ m` to `algebraMap A' B' a' ⊗ m`. -/
@[simp]
lemma linearEquiv_tmul (a' : A') (m : M) :
    linearEquiv A B A' B' M (a' ⊗ₜ[A] m) = (algebraMap A' B' a') ⊗ₜ[B] m :=
  can_tmul a' m

/-- `B' ⊗_B M` is the base change of the `A`-module `M` along `A ⟶ A'`: base change of a module
commutes with a pushout square of commutative rings. -/
theorem isBaseChange_mk_one :
    IsBaseChange A' ((TensorProduct.mk B B' M (1 : B')).restrictScalars A) :=
  IsBaseChange.of_equiv (linearEquiv A B A' B' M) fun m => can_one_tmul m

end Bijective

end Stacks.Algebra.PushoutBaseChange

end
