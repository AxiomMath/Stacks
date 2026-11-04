module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Inverting an element commutes with a change of base ring

Let `R → T` be a map of commutative rings, let `r : R`, let `A` be the localization of `R` away
from `r` and let `B` be the localization of `T` away from the image of `r`. Then

`A ⊗_R T ≅ B`.

This file provides that identification *as an explicit map* `A ⊗_R T → B`, namely the one
sending a pure tensor `a ⊗ t` to the product of the image of `a` under
`IsLocalization.Away.map` with the image of `t` in `B`, together with the proof that it is
bijective. The explicit map is what a statement natural in further data — for instance in an
object of a site, where `R`, `T`, `A` and `B` are the sections of four presheaves — needs: the
`Algebra` and `IsScalarTower` instances are chosen one base ring at a time, so an isomorphism
produced by a universal property is not usable until it has been pinned to a formula.

## Main definitions

* `IsLocalization.Away.tensorBaseChangeMap`: the comparison `A ⊗_R T → B`, with
  `IsLocalization.Away.tensorBaseChangeMap_tmul` its value on a pure tensor.

## Main results

* `IsLocalization.Away.bijective_tensorBaseChangeMap`: **the comparison is bijective.**

## Implementation notes

Bijectivity is the uniqueness of a localization of modules, not a computation: `A ⊗_R T` and
`B` are both localizations of the `R`-module `T` at the powers of `r` — the first by
`IsLocalization.tensorProduct_isLocalizedModule`, the second by
`isLocalizedModule_iff_isLocalization` — and the comparison is a map between them commuting with
the two structure maps, so `IsLocalizedModule.ext` identifies it with
`IsLocalizedModule.linearEquiv`.

`IsLocalization.Away.tensorRightEquiv` of Mathlib is the same isomorphism, but only as an
`AlgEquiv` onto `Localization.Away (algebraMap R T r)` obtained from
`IsLocalization.algEquiv`; it says nothing about which map it is, and its `Algebra` structure on
`A ⊗_R T` is `Algebra.TensorProduct.rightAlgebra`, which is a local instance in Mathlib.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace IsLocalization.Away

variable {R T A B : Type u} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R T] [Algebra T B] [Algebra R B] [IsScalarTower R T B]
  (r : R) [IsLocalization.Away r A] [IsLocalization.Away (algebraMap R T r) B]

/-- The map `A → B` induced by `R → T` on the localizations away from `r` carries the image of
`x : R` in `A` to its image in `B`. -/
theorem map_algebraMap (x : R) :
    IsLocalization.Away.map A B (algebraMap R T) r (algebraMap R A x) = algebraMap R B x :=
  (IsLocalization.map_eq _ x).trans (IsScalarTower.algebraMap_apply R T B x).symm

/-- **The comparison `A ⊗_R T → B`** between the base change to `T` of the localization of `R`
away from `r` and the localization of `T` away from the image of `r`: on a pure tensor it is
the product of the two images in `B`. -/
def tensorBaseChangeMap : A ⊗[R] T →ₗ[R] B :=
  TensorProduct.lift <| LinearMap.mk₂ R
    (fun a t => IsLocalization.Away.map A B (algebraMap R T) r a * algebraMap T B t)
    (fun a₁ a₂ t => by rw [map_add, add_mul])
    (fun c a t => by
      rw [Algebra.smul_def, map_mul, map_algebraMap, Algebra.smul_def, mul_assoc])
    (fun a t₁ t₂ => by rw [map_add, mul_add])
    (fun c a t => by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def,
        mul_left_comm])

/-- The comparison `A ⊗_R T → B` sends `a ⊗ t` to the product of the image of `a` under
`IsLocalization.Away.map` and the image of `t` in `B`. -/
@[simp]
theorem tensorBaseChangeMap_tmul (a : A) (t : T) :
    tensorBaseChangeMap (B := B) r (a ⊗ₜ[R] t) =
      IsLocalization.Away.map A B (algebraMap R T) r a * algebraMap T B t :=
  TensorProduct.lift.tmul _ _

/-- **Inverting an element commutes with a change of base ring**: the comparison
`A ⊗_R T → B` is bijective.

Both sides are localizations of the `R`-module `T` at the powers of `r`, and the comparison
commutes with the two maps out of `T`, so it is the canonical isomorphism between them. -/
theorem bijective_tensorBaseChangeMap :
    Function.Bijective (tensorBaseChangeMap (T := T) (A := A) (B := B) r) := by
  let f := (IsScalarTower.toAlgHom R T B).toLinearMap
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers r) (TensorProduct.mk R A T 1) f
  have key : tensorBaseChangeMap (T := T) (A := A) (B := B) r = e.toLinearMap := by
    refine IsLocalizedModule.ext (Submonoid.powers r) (TensorProduct.mk R A T 1)
      (IsLocalizedModule.map_units f) ?_
    ext t
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      IsLocalizedModule.linearEquiv_apply, TensorProduct.mk_apply, tensorBaseChangeMap_tmul,
      map_one, one_mul]
    rfl
  rw [key]
  exact e.bijective

/-- The comparison `A ⊗_R T → B`, as a linear equivalence. -/
def tensorBaseChangeEquiv : (A ⊗[R] T) ≃ₗ[R] B :=
  LinearEquiv.ofBijective (tensorBaseChangeMap r) (bijective_tensorBaseChangeMap r)

/-- The linear equivalence `tensorBaseChangeEquiv` agrees with `tensorBaseChangeMap`. -/
@[simp]
theorem tensorBaseChangeEquiv_apply (x : A ⊗[R] T) :
    tensorBaseChangeEquiv (B := B) r x = tensorBaseChangeMap r x := rfl

end IsLocalization.Away

end
