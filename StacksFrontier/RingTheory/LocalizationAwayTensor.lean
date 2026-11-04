module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor product of two localizations away from elements

Let `A` be a commutative ring and let `f`, `g` be elements of `A`. Inverting `f` and inverting
`g` independently, then tensoring over `A`, inverts the product:

`A[1/f] ⊗_A A[1/g] = A[1/(f g)]`.

## Main results

* `IsLocalization.Away.isLocalization_tensorProduct`: **the tensor product of a localization
  away from `f` and a localization away from `g` is a localization away from `f * g`.**
* `IsLocalization.Away.tensorProductAlgEquiv`: consequently it is isomorphic, as an
  `A`-algebra, to any localization away from `f * g`.
* `IsLocalization.Away.tensorProductAlgEquiv_tmul`: that isomorphism carries a pure tensor to
  the product of the images of its two factors, which pins it down.

## Implementation notes

There is no computation. `IsLocalization.Away.tensor` says that base change of a localization
away from `g` along any `A`-algebra `A[1/f]` is a localization of `A[1/f]` away from the image
of `g`, so `A[1/f] ⊗_A A[1/g]` is one; and `IsLocalization.Away.mul'` says that an iterated
localization is a localization at the product. Any two localizations at one multiplicative set
are isomorphic as algebras over the base, by `IsLocalization.algEquiv`.

The description on a pure tensor is not read off the construction either: both the comparison
and the multiplication map `x ⊗ y ↦ x · y` are `A`-algebra maps out of `A[1/f] ⊗_A A[1/g]`,
which is a localization of `A`, and `IsLocalization.algHom_subsingleton` says there is at most
one such map. So the two agree, and the multiplication map computes pure tensors by
`Algebra.TensorProduct.lift_tmul`.
-/

@[expose] public noncomputable section

open TensorProduct

namespace IsLocalization.Away

variable {A : Type*} [CommRing A] (f g : A)
  (Af Ag Afg : Type*) [CommRing Af] [CommRing Ag] [CommRing Afg]
  [Algebra A Af] [Algebra A Ag] [Algebra A Afg]

/-- **The tensor product of a localization away from `f` and a localization away from `g` is a
localization away from `f * g`.** -/
theorem isLocalization_tensorProduct [IsLocalization.Away f Af] [IsLocalization.Away g Ag] :
    IsLocalization.Away (f * g) (Af ⊗[A] Ag) :=
  IsLocalization.Away.mul' Af (Af ⊗[A] Ag) f g

/-- **`A[1/f] ⊗_A A[1/g] = A[1/(f g)]`**, as an isomorphism of `A`-algebras with any
localization of `A` away from `f * g`. -/
@[ega "III 6.7.1" "special case"]
def tensorProductAlgEquiv [IsLocalization.Away f Af] [IsLocalization.Away g Ag]
    [IsLocalization.Away (f * g) Afg] :
    (Af ⊗[A] Ag) ≃ₐ[A] Afg :=
  have := isLocalization_tensorProduct f g Af Ag
  IsLocalization.algEquiv (Submonoid.powers (f * g)) (Af ⊗[A] Ag) Afg

/-- The canonical map `A[1/f] ⟶ A[1/(f g)]`, as an `A`-algebra map. -/
def toMulLeft [IsLocalization.Away f Af] [IsLocalization.Away (f * g) Afg] : Af →ₐ[A] Afg where
  __ := (IsLocalization.Away.awayToAwayRight f g : Af →+* Afg)
  commutes' a := IsLocalization.Away.awayToAwayRight_eq f g a

/-- The canonical map `A[1/g] ⟶ A[1/(f g)]`, as an `A`-algebra map. -/
def toMulRight [IsLocalization.Away g Ag] [IsLocalization.Away (f * g) Afg] : Ag →ₐ[A] Afg where
  __ := (IsLocalization.Away.awayToAwayLeft g f : Ag →+* Afg)
  commutes' a := IsLocalization.Away.awayToAwayLeft_eq g f a

/-- Multiplication of the two canonical maps, as an `A`-algebra map out of the tensor product. -/
def tensorProductMul [IsLocalization.Away f Af] [IsLocalization.Away g Ag]
    [IsLocalization.Away (f * g) Afg] : (Af ⊗[A] Ag) →ₐ[A] Afg :=
  Algebra.TensorProduct.lift (toMulLeft f g Af Afg) (toMulRight f g Ag Afg)
    (fun _ _ => mul_comm _ _)

/-- **The comparison carries a pure tensor to the product of the images of its factors.** -/
theorem tensorProductAlgEquiv_tmul [IsLocalization.Away f Af] [IsLocalization.Away g Ag]
    [IsLocalization.Away (f * g) Afg] (x : Af) (y : Ag) :
    tensorProductAlgEquiv f g Af Ag Afg (x ⊗ₜ[A] y) =
      toMulLeft f g Af Afg x * toMulRight f g Ag Afg y := by
  have := isLocalization_tensorProduct f g Af Ag
  have h : (tensorProductAlgEquiv f g Af Ag Afg : (Af ⊗[A] Ag) →ₐ[A] Afg) =
      tensorProductMul f g Af Ag Afg :=
    (IsLocalization.algHom_subsingleton (Submonoid.powers (f * g))).elim _ _
  exact DFunLike.congr_fun h (x ⊗ₜ[A] y)

end IsLocalization.Away

end
