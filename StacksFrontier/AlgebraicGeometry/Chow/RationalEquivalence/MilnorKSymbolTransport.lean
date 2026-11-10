module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTransport
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.Transport

/-!
# The two transports of Milnor K-theory along an isomorphism of fields agree

Milnor K-theory carries two transports along a ring homomorphism of fields in this library.
`milnorKTransport` is the functoriality of `MilnorKTheory` in the field, defined in every degree
from the presentation of the Milnor K-ring as a quotient of a tensor algebra; it is what
`Stacks.Chow.milnorChainComap` and `Stacks.Chow.milnorChainExtend` move chains with. In degrees
one and two there are also the transports `Stacks.Chow.milnorKOneRingEquiv` and
`Stacks.Chow.milnorKTwoRingEquiv` of an *isomorphism* of fields, built from the presentations by
the unit group and by the tensor square modulo the Steinberg relations; those are the transports
along which `Stacks.Chow.milnorKTwoTameSymbol_ringEquiv` moves the tame-symbol boundary of
Stacks 0GU9.

This file proves that for an isomorphism of fields the two agree, in both degrees. That is what
lets the degreewise localization sequence of Stacks 0GUA be compared with the first differential
of the complex of Stacks 0GU9: the chains move by `milnorKTransport`, the boundary moves by
`Stacks.Chow.milnorKTwoTameSymbol_ringEquiv`, and without this comparison the two cannot meet.

## Main results

* `Stacks.Chow.milnorKTransport_eq_milnorKOneRingEquiv` — in degree one the two transports agree.
* `Stacks.Chow.milnorKTransport_milnorKTwoPureSymbol` — `milnorKTransport` sends a pure symbol to
  the pure symbol of the images.
* `Stacks.Chow.milnorKTransport_eq_milnorKTwoRingEquiv` — in degree two the two transports agree.

## Implementation notes

The degree-one comparison is immediate from the naturality
`milnorKTheoryOneAddEquiv_milnorKTransport` of the identification of the degree-one group with
the unit group. The degree-two comparison is reduced to a pure symbol by
`AlgebraicGeometry.milnorKTwo_induction`; the computation of `milnorKTransport` on a pure symbol
goes through the observation that the pure symbol is the image of `f ⊗ g` under the comparison
map `milnorKTwoToKGroup`, whose value in the Milnor K-ring is the class of `ι f * ι g`, and
`milnorKTensorMap` is an algebra homomorphism sending `ι a` to `ι` of the transported unit.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Stacks.Chow

variable {k₁ k₂ : Type u} [Field k₁] [Field k₂]

/-! ### Degree one -/

/-- **In degree one the functorial transport is the transport along the unit group.** Both are
read through the identification of the degree-one Milnor K-group with the unit group of the
field. -/
theorem milnorKTransport_eq_milnorKOneRingEquiv (φ : k₁ ≃+* k₂) (y : MilnorKTheory k₁ 1) :
    milnorKTransport (φ : k₁ →+* k₂) 1 y = milnorKOneRingEquiv φ y := by
  apply (milnorKTheoryOneAddEquiv k₂).injective
  rw [milnorKTheoryOneAddEquiv_milnorKTransport]
  change milnorKUnitsMap (φ : k₁ →+* k₂) (milnorKTheoryOneAddEquiv k₁ y) =
    milnorKTheoryOneAddEquiv k₂
      ((milnorKTheoryOneAddEquiv k₂).symm
        ((MulEquiv.toAdditive (Units.mapEquiv φ.toMulEquiv))
          (milnorKTheoryOneAddEquiv k₁ y)))
  rw [AddEquiv.apply_symm_apply]
  rfl

/-! ### Degree two -/

/-- The pure symbol is the image of the tensor `f ⊗ g` under the comparison map from the tensor
square of the unit group to the degree-two Milnor K-group. -/
theorem milnorKTwoPureSymbol_eq_milnorKTwoToKGroup (k : Type u) [Field k] (f g : kˣ) :
    milnorKTwoPureSymbol k f g =
      milnorKTwoToKGroup k (Additive.ofMul f ⊗ₜ[ℤ] Additive.ofMul g) := by
  apply (milnorKTwoEquivTensorProductQuotient k).injective
  rw [milnorKTwoEquivTensorProductQuotient_toKGroup, milnorKTwoPureSymbol,
    LinearEquiv.apply_symm_apply]

/-- The class of the pure symbol in the Milnor K-ring is the class of the product of the two
generators of the tensor algebra. -/
theorem coe_milnorKTwoPureSymbol (k : Type u) [Field k] (f g : kˣ) :
    ((milnorKTwoPureSymbol k f g : MilnorKTheory k 2) : MilnorKRing k) =
      (milnorKSteinbergIdeal k).ringCon.mk'
        (TensorAlgebra.ι ℤ (Additive.ofMul f) * TensorAlgebra.ι ℤ (Additive.ofMul g)) := by
  rw [milnorKTwoPureSymbol_eq_milnorKTwoToKGroup]
  change (milnorKSteinbergIdeal k).ringCon.mk'
      (milnorKTwoTensorMap k (Additive.ofMul f ⊗ₜ[ℤ] Additive.ofMul g)) = _
  rw [milnorKTwoTensorMap_tmul]

/-- **The functorial transport sends a pure symbol to the pure symbol of the images.** -/
theorem milnorKTransport_milnorKTwoPureSymbol (φ : k₁ →+* k₂) (f g : k₁ˣ) :
    milnorKTransport φ 2 (milnorKTwoPureSymbol k₁ f g) =
      milnorKTwoPureSymbol k₂ (Units.map (φ : k₁ →* k₂) f) (Units.map (φ : k₁ →* k₂) g) := by
  refine Subtype.ext ?_
  change milnorKRingMap φ ((milnorKTwoPureSymbol k₁ f g : MilnorKTheory k₁ 2) : MilnorKRing k₁) =
    ((milnorKTwoPureSymbol k₂ (Units.map (φ : k₁ →* k₂) f)
      (Units.map (φ : k₁ →* k₂) g) : MilnorKTheory k₂ 2) : MilnorKRing k₂)
  rw [coe_milnorKTwoPureSymbol, coe_milnorKTwoPureSymbol, milnorKRingMap_mk', map_mul,
    milnorKTensorMap_ι, milnorKTensorMap_ι, milnorKUnitsMap_ofMul, milnorKUnitsMap_ofMul]

/-- **In degree two the functorial transport is the transport along the presentation by the
tensor square.** Both send a pure symbol to the pure symbol of the images, and the degree-two
Milnor K-group is generated by pure symbols. -/
theorem milnorKTransport_eq_milnorKTwoRingEquiv (φ : k₁ ≃+* k₂) (α : MilnorKTheory k₁ 2) :
    milnorKTransport (φ : k₁ →+* k₂) 2 α = milnorKTwoRingEquiv φ α := by
  induction α using milnorKTwo_induction with
  | hsymb f g =>
      rw [milnorKTransport_milnorKTwoPureSymbol, milnorKTwoRingEquiv_pureSymbol]
      rfl
  | hadd a b ha hb => rw [map_add, map_add, ha, hb]

end Stacks.Chow

end
