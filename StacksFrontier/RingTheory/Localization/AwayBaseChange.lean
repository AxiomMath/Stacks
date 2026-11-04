module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The base change of a localization away from an element

Let `A' → A` and `A' → P'` be ring maps, let `g ∈ P'` and let `(P')_g` be the localization of
`P'` at `g`. The base change `(P')_g ⊗_{A'} A` is the localization of `P = P' ⊗_{A'} A` at the
image of `g`: cancelling the base change identifies it with `(P')_g ⊗_{P'} P`, which is a
localization of `P` because localization is stable under base change.

This is the square used by the localization step of Stacks 0DZ2: the thickening `P' → P` of
Stacks 0DZ2 localizes to the thickening `(P')_g → P_g` with the same kernel.

## Main results

* `IsLocalization.Away.tensorBaseChange`: `(P')_g ⊗_{A'} A` is the localization of
  `P' ⊗_{A'} A` at the image of `g`.

## Implementation notes

The `P' ⊗_{A'} A`-algebra structure on `(P')_g ⊗_{A'} A` is a hypothesis rather than a
definition, pinned down by the formula `x ⊗ a ↦ (x/1) ⊗ a` on generators; this lets a caller
use whichever structure it has already built.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace IsLocalization.Away

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The base change of a localization away from an element.** Let `g ∈ P'`, let `Pg'` be the
localization of `P'` at `g`, and give `Pg' ⊗_{A'} A` the `P' ⊗_{A'} A`-algebra structure sending
`x ⊗ a` to `(x/1) ⊗ a`. Then `Pg' ⊗_{A'} A` is the localization of `P' ⊗_{A'} A` at the image
of `g`. -/
theorem tensorBaseChange (A' A P' Pg' : Type u) [CommRing A'] [CommRing A] [CommRing P']
    [CommRing Pg'] [Algebra A' A] [Algebra A' P'] [Algebra A' Pg'] [Algebra P' Pg']
    [IsScalarTower A' P' Pg'] (g : P') [IsLocalization.Away g Pg']
    [Algebra (TensorProduct A' P' A) (TensorProduct A' Pg' A)]
    (hmap : ∀ (x : P') (a : A),
      algebraMap (TensorProduct A' P' A) (TensorProduct A' Pg' A) (x ⊗ₜ[A'] a) =
        (algebraMap P' Pg' x) ⊗ₜ[A'] a) :
    IsLocalization.Away (algebraMap P' (TensorProduct A' P' A) g)
      (TensorProduct A' Pg' A) := by
  have hΦ : ∀ p : TensorProduct A' P' A,
      Algebra.TensorProduct.cancelBaseChange A' P' P' Pg' A
          (algebraMap (TensorProduct A' P' A)
            (TensorProduct P' Pg' (TensorProduct A' P' A)) p) =
        algebraMap (TensorProduct A' P' A) (TensorProduct A' Pg' A) p := by
    intro p
    induction p using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul x a =>
        have h1 : algebraMap (TensorProduct A' P' A)
            (TensorProduct P' Pg' (TensorProduct A' P' A)) (x ⊗ₜ[A'] a) =
            (1 : Pg') ⊗ₜ[P'] (x ⊗ₜ[A'] a) := rfl
        rw [h1, Algebra.TensorProduct.cancelBaseChange_tmul, hmap x a, Algebra.smul_def,
          mul_one]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  exact IsLocalization.isLocalization_of_algEquiv
    (Submonoid.powers (algebraMap P' (TensorProduct A' P' A) g))
    (AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.cancelBaseChange A' P' P' Pg' A).toRingEquiv) hΦ)

end IsLocalization.Away

end
