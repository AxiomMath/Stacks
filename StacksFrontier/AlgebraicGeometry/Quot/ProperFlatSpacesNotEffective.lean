module

public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpaces
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationEssSurjLargeHoms

/-!
# Non-effective formal objects of the stack of proper flat algebraic spaces

The stack `p'_{fp, flat, proper} : Spaces'_{fp, flat, proper} ⟶ (Sch/S)_{fppf}` of Stacks 0D1D
(`AlgebraicGeometry.cartesianProperFlatProjection`) is fibred in groupoids (Stacks 0D1E). By
Stacks 07X8 every formal object of an algebraic stack is effective. This file records the
contrapositive for `p'_{fp, flat, proper}`: one formal object of it that is not effective makes
it fail to be an algebraic stack. This is the deduction in the proof of Stacks 0D1R.

## Main results

* `AlgebraicGeometry.not_isAlgebraicStack_cartesianProperFlatProjection_of_not_isEffective`:
  a formal object of `p'_{fp, flat, proper}` that is not effective shows that
  `p'_{fp, flat, proper}` is not an algebraic stack.

## References

* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The stack `p'_{fp, flat, proper}` of Stacks 0D1D, as a category over the big fppf site
of `S`. -/
abbrev cartesianProperFlatBasedCategory : BasedCategory (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (cartesianProperFlatProjection B S hS)

/-- If the stack `p'_{fp, flat, proper}` of finitely presented, flat and proper algebraic
spaces over the big fppf site of `S` has a formal object (Stacks 07X3) that is not effective
(Stacks 07X7), then it is not an algebraic stack. This is Stacks 07X8, the effectiveness of
formal objects of algebraic stacks, read contrapositively. -/
theorem not_isAlgebraicStack_cartesianProperFlatProjection_of_not_isEffective
    (ξ : Deformation.Artin.FormalObject B S hS (cartesianProperFlatProjection B S hS))
    (hξ : ¬ Deformation.Artin.FormalObject.IsEffective B S hS
      (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) ξ) :
    ¬ Stack.IsAlgebraicStack.{u, w} B S hS (cartesianProperFlatBasedCategory B S hS) :=
  fun h ↦ hξ (Deformation.Artin.FormalObject.isEffective_of_isAlgebraicStack_largeHoms
    (cartesianProperFlatBasedCategory B S hS) h ξ)

end AlgebraicGeometry

end
