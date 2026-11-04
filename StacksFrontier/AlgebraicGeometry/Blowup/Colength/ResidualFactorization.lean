module

public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.PositiveOrder
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference

/-!
# The residual ideal left by the exceptional divisor

If the pull-back of an ideal sheaf to a blowup is contained in the `d`-th power of the exceptional
ideal, it is that power times a residual ideal sheaf: the exceptional ideal is an effective
Cartier divisor ([Stacks, Tag 02OS]), and a containment in a power of an effective Cartier divisor
is a factorization through it. The residual factor is the quotient ideal sheaf
`(I·𝒪_X) : (dE)`, the source's `I·𝒪_X(dE)` read without the twist.

## Main results

* `Stacks.Blowup.Colength.exists_exceptionalIdeal_pow_mul_eq_comap`: the splitting of clause (2)
  of [Stacks, Tag 0AGT].

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace Stacks.Blowup.Colength

/-- The pulled-back ideal sheaf is the `d`-th power of the exceptional divisor times a residual
ideal sheaf on the blowup, whenever it is contained in that power. The residual factor is the
quotient `(J·𝒪_X) : (dE)`, the source's `I·𝒪_X(dE)`. -/
@[stacks 0AGT "clause (2), the splitting: the pulled-back ideal is the d-th power of the \
exceptional divisor times a residual ideal sheaf"]
public theorem exists_exceptionalIdeal_pow_mul_eq_comap
    {X : Scheme} (M J : X.IdealSheafData) (d : ℕ)
    (horder : J.comap (blowUpToBase M) ≤ exceptionalIdeal M ^ d) :
    ∃ J' : (blowUp M).IdealSheafData,
      exceptionalIdeal M ^ d * J' = J.comap (blowUpToBase M) :=
  ⟨_, AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor _ _
    (Stacks.Divisors.isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal M) d) horder⟩

end Stacks.Blowup.Colength

end
