module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.CartierCentre

/-!
# Blowing up an effective Cartier divisor

Blowing up a scheme along an effective Cartier divisor changes nothing: the blowup morphism
is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_blowUpToBase_of_isEffectiveCartierDivisor`: the blowup morphism of
  a scheme in an effective Cartier divisor is an isomorphism.

## Implementation notes

The assertion of the source, that the blowup "is the identity morphism of `X`", means that the
canonical structure morphism of the blowup is an isomorphism over the base, not that the scheme
underlying the blowup is definitionally `X`. Both `X` itself and the blowup are terminal in the
category of `X`-schemes along which the centre becomes an effective Cartier divisor
(`Stacks.Blowup.isTerminal_blowUp`), so the two comparison morphisms are mutually inverse.

## References

* [Stacks Project, Tag 0807](https://stacks.math.columbia.edu/tag/0807)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0807.** The blowup of a scheme in an effective Cartier divisor is
the scheme itself: its blowup morphism is an isomorphism.

This is `Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor` of
`StacksFrontier/AlgebraicGeometry/Blowup/CartierCentre.lean`, where the proof and the tag live;
the name is kept in this namespace because consumers of this file use it unqualified. -/
theorem isIso_blowUpToBase_of_isEffectiveCartierDivisor {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) : IsIso (blowUpToBase I) :=
  Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor I hI

end AlgebraicGeometry

end
