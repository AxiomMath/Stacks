module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier

/-!
# The sum of two effective Cartier divisors

Let `S` be a scheme. The *sum* of two effective Cartier divisors is the closed subscheme cut out
by the product of their ideal sheaves; Mathlib's `Mul` instance on
`AlgebraicGeometry.Scheme.IdealSheafData` already is that construction, on all quasi-coherent
ideal sheaves, and `AlgebraicGeometry.Scheme.IdealSheafData.ideal_mul` identifies its ideal on
every affine open with the product of the two ideals. No effective-Cartier hypothesis is needed
to form the sum, which is why Tag 01WT is recorded against those Mathlib declarations rather
than against new ones, and why this file contains no declaration of its own.

## Implementation notes

The remaining operations of this part of the source are elsewhere. The condition
`Stacks.Divisors.IsPullbackDefined` under which the pullback of an effective Cartier divisor
along `f : X ⟶ Y` is defined — that the scheme-theoretic inverse image `D.comap f` is again an
effective Cartier divisor — is Tag 01WV, in
`StacksFrontier/AlgebraicGeometry/DivisorFlatPullback/Basic.lean`, which also proves that it
holds whenever `f` is flat. That local principality is always preserved,
`Stacks.Divisors.isLocallyPrincipal_comap`, is Tag 053P, in
`StacksFrontier/AlgebraicGeometry/LocallyPrincipalPullback/Basic.lean`. The relative notion
`Stacks.Divisors.IsRelativeEffectiveCartierDivisor` over a base, Tag 062T, is in
`StacksFrontier/AlgebraicGeometry/Picard/RelativeEffectiveCartier.lean`.

## References

* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

add_to_stacks 01WT "product ideal sheaf" AlgebraicGeometry.Scheme.IdealSheafData.instMul
add_to_stacks 01WT "ideal of the sum" AlgebraicGeometry.Scheme.IdealSheafData.ideal_mul

end
