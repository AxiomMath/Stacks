module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalAffineComplement

/-!
# The complement of a locally principal closed subscheme is affine over the scheme

Let `X` be a scheme and `Z ⊆ X` a locally principal closed subscheme, presented by its
ideal-sheaf data `I`.  Then the complementary open immersion `X ∖ Z → X` is an affine morphism.
This is [Stacks, Tag 07ZT](https://stacks.math.columbia.edu/tag/07ZT), and applied to an
effective Cartier divisor it is the affineness half of
[Stacks, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU), whose density half is
`Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor`.

## Main results

* `Stacks.Divisors.isAffineHom_compl_of_isLocallyPrincipal`: **Tag 07ZT.**
* `Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor`:
  **Tag 07ZU, affineness.**

## Implementation notes

The source argument is: affineness is local on the target (Morphisms, Tag 01S8), so one may
assume `X = Spec A` and `Z = V(f)`, and then `X ∖ Z = D(f) = Spec A_f` is affine.  That argument
is already carried out, for an arbitrary open presenting the complement and with the hypothesis
weakened to the support being locally a zero locus, in
`StacksFrontier/AlgebraicGeometry/Divisors/LocallyPrincipalAffineComplement.lean`, so Tag 07ZT here
is `Stacks.Divisors.isAffineHom_ι_compl_support_of_isLocallyPrincipal` from that file.

For the divisor case the locally principal hypothesis is supplied by
`Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor`; nothing about
nonzerodivisors is needed, since affineness does not use regularity of the local equation.

## References

* [Stacks Project, Tag 07ZT](https://stacks.math.columbia.edu/tag/07ZT)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Stacks Project, Tag 07ZT.**  The open complement of a locally principal closed subscheme
is affine over the ambient scheme. -/
@[stacks 07ZT]
theorem isAffineHom_compl_of_isLocallyPrincipal (hI : IsLocallyPrincipal I) :
    IsAffineHom (Scheme.Opens.ι I.support.compl) :=
  isAffineHom_ι_compl_support_of_isLocallyPrincipal I hI

/-- **Stacks Project, Tag 07ZU (affineness).**  The complement of an effective Cartier divisor
is affine over the ambient scheme: an effective Cartier divisor is locally principal, so Tag
07ZT applies. -/
@[stacks 07ZU "affineness"]
theorem isAffineHom_compl_of_isEffectiveCartierDivisor (hI : IsEffectiveCartierDivisor I) :
    IsAffineHom (Scheme.Opens.ι I.support.compl) :=
  isAffineHom_compl_of_isLocallyPrincipal I
    (isLocallyPrincipal_of_isEffectiveCartierDivisor I hI)

end Stacks.Divisors

end
