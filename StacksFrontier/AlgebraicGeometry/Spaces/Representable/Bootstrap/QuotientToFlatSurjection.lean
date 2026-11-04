module

public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatChartAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.StatementSpellings

/-!
# The quotient form of Stacks 04S6 implies representability descent along flat surjections

`StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/StatementSpellings.lean` sorts the
library's spellings of the bootstrap theorem **Stacks 04S6** into two families — the
*flat-surjection* family, "a sheaf receiving a morphism from an algebraic space which is
representable by algebraic spaces, surjective, flat and locally of finite presentation is an
algebraic space", and the *quotient* family, "the quotient sheaf of a flat, locally finitely
presented equivalence relation of algebraic spaces is an algebraic space".

The connection in the direction the source's proof provides — the quotient form implies the
flat-surjection form, the source's passage from condition (5) to case (1) read backwards — is
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf` of
`StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/FlatChartAlgebraic.lean`, and for
the spelling the Stacks chapter carries it is
`AlgebraicGeometry.Stack.bootstrap04S6Spaces_of_quotientSheaf`.  This module adds the third member
of the flat-surjection family.

The converse is *not* available: it would need the quotient map `U ⟶ U/R` to be representable by
algebraic spaces, which in this library is known only once `U/R` is already an algebraic space,
as the introduction to `AlgebraicGeometry.Space.Bootstrap04S6QuotientSheaf` records.

## Main results

* `isRepresentabilityDescentAlongFlatSurjection_of_bootstrap04S6QuotientSheaf`: the quotient
  spelling implies `AlgebraicGeometry.Space.IsRepresentabilityDescentAlongFlatSurjection`.

## Implementation notes

Nothing here registers a tag and nothing here proves Stacks 04S6: the statement proved is an
implication between two statements the library does not have, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/StatementSpellings.lean`.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The quotient spelling of Stacks 04S6 implies the third member of the flat-surjection
family.**

`AlgebraicGeometry.Space.IsRepresentabilityDescentAlongFlatSurjection` is the hypothesis of
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_isPullback_of_descent`, and is the
same statement as the other two by
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection_iff`. -/
theorem isRepresentabilityDescentAlongFlatSurjection_of_bootstrap04S6QuotientSheaf
    (h04S6 : Bootstrap04S6QuotientSheaf B S hS) :
    IsRepresentabilityDescentAlongFlatSurjection B S hS :=
  isRepresentabilityDescentAlongFlatSurjection_of_bootstrap B S hS
    (isBootstrapAlgebraicSpaceAlongFlatSurjection_of_quotientSheaf B S hS h04S6)

end AlgebraicGeometry.Space

end
