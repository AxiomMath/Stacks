module

public import Mathlib.RingTheory.AdjoinRoot
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The spectrum of a root extension stays below the cutoff

`AdequateFunctor.size_lt_of_spec_adjoinRoot` is the size bound for the algebras obtained by
adjoining a root of a polynomial: if the spectrum of `R` has size below an uncountable strong
prelimit cutoff, then so does the spectrum of `AdjoinRoot p` for every `p : R[X]`.

This is the companion of `AdequateFunctor.size_lt_of_spec_symmetricAlgebra` and
`AdequateFunctor.size_lt_of_spec_laurentPolynomial`, and like them it is an instance of the
unconditional clause (9)(b) of [Stacks, Tag 000R]: `AdjoinRoot p` is `R[X]/(p)`, generated as an
`R`-algebra by the single element `AdjoinRoot.root p`, hence of finite type over `R`, so
`AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType` applies.

## Implementation notes

The statement is made for an arbitrary polynomial, with no monicity hypothesis. Monicity is what
makes `AdjoinRoot p` finite *free* over `R`, and that is how the quadratic unit extension
`X ^ 2 - C b * X + 1` of [Stacks, Tag 06V5] is used elsewhere; but finite freeness is strictly
more than this bound needs. Being a quotient of `R[X]` makes `AdjoinRoot p` a one-generator
`R`-algebra for every `p`, including `p = 0`, so `Algebra.FiniteType R (AdjoinRoot p)` holds
unconditionally and carrying a `p.Monic` hypothesis would only narrow the lemma for nothing.

No `@[stacks]` attribute is placed here: the tagged statement of clause (9)(b) is
`AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType`, and this is that statement specialized to
a root extension.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 06V5](https://stacks.math.columbia.edu/tag/06V5)
* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AdequateFunctor

variable {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hsl : Cardinal.IsStrongPrelimit κ)

include hκ hsl in
/-- The spectrum of the algebra obtained from a ring `R` by adjoining a root of a polynomial
`p : R[X]` has size below an uncountable strong prelimit cutoff as soon as the spectrum of `R`
does: `AdjoinRoot p` is the quotient `R[X]/(p)`, generated over `R` by the root alone, so it is
of finite type and this is [Stacks, Tag 000R] (9)(b).

No hypothesis on `p` is needed; in particular the quadratic unit extension
`X ^ 2 - C b * X + 1` of [Stacks, Tag 06V5] is covered. -/
public theorem size_lt_of_spec_adjoinRoot (R : Type u) [CommRing R] (p : Polynomial R)
    (hR : (Spec (CommRingCat.of R)).size < κ) :
    (Spec (CommRingCat.of (AdjoinRoot p))).size < κ :=
  Scheme.size_Spec_lt_of_finiteType hκ hsl R (AdjoinRoot p) hR

end AdequateFunctor
