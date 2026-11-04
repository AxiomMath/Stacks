module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentable
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorClosedImmersion

/-!
# The affine representability reduction with its closed-immersion input discharged

`StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentable` reduces
representability of the degree-`d` Hilbert functor of an affine scheme over an affine base to
two cited inputs, both carried there as named hypotheses of type
`Stacks.Hilbert.ClosedImmersionRepresentability` and
`Stacks.Hilbert.AffineSpaceRepresentability`. One of the two is in fact available in this
development. This file supplies it and restates the reduction with only the other one left.

## Main results

* `Stacks.Hilbert.closedImmersionRepresentability` — the proposition
  `Stacks.Hilbert.ClosedImmersionRepresentability` is inhabited, i.e. the content of Stacks
  Tag 0B97 holds here.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isAffine'` — the reduction step with
  that input supplied rather than assumed, leaving representability for an affine space over an
  affine base as the only antecedent.

## Implementation notes

The content of Stacks Tag 0B97 is proved in this development, by
`Stacks.Hilbert.exists_closedSubschemeRepresentingHilbertFunctor` of
`StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorClosedImmersion`, whose conclusion is the
structure `Stacks.Hilbert.ClosedSubschemeRepresentingHilbertFunctor`. The stand-in
`Stacks.Hilbert.ClosedImmersionRepresentability` differs from it only in taking the closed
immersion hypothesis as an explicit argument rather than as an instance, so inhabiting the
stand-in is a matter of reinstating the instance. The remark in the imported module that this
proposition is not proved here is superseded by `closedImmersionRepresentability` below; the
proposition itself is retained because the theorems there take it as an argument, and they can
now be handed the real term.

The other input, `Stacks.Hilbert.AffineSpaceRepresentability`, is the case of affine space,
which the source proves by an explicit universal construction. That construction is absent, and
nothing in this development inhabits the proposition, so it stays a hypothesis of the theorem
below. It is worth noting that it is an instance of the very conclusion being proved, an affine
space over an affine base being affine; what is established is therefore the source's reduction
step and not the universal construction that makes the affine-space case true.

For that reason no Stacks tag is registered in this file. The Stacks 0B99 registration lives on
the declaration in the imported base module, which carries the note recording what that
reduction is conditional on; the two results here prove only the reduction, not representability
outright, so neither is a carrier for the tag.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 0B97](https://stacks.math.columbia.edu/tag/0B97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Hilbert

/-! ### The closed-immersion input -/

/-- **Stacks 0B97, in the form `ClosedImmersionRepresentability` asserts it.** The Hilbert
functor of a closed subscheme is represented by a closed subscheme of the representing scheme of
the ambient one. This is `exists_closedSubschemeRepresentingHilbertFunctor` with the closed
immersion hypothesis moved from an instance to an explicit argument. -/
theorem closedImmersionRepresentability : ClosedImmersionRepresentability.{u} :=
  fun i hi d H_Y hY =>
    haveI := hi
    exists_closedSubschemeRepresentingHilbertFunctor i d H_Y hY

/-! ### The reduction with that input supplied -/

/-- **The source's reduction step for Stacks Tag 0B99, with the Stacks 0B97 input discharged.**
Let `X ⟶ S` be a morphism of affine schemes and let `d` be a natural number. Then the degree-`d`
Hilbert functor of points of `X` over `S` is represented by a scheme over `S`, given
representability for an affine space over an affine base.

This is `exists_representsHilbertFunctorOfRank_of_isAffine` with its first hypothesis supplied
rather than assumed: the content of Stacks 0B97 holds in this development, in the form
`closedImmersionRepresentability`. Over an affine base, `X` is a closed subscheme of an affine
space, and its Hilbert functor is therefore represented by a closed subscheme of the Hilbert
scheme of that affine space. Only the affine-space case remains an antecedent. -/
theorem exists_representsHilbertFunctorOfRank_of_isAffine' {S : Scheme.{u}} [IsAffine S]
    (X : Over S) [IsAffine X.left] (d : ℕ)
    (hAffineSpace : AffineSpaceRepresentability.{u}) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) :=
  exists_representsHilbertFunctorOfRank_of_isAffine X d closedImmersionRepresentability
    hAffineSpace

end Stacks.Hilbert

end
