module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection

/-!
# Minimal non-schematic algebraic spaces are reduced

Let `X` be an algebraic space over a scheme `S` which is not a scheme, and assume every closed
subspace of `X` other than `X` itself is a scheme. Then `X` is reduced. This is the reducedness
half of Stacks 0B7Z. This file has no declarations; see *Main results*.

Being a scheme is `CategoryTheory.Functor.IsRepresentable` of the presheaf underlying the space,
as in `StacksFrontier/AlgebraicGeometry/Spaces/SchemeOfIntegralBijection.lean`. A *proper* closed
subspace is a closed subspace `Z` with `Z ≠ ⊤` as a subfunctor — strictly smaller than the whole
space in the scheme-theoretic sense, which is the meaning of "proper closed subspace `Z ⊂ X`" in
the source and has nothing to do with the morphism property of being proper. The distinction
matters here: the reduction of `X` has *every* point of `X`, so it is not a proper closed subset
of `|X|`, and it is exactly the proper closed subspace the argument is applied to.

## Main definitions

No new definitions are introduced.

## Main results

None. Stacks 0B7Z, with both of its conclusions, is proved, in the namespace
`AlgebraicGeometry.Space`, as
`hasEtaleLocalProperty_isReduced_and_irreducibleSpace_of_forall_ne_top_isRepresentable`
in `StacksFrontier/AlgebraicGeometry/Spaces/MinimalNonSchematicSpaceReducedIrreducible.lean`.

## References

* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 07VU](https://stacks.math.columbia.edu/tag/07VU)
* [Stacks Project, Tag 0B7Z](https://stacks.math.columbia.edu/tag/0B7Z)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.Space

end
