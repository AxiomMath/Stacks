module

public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange.ComparisonMap
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange.KernelPair
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange.Representability

/-!
# Part (6) of Stacks 03FN: the base change trivialising the twisted doubled origin

Part (6) of the example asks for a surjective, finite, étale morphism `S' ⟶ S` such that the
base change `X' = S' ×_S X` is a scheme. Take `S' = U = Spec K[x]`, the chart itself: it is
surjective, finite and étale over `S`, and `U ×_S X` is two copies of `U` glued along the
puncture, that is, the total space of
`Stacks.Examples.doubleSectionCover (cover K) (puncturedCover K)`.

Pulling the quotient `X = U/R` back along `U ⟶ S` presents `X'` as the quotient of the
self-product `U ×_S U` by the base change of `R`; the self-product is two copies of `U`
(`coverFiberProductSplitIso`), and the induced relation is exactly the gluing relation of two
copies of `U` along the puncture. The representability criterion of Stacks 03C5 then identifies
that quotient with the functor of points of the glued scheme.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.uToBase`: the chart, as a scheme over the base via
  its own structure morphism.
* `AlgebraicGeometry.TwistedDoubledOrigin.doubledOverBase`: the glued scheme of part (6),
  as a scheme over the base, via the projection to `U` followed by the chart map.
* `AlgebraicGeometry.TwistedDoubledOrigin.doubledChartsToGluedOverBase`: the map from two
  copies of the chart to the glued scheme, sending each copy to its chart of the gluing datum,
  as a morphism over the base, and
  `AlgebraicGeometry.TwistedDoubledOrigin.doubledSelfProductToGlued`: the same map read on the
  self-product of the chart, which is the comparison map `f''` of the base-change argument.
* `AlgebraicGeometry.TwistedDoubledOrigin.doubledRelation`: the base change of the twisted
  relation along `U ⟶ S`, a pre-relation on `U ×_S U`.
* `AlgebraicGeometry.TwistedDoubledOrigin.baseChangePresheaf`: the base change
  `X' = S' ×_S X`, formed in presheaves on the big fppf site of the base.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.surjective_isFinite_etale_and_baseChange_isScheme`:
  **Stacks 03FN, part (6)** — the chart is surjective, finite and étale over the base, and the
  base change of the quotient along it is the functor of points of the glued scheme, hence a
  scheme.
* `AlgebraicGeometry.TwistedDoubledOrigin.isPullback_doubledChartsToGlued`: the kernel pair of
  the map from two copies of the chart to the glued scheme, as four blocks.
* `AlgebraicGeometry.TwistedDoubledOrigin.isPullback_doubledRelation`: the base-changed
  relation *is* that kernel pair, which is the second hypothesis of Stacks 03C5.
* `AlgebraicGeometry.TwistedDoubledOrigin.exists_isIso_baseChangePresheaf`: the glued scheme
  represents the base change.

## Implementation notes

**The two groupings of the four blocks.** The kernel pair of the comparison map has four
summands, indexed by a pair of chart labels; the two applications of distributivity of pullback
over a binary coproduct which compute `U ×_S R` produce them grouped by *relation summand*
instead, and on one block the two parametrisations of the puncture differ by the Galois
automorphism. `coprodShuffle` and a reparametrisation by
`galoisActionPuncturedMap` mediate; `coverRelationSplitIso` is the resulting identification.

**Why the base change needs no new descent input.** The comparison map of part (6) is an fppf
covering, so it is a local surjection on functors of points
(`AlgebraicGeometry.isLocallySurjective_points_map_of_fppf`), and the base-changed relation is
its kernel pair *on the nose*, so the second hypothesis of Stacks 03C5 holds because the
comparison map to the chosen fibre square is an isomorphism. On the other side, the map from the
quotient presheaf of the base-changed relation to `X'` is a base change of the quotient map
`U ⟶ X`, hence locally surjective, and it is *injective* — not merely locally so — because
`Stacks.Groupoids.isPullback_toQuotientSheaf_self` exhibits the relation as the kernel pair of
that quotient map by a Cartesian square of presheaves, which is Cartesian in every degree. Two
locally bijective maps out of one presheaf into sheaves identify their targets, which is
`CategoryTheory.Presheaf.isIso_of_isLocallyBijective_fac`.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
* [Stacks Project, Tag 03C5](https://stacks.math.columbia.edu/tag/03C5)
-/
