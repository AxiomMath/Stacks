module

public import StacksFrontier.AlgebraicGeometry.Groupoids.EquivalenceRelation.InvolutionGraph
public import StacksFrontier.AlgebraicGeometry.Groupoids.EquivalenceRelation.Slice
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginEtaleRelation

/-!
# The projections of the twisted relation on the affine line

The quotient construction of the Galois twist of the affine line with zero doubled takes the
pre-relation `AlgebraicGeometry.TwistedDoubledOrigin.twistedRelation` — the diagonal together
with the twisted diagonal away from the origin — and forms the quotient sheaf of the chart by
it. This file reads the two projections of that pre-relation in the category of schemes, where
they are descents out of the coproduct of the chart with its puncture, and identifies them with
the composites of the relation and the two projections of the self-product of the chart.

That `Stacks.Groupoids.IsEtaleEquivalenceRelation` holds of the pre-relation — the hypothesis
every statement about the quotient consumes — is
`AlgebraicGeometry.TwistedDoubledOrigin.twistedRelation_isEtaleEquivalenceRelation`, in
`StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginEtaleRelation`.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.relationFirst_left` and
  `AlgebraicGeometry.TwistedDoubledOrigin.relationSecond_left`: the two projections of the
  twisted relation, read in the category of schemes as descents out of the coproduct.
* `AlgebraicGeometry.TwistedDoubledOrigin.twistedRelation_left_comp_prod_fst` and
  `AlgebraicGeometry.TwistedDoubledOrigin.twistedRelation_left_comp_prod_snd`: composing the
  relation with a projection of the self-product of the chart gives that projection of the
  relation.

## Implementation notes

The relation object is `AlgebraicGeometry.TwistedDoubledOrigin.relationScheme`, a coproduct of
*schemes* carrying a structure morphism to the base, so each projection is a `coprod.desc`: the
identity on the diagonal summand, and on the other summand the inclusion of the puncture, which
the second projection twists by the Galois automorphism. All four readings are definitional.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
* [Stacks Project, Tag 02WS](https://stacks.math.columbia.edu/tag/02WS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The first projection of the twisted relation, read in the category of schemes: the identity
on the diagonal summand and the inclusion of the puncture on the other. -/
theorem relationFirst_left :
    (relationFirst k K).left = coprod.desc (𝟙 (cover K)) (puncturedCover K).ι := rfl

/-- The second projection of the twisted relation, read in the category of schemes: the identity
on the diagonal summand and the inclusion of the puncture followed by the Galois automorphism on
the other. -/
theorem relationSecond_left (σ : K ≃ₐ[k] K) :
    (relationSecond k K σ).left =
      coprod.desc (𝟙 (cover K)) ((puncturedCover K).ι ≫ galoisAction k K σ) := rfl

/-- The relation composed with the first projection of the self-product of the chart is the
first projection of the relation. -/
theorem twistedRelation_left_comp_prod_fst (σ : K ≃ₐ[k] K) :
    (twistedRelation k K σ).left ≫
        (prod.fst (X := coverOverBase k K) (Y := coverOverBase k K)).left =
      (relationFirst k K).left :=
  congrArg Over.Hom.left (twistedRelation_target k K σ)

/-- The relation composed with the second projection of the self-product of the chart is the
second projection of the relation. -/
theorem twistedRelation_left_comp_prod_snd (σ : K ≃ₐ[k] K) :
    (twistedRelation k K σ).left ≫
        (prod.snd (X := coverOverBase k K) (Y := coverOverBase k K)).left =
      (relationSecond k K σ).left :=
  congrArg Over.Hom.left (twistedRelation_source k K σ)

end AlgebraicGeometry.TwistedDoubledOrigin

end
