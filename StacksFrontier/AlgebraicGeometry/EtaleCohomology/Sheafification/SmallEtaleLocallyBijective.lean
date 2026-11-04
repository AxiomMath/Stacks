module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian

/-!
# Local bijectivity on the small étale site at every coefficient universe

A morphism of presheaves becomes an isomorphism after sheafification exactly when it is locally
injective and locally surjective. Mathlib registers that equivalence for the small étale site of
a scheme `X : Scheme.{u}` only for coefficient categories concrete over `Type u`, so it covers
`AddCommGrpCat.{u}` and not the universe `max (u + 1) v` in which this library computes étale
cohomology. This file supplies it there.

## Main results

* `AlgebraicGeometry.Scheme.wEqualsLocallyBijective_smallEtaleTopology`: abelian sheaves on the
  small étale site satisfy the local-bijectivity criterion for coefficients in
  `AddCommGrpCat.{max (u + 1) v}`, for every scheme and every `v`.

## Implementation notes

The mechanism is the one used for sheafification itself in
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`: the small étale site has objects in
`Type (u + 1)` and morphisms in `Type u`, so it is essentially small *in the coefficient
universe* `max (u + 1) v`, and `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`
transports along the equivalence with a small model at that universe. Taking the smallness
universe to be the coefficient universe rather than `u` is what makes the criterion available:
at `u` the small model is a `Type u`-category and Mathlib has no instance for coefficients
above it.

Together with `AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology` this removes both
coefficient-universe side conditions of the site-generic torsion-cohomology lemmas, so an
assertion proved for `AddCommGrpCat.{u}` can be restated for `AddCommGrpCat.{max (u + 1) v}`
without carrying extra hypotheses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme

/-- **The local-bijectivity criterion holds for abelian sheaves on the small étale site of a
scheme `X : Scheme.{u}` with coefficients in `AddCommGrpCat.{max (u + 1) v}`, for every `v`.**

The site is essentially small in the coefficient universe, and the criterion transports from a
small model there. Mathlib's instance for this site covers only `AddCommGrpCat.{u}`. -/
instance (priority := low) wEqualsLocallyBijective_smallEtaleTopology (X : Scheme.{u}) :
    X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
  have : ∀ T : (X.Etale)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow T (equivSmallModel.{max (u + 1) v} X.Etale).inverse.op)
      AddCommGrpCat.{max (u + 1) v} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{max (u + 1) v} _ _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
    max (u + 1) v, u + 1, max (u + 1) v + 1, max (u + 1) v} X.smallEtaleTopology

end AlgebraicGeometry.Scheme

end
