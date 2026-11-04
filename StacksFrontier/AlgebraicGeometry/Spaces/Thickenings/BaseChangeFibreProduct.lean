module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleCovering

/-!
# Base change of a thickening read at a chosen fibre product

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`, with inclusion
`i : G ⟶ X`, and let `φ : U ⟶ X` be a morphism. The restriction of the thickening to `U` is
the closed subspace `G ×_X U ⊂ U`, and there are two ways to name it: as the pointwise
inverse image `CategoryTheory.Subfunctor.preimage`, which is how
`AlgebraicGeometry.Space.isThickening_preimage` states the base change, and as the *range* of
the cartesian projection out of a chosen fibre product, which is how every consumer that goes
through `AlgebraicGeometry.Space.spacesBaseChange` meets it.

This file states the base change at the second reading: the range of the leg opposite `i` in
any cartesian square over `i` is a thickening of `U`.

## Main results

* `AlgebraicGeometry.Space.isThickening_range_of_isPullback`: the range of the cartesian
  projection of a thickening along an arbitrary morphism is a thickening.

## Implementation notes

The chosen fibre product in a cartesian square over `i` need not be the pointwise inverse
image on the nose — `AlgebraicGeometry.Space.spacesBaseChange` takes the fibre products of the
slice category — so neither reading is obtained from the other by `rfl`. They are nevertheless
equal as subfunctors: `CategoryTheory.Subfunctor.range_eq_preimage_of_isPullback` says that the
range of one leg of a cartesian square of presheaves is the inverse image of the range of the
opposite leg, the opposite leg here being the inclusion `i = G.ι`, whose range is `G` itself by
`CategoryTheory.Subfunctor.range_ι`. A cartesian square of algebraic spaces is cartesian as a
square of presheaves by `AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_hom`, so that
equality applies to the square supplied here and the statement reduces to
`AlgebraicGeometry.Space.isThickening_preimage`.

No hypothesis is placed on `φ`: a thickening restricts to a thickening along an arbitrary
morphism, which is what Stacks 09ZX asserts, and an étale `φ` — the case the spaces-étale site
of `X` supplies, through the `isPullback` field of
`AlgebraicGeometry.Space.spacesBaseChange` — is an instance.

## References

* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (1), the
  cartesian base-change functor on spaces-étale sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 09ZX, at a chosen fibre product.** Let `G ⊂ X` be a thickening of algebraic
spaces over `S` with inclusion `i : G ⟶ X`, let `φ : U ⟶ X` be any morphism, and let

    P --q--> U
    |        |
    p        φ
    v        v
    G --i--> X

be a cartesian square. Then the range of `q` is a thickening of `U`.

This is the reading of the base change of a thickening that a chosen fibre product supplies,
and in particular the one that the `isPullback` field of
`AlgebraicGeometry.Space.spacesBaseChange` supplies for an object of the spaces-étale site of
`X`. The range of `q` is the inverse image of `G` along `φ`, so this is
`AlgebraicGeometry.Space.isThickening_preimage` read through that identification; see the
implementation notes. -/
@[stacks 09ZX "base change of a thickening, at a chosen fibre product"]
theorem isThickening_range_of_isPullback {X U P : AlgebraicSpaces B S hS}
    {G : Subfunctor X.1} (hG : IsThickening B S hS X G) {φ : U ⟶ X} {q : P ⟶ U}
    {p : P ⟶ IsThickening.space B S hS hG}
    (sq : IsPullback q p φ (IsThickening.inclusion B S hS hG)) :
    IsThickening B S hS U (Subfunctor.range q.hom) := by
  have hrange : Subfunctor.range q.hom = G.preimage φ.hom :=
    (Subfunctor.range_eq_preimage_of_isPullback
        (AlgebraicSpaces.isPullback_hom B S hS sq)).trans
      (congrArg (fun T : Subfunctor X.1 => T.preimage φ.hom) (Subfunctor.range_ι G))
  exact hrange ▸ isThickening_preimage B S hS G φ hG

end AlgebraicGeometry.Space

end
