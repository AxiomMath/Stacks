module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange

/-!
# The base-change map on small étale topoi of algebraic spaces (towards Stacks 0DG0)

Let
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
be a commuting square of algebraic spaces over `S`. Direct image is functorial, so the two
ways around the square give canonically isomorphic direct-image functors; that isomorphism is
`AlgebraicGeometry.Space.smallToposPushforwardBaseChange`, assembled from the composition
isomorphism of Stacks 03G2, part (3), in the two directions and the equality of the two
diagonals of the square.

Its *mate* under the two inverse-image/direct-image adjunctions of `g'` and `g` is the
canonical base-change map
`g⁻¹ f_* ⟶ f'_* (g')⁻¹`,
here `AlgebraicGeometry.Space.properBaseChangeMap`. Proper base change (Stacks 0DG0) is the
assertion that this map is an isomorphism when `f` is proper and the square is cartesian.

**That assertion is not proved here, and cannot be proved on this branch.** Stacks' own proof
of 0DG0 ("Proper base change", Stacks 0DFW) reduces it to proper base change *for schemes*
(Étale Cohomology, Stacks 0A3U) via Chow's lemma for algebraic spaces (Cohomology of Spaces,
Stacks 089J) and the descent exact sequence Stacks 0DFX; restricted to representable
`X`, `Y`, `Y'` the statement of 0DG0 *is* 0A3U, so no route avoids it. Neither Mathlib nor
this repository has 0A3U. What this file supplies is the construction half: the map itself,
in library vocabulary, characterized by the mate equation.

## Main definitions

* `AlgebraicGeometry.Space.smallToposPushforwardBaseChange`: the canonical isomorphism
  `(g')_* ⋙ f_* ≅ f'_* ⋙ g_*` attached to a commuting square of algebraic spaces.
* `AlgebraicGeometry.Space.properBaseChangeMap`: the canonical base-change map
  `f_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ f'_*` attached to a cartesian square, the mate of the former.

## Main results

* `AlgebraicGeometry.Space.mateEquiv_properBaseChangeMap`: the base-change map is pinned down
  by its mate being the direct-image comparison, so it can be used without unfolding.

## Implementation notes

The square is supplied as an `IsPullback`, rather than by choosing a fibre product, so that
the map is available for any realization of the base change. Only commutativity of the square
enters the direct-image comparison, which is therefore stated for a bare commuting square.

Component-level (`.app F`) forms of the unit and counit characterizations of the mate
(`CategoryTheory.unit_mateEquiv_symm`, `CategoryTheory.mateEquiv_counit_symm` specialized
here) exceed the kernel's deterministic budget at these sheaf categories, so they are omitted
rather than carried with a raised heartbeat count.

## References

* [Stacks Project, Tag 0DG0](https://stacks.math.columbia.edu/tag/0DG0)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- Direct image along the two paths of a commuting square `g' ≫ f = f' ≫ g` of algebraic
spaces agrees up to the canonical isomorphism built from the composition isomorphism of
Stacks 03G2, part (3), on both diagonals. -/
noncomputable def smallToposPushforwardBaseChange (w : g' ≫ f = f' ≫ g) :
    (smallToposMorphism B S hS g').pushforward ⋙
      (smallToposMorphism B S hS f).pushforward ≅
    (smallToposMorphism B S hS f').pushforward ⋙
      (smallToposMorphism B S hS g).pushforward :=
  smallToposMorphism_comp B S hS g' f ≪≫
    eqToIso (congrArg
      (fun h : X' ⟶ Y => (smallToposMorphism B S hS h).pushforward) w) ≪≫
    (smallToposMorphism_comp B S hS f' g).symm

/-- The canonical base-change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of a cartesian square of algebraic
spaces, obtained as the mate of `AlgebraicGeometry.Space.smallToposPushforwardBaseChange`
under the adjunctions of `g'` and of `g`. Proper base change, **Stacks 0DG0**, asserts that
it is an isomorphism when `f` is proper; that assertion is not proved here. -/
noncomputable def properBaseChangeMap (sq : IsPullback g' f' f g) :
    (smallToposMorphism B S hS f).pushforward ⋙
      (smallToposMorphism B S hS g).inverseImage ⟶
    (smallToposMorphism B S hS g').inverseImage ⋙
      (smallToposMorphism B S hS f').pushforward :=
  (mateEquiv (smallToposMorphism B S hS g').adj
      (smallToposMorphism B S hS g).adj).symm
    (smallToposPushforwardBaseChange B S hS f g f' g' sq.w).hom

/-- The base-change map is characterized by its mate: transposing it back across the two
adjunctions returns the direct-image comparison of the square. -/
theorem mateEquiv_properBaseChangeMap (sq : IsPullback g' f' f g) :
    mateEquiv (smallToposMorphism B S hS g').adj (smallToposMorphism B S hS g).adj
        (properBaseChangeMap B S hS f g f' g' sq) =
      (smallToposPushforwardBaseChange B S hS f g f' g' sq.w).hom :=
  (mateEquiv (smallToposMorphism B S hS g').adj
    (smallToposMorphism B S hS g).adj).apply_symm_apply _

end AlgebraicGeometry.Space

end
