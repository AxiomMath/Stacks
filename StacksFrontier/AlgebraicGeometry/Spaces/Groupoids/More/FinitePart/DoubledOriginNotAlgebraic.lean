module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.DoubledOriginNotAlgebraic.PairsOnSchemes
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.DoubledOriginNotAlgebraic.NotAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.DoubledOriginNotAlgebraic.FourPoints

/-!
# The finite part of the doubled origin is not an algebraic space

Stacks 04QI is the remark that separatedness cannot be dropped from Stacks 04QH. Let `X` be
affine `n`-space over a field `k` with its origin doubled (`n = 1` in the source), `Y` affine
`n`-space and `f : X ⟶ Y` the coordinate morphism, read as a morphism of algebraic spaces over
`Spec k` in a big fppf site containing `Spec k`. The morphism `f` is locally of finite type, and:

* the finite part `(X/Y)_fin` has exactly four points over the origin, the subsets `∅`, `{0₁}`,
  `{0₂}`, `{0₁, 0₂}` of the fibre of `f` over the origin;
* only `∅`, `{0₁}`, `{0₂}` lift to an open subscheme of `U ×_Y X` finite over `U` for an étale
  `U ⟶ Y`;
* hence `(X/Y)_fin`, if it is an algebraic space, is not étale over `Y`;
* and in fact `(X/Y)_fin` is not an algebraic space.

All of this is proved here for the sheaf `(X/Y)_fin` of Stacks 04PC and 04PD,
`AlgebraicGeometry.Space.finiteOpenSubspacePresheaf`.

## Main definitions

* `AlgebraicGeometry.Space.doubledCoordHom`: the coordinate morphism, as a morphism of the big
  fppf site of `Spec k`; `AlgebraicGeometry.Space.doubledOriginFinitePart` is its finite part.
* `AlgebraicGeometry.Space.originPoints`: the points of the finite part over the origin, its
  sections over `Spec k` lying over the origin; `AlgebraicGeometry.Space.chartIndices` reads off
  the set of chart origins the open subspace of such a point contains.
* `AlgebraicGeometry.Space.wholeFiniteOpenSubspace`: for a morphism of the site whose base change
  along `b` is finite, the pair of Stacks 04PC at `b` whose open subspace is everything.

## Main results

* `AlgebraicGeometry.Space.doubledOrigin_finitePart`: **Stacks 04QI**, all claims of the remark.
* `AlgebraicGeometry.Space.exists_equiv_originPoints`, `AlgebraicGeometry.Space.card_originPoints`:
  the four points over the origin.
* `AlgebraicGeometry.Space.not_isEtale_baseMap_doubledOriginFinitePart`: if `(X/Y)_fin` is an
  algebraic space, its projection to `Y` is not étale.
* `AlgebraicGeometry.Space.not_isAlgebraicSpace_doubledOriginFinitePart`: `(X/Y)_fin` is not an
  algebraic space.
* `AlgebraicGeometry.Space.FiniteOpenSubspace.exists_eq_range`: the open subspace of a pair of
  Stacks 04PC for a morphism of the site is the range of an open subscheme of the pullback of the
  site, finite over an affine base; `FiniteOpenSubspace.exists_comp_ι_eq_iff_range_subset` says
  which morphisms of the site factor through it.

## Implementation notes

Everything rests on one scheme-theoretic fact,
`AlgebraicGeometry.exists_opens_forall_notMem_puncturedAffineSpace`: if an open subscheme of
`U ×_Y X` finite over `U` contains both chart sections at a point `u` over the origin, then a
whole neighbourhood of `u` lies over the origin. To apply it to a section of `(X/Y)_fin`, an
open subspace of the presheaf fibre product is turned into an open subscheme of the fibre product
of the site (`FiniteOpenSubspace.exists_eq_range`), and the fourth point `{0₁, 0₂}` is pulled
back along a surjective chart `φ : U ⟶ (X/Y)_fin`; over the pullback both chart sections lie in
the open subspace, so some point of `U` has a neighbourhood mapped to the origin
(`exists_opens_forall_notMem_of_surjective`).

Non-étaleness follows because an étale chart composed with an étale projection would be open.
That `(X/Y)_fin` is not an algebraic space, which the source leaves to the reader, follows from
the infinitesimal neighbourhoods `T_N = Spec k[t]/(t^(N+1))` of the origin: a coordinate is
nilpotent, say of order `N`, near the point of `U` found above, while the pullback of the pair
over `T_N` with whole open subspace is étale over `T_N` and passes through that neighbourhood, so
it would be a nonempty flat `k[t]/(t^(N+1))`-algebra killing `t ^ N`, which
`RingHom.Flat.subsingleton_of_map_pow_eq_zero` rules out.

Sections of the finite part over a scheme are handled through morphisms from representable
presheaves rather than elements, and morphisms of the site are read as morphisms of algebraic
spaces through `AlgebraicGeometry.schemeSpaceMap`; `schemeSpaceMap_hom_comp` and
`schemeSpaceMap_hom_id` are the functoriality this needs.

## References

* [Stacks Project, Tag 04QI](https://stacks.math.columbia.edu/tag/04QI)
* [Stacks Project, Tag 04QH](https://stacks.math.columbia.edu/tag/04QH)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
-/
