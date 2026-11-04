module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.OverSiteDisjointCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.SplitPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.LocallyQConstant

/-!
# Direct image of locally constant étale sheaves under finite étale morphisms

Let `f : X ⟶ Y` be a finite étale morphism of schemes. Direct image along `f` carries a locally
constant sheaf on `X_étale` to a locally constant sheaf on `Y_étale`, for sheaves of sets, of
abelian groups and of `R`-modules, and it preserves the accompanying finiteness condition in
each case: finiteness of the constant values for sets and abelian groups, and finite generation
of them for modules. This is Stacks 095B.

Direct image is precomposition with base change `Stacks.EtaleCohomology.smallEtaleBaseChange f`
between the small étale sites, which is the site functor underlying `f`.

## Main results

* `Stacks.ConstantSheaf.isLocallyConstant_finiteEtalePushforward` and
  `Stacks.ConstantSheaf.isFiniteLocallyConstant_finiteEtalePushforward` — sheaves of sets.
* `Stacks.ConstantSheaf.isLocallyConstant_finiteEtalePushforward_abelian` and
  `Stacks.ConstantSheaf.isFiniteLocallyConstant_finiteEtalePushforward_abelian` — sheaves of
  abelian groups.
* `Stacks.ConstantSheaf.isLocallyConstant_finiteEtalePushforward_modules` and
  `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_finiteEtalePushforward_modules` — sheaves
  of modules.

## Implementation notes

The source states the three coefficient cases with the finiteness condition in parentheses, so
it asserts six things; the six declarations keep them apart, and each conclusion is usable on
its own. The finiteness condition for module sheaves is
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant`, local constancy with finitely generated
constant values, which is the condition Tag 03RW calls finite type.

All six statements are instances of one argument, run for a predicate `Q` on the coefficient
category that is stable under finite products: trivial `Q` gives local constancy, finite
underlying type gives finite local constancy, and finite generation gives finite-type local
constancy. The argument has three ingredients. First, a sheaf takes a disjoint covering family
to the product of its values on the members, for an arbitrary coefficient category. Second, by
Tag 04HN the morphism is étale-locally a finite disjoint union of copies of the base, so over
such an object the restricted direct image is the finite product of the restrictions of the
sheaf along the sheets; a trivialization base-changes along any morphism of the site, which is
what makes this a statement about a sieve. Third, local `Q`-constancy of a sheaf is transported
between a localized site and the small étale site of the underlying scheme, where restricting
twice is restricting along a composite; in that formulation it is stable under restriction,
under finite products and local on the base.

## References

* [Stacks Project, Tag 095B](https://stacks.math.columbia.edu/tag/095B)

## Files

* `OverSiteDisjointCover`: the localized small étale site, disjoint covers, the initial object.
* `SplitPushforward`: splittings of finite étale morphisms and the split direct image.
* `LocallyQConstant`: local `Q`-constancy and the six main results.
-/
