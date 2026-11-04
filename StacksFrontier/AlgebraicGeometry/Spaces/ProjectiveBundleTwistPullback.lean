module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback.QuotientReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback.PullbackMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback.TwistIso

/-!
# The twist `𝒪(1)` of the projective bundle of an inverse image

Let `g : X' ⟶ X` be a morphism of algebraic spaces over `S`, `ℰ` a finite locally free
quasi-coherent `𝒪_X`-module, `π : P = 𝐏(ℰ) ⟶ X` its projective bundle and
`π' : Q = 𝐏(g^*ℰ) ⟶ X'` the projective bundle of the inverse image.  By
`AlgebraicGeometry.Space.projectiveBundlePullbackIso`, `Q` is the base change `P ×_X X'`, so
there is a morphism `θ : Q ⟶ P` over `g`.  This file proves that **`θ` pulls the twist back to
the twist**: there is an isomorphism `θ^*𝒪_P(1) ≅ 𝒪_Q(1)` carrying the inverse image of the
tautological quotient `π^*ℰ ⟶ 𝒪_P(1)` to the tautological quotient `π'^*g^*ℰ ⟶ 𝒪_Q(1)`,
through the identification `π'^*g^*ℰ ≅ θ^*π^*ℰ` of iterated inverse images.

## Strategy

Both are quotients of the one module `π'^*g^*ℰ`, so by
`AlgebraicGeometry.Space.quotientIsoOfModulePullbackIsFlat` it suffices to compare them after the
inverse image along the étale surjective chart `a : 𝐏(g^*ℰ|_W) ⟶ Q`, for `W = U' ×_X U` the
chart of `X'` of `AlgebraicGeometry.Space.presentingFiberChart`.  The chart bundle
`𝐏(g^*ℰ|_W)` is a represented algebraic space, on which a quotient of quasi-coherent modules is
determined by its reading on the scheme (Stacks 03DX (2)).  The chart `a` factors through the
presenting chart bundle `𝐏(g^*ℰ|_{U'})` of `Q`, and `a ≫ θ` through the presenting chart bundle
`𝐏(ℰ|_U)` of `P`; on these the two tautological quotients read as the tautological quotients of
the chart bundles, and their inverse images to `𝐏(g^*ℰ|_W)` both read as the tautological
quotient of `𝐏(g^*ℰ|_W)`, by Stacks 01O3 along `W ⟶ U'` and along `W ⟶ U`.

The reading statements are `AlgebraicGeometry.Space.QuotientReadingHyp`; this file proves that it
is preserved by inverse images along a morphism of the site
(`AlgebraicGeometry.Space.quotientReadingHyp_modulePullback`), that it passes between a module
and its inverse image (`AlgebraicGeometry.Space.quotientReadingHyp_modulePullback_obj`), and that
two quotients with the same reading are isomorphic
(`AlgebraicGeometry.Space.exists_iso_comp_eq_of_quotientReadingHyp`).

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundlePullbackMap`: the morphism `θ : 𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`.
* `AlgebraicGeometry.Space.projectiveBundlePullbackModuleIso`: `π'^*g^*ℰ ≅ θ^*π^*ℰ`.
* `AlgebraicGeometry.Space.projectiveBundlePullbackTautological`: the quotient
  `π'^*g^*ℰ ⟶ θ^*𝒪_P(1)`.

## Main results

* `AlgebraicGeometry.Space.quotientReadingHyp_modulePullback`,
  `AlgebraicGeometry.Space.quotientReadingHyp_modulePullback_obj` and
  `AlgebraicGeometry.Space.exists_iso_comp_eq_of_quotientReadingHyp`: readings of quotients on
  represented algebraic spaces.
* `AlgebraicGeometry.Space.pullbackComparison_coherence_of_square`: the coherence of the
  comparisons of iterated inverse images around `θ ≫ π = π' ≫ g`.
* `AlgebraicGeometry.Space.presentingFiberChartAtlas_comp_projectiveBundlePullbackMap`,
  `AlgebraicGeometry.Space.isEtale_presentingFiberChartAtlas` and
  `AlgebraicGeometry.Space.surjective_pointsMap_presentingFiberChartAtlas`: the étale surjective
  chart `𝐏(g^*ℰ|_W) ⟶ 𝐏(g^*ℰ)` and its composite with `θ`.
* `AlgebraicGeometry.Space.exists_quotientReadingHyp_siteMap_projectiveBundleChartQuotient` and
  `exists_quotientReadingHyp_chartBundlePullbackSiteMap_projectiveBundleChartQuotient`: over a
  chart `V` of `X'` with morphisms to the presenting charts of `X'` and of `X`, the tautological
  quotients of `𝐏(g^*ℰ|_{U'})` and of `𝐏(ℰ|_U)` pull back to quotients reading as the
  tautological quotient of `𝐏(g^*ℰ|_V)` (Stacks 01O3).

## Implementation notes

Every hypothesis of a lemma instantiated here at the projective bundles is passed with all its
arguments explicit and in the spelling of the lemma's binders: a class-typed local hypothesis
would be picked up by instance search, and an argument left to unification may be filled by a
different but definitionally equal term, either of which makes the matching of the instantiated
statements unfold the inverse-image functors.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0ERT](https://stacks.math.columbia.edu/tag/0ERT)

## Parts

* `StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback.QuotientReading`: readings
  of quotients on represented algebraic spaces.
* `StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback.PullbackMap`: comparisons
  of iterated inverse images, the morphism `θ` and the chart over `W`.
* `StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistPullback.TwistIso`: the two
  tautological quotients over `W` and the isomorphism `θ^*𝒪_P(1) ≅ 𝒪_Q(1)`.
-/
