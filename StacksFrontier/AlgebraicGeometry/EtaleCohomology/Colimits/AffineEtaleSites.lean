module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.CoveringsAndDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.StrictModels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.ColimitSite

/-!
# The affine étale site of a limit is the colimit of the affine étale sites

Let `I` be a directed set, let `(X_i, f_{i'i})` be an inverse system of schemes over `I` with
affine transition morphisms and let `X = lim X_i`. Stacks 0EYL says that
`X_{affine, étale} = colim (X_i)_{affine, étale}` as sites in the sense of Stacks 09YL.

## Main definitions

* `Stacks.EtaleCohomology.AffineEtaleSiteColimit` packages coherent geometric data: a strict
  inverse system of sites (Stacks 0A34) whose levels are identified, as sites, with the small
  affine étale sites of the `X_i` (Stacks 021B), together with functors to the small affine
  étale site of `X` given by base change along `X → X_i`.
* `Stacks.EtaleCohomology.affineEtaleSiteColimit` is the canonical such datum attached to a
  limit cone of an inverse system with affine transition morphisms.

## Main results

* `Stacks.EtaleCohomology.affineEtaleSiteColimit_level_cover` identifies the covering sieves of
  each level with those of the small affine étale site of the corresponding `X_i`.
* `Stacks.EtaleCohomology.affineEtaleSiteColimit_obj_descends`,
  `Stacks.EtaleCohomology.affineEtaleSiteColimit_hom_descends` and
  `Stacks.EtaleCohomology.affineEtaleSiteColimit_hom_eventually_eq` are the three clauses
  exhibiting the small affine étale site of `X` as the colimit of the underlying categories:
  every object comes from a stage, every morphism between objects from one stage comes from a
  further stage, and two morphisms with equal images agree at a further stage.
* `Stacks.EtaleCohomology.affineEtaleSiteColimit_mem_precoverage_iff` identifies the coverings
  of the small affine étale site of `X` with the images of the finite coverings of the stages.
* `Stacks.EtaleCohomology.affineEtaleSiteColimit_isColimitPrecoverage` is the conclusion "as
  sites in the sense of Stacks 09YL": the standard étale precoverage of the small affine étale
  site of `X` is exactly the colimit precoverage produced by Stacks 09YL from the system, and
  therefore satisfies the three site axioms of Stacks 00VH.

## Implementation notes

The scheme universe includes the universe of the directed index, as in Stacks 0EY1: a limit in a
smaller category of schemes need not remain a limit when the scheme universe is enlarged.

The colimit category is `AlgebraicGeometry.SmallAffineEtale B X hX` itself — the small affine
étale site of `X` of Stacks 021B, with no intervening model — because
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.exists_precoverage_of_colimit`,
the Lean form of Stacks 09YL, takes the colimit category at arbitrary universes. The *levels*
cannot be taken to be the sites of the `X_i` on the nose. A level of the system must be a
small category and the transition functors must be strictly functorial, `u (b ≫ a) = u a ⋙ u b`
and `u (𝟙 i) = 𝟭 _`, whereas `AlgebraicGeometry.SmallAffineEtale` is only locally small and
geometric base change is only pseudofunctorial: the fibre product of a fibre product is
canonically, not equally, the fibre product along the composite. The levels are therefore strict
small models, equivalent as sites to the small affine étale sites of the `X_i` (`levelEquiv`,
`affineEtaleSiteColimit_level_cover`); smallness is supplied by `CategoryTheory.AsSmall`. An
object of a model is an affine étale object over some `X_j` together with a chosen limit object
over `X`, and a transition changes only its stage map, so that the transition functors are
strictly functorial on the nose.

That the functors are geometric base change, and not merely functors between equivalent
categories, is recorded by the fibre-product squares `transition_isPullback` and
`toLimit_isPullback` together with the coherence laws `transitionFst_id`, `transitionFst_comp`
and `toLimitFst_transition` for the chosen projections.

`Stacks.EtaleCohomology.affineEtaleSiteColimit` carries `@[no_expose]`: the strict small models
it is assembled from are an implementation of the levels and not part of what Stacks 0EYL
asserts, so the construction is used only through the tagged lemmas below, which say everything
about it that the source does.

## Parts

* `BaseChange`: base change of affine étale objects and the structure `AffineEtaleSiteColimit`.
* `CoveringsAndDescent`: the coverings of the small affine étale site and étale descent.
* `StrictModels`: affine étale models over the limit and the strict small models of the levels.
* `ColimitSite`: the datum `affineEtaleSiteColimit` and the clauses of Stacks 0EYL.

## References

* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 09YL](https://stacks.math.columbia.edu/tag/09YL)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)

Tags covered: 0EYL.
-/
