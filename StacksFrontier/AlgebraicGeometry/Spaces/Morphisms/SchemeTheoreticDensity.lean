module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity.OpenSubspaceCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity.Density
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity.ChartCriterion

/-!
# Scheme-theoretic density of an open subspace of an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`U ⊆ X` be an open subspace. The *scheme-theoretic closure* of `U` in `X` is the
scheme-theoretic image of Stacks 082X of its inclusion, and `U` is *scheme-theoretically dense
in `X`* when the scheme-theoretic closure of `U ×_X V` in `V` is all of `V` for every étale
morphism `V ⟶ X` of algebraic spaces over `S`. That is Stacks 0834, whose definition of
density is the first of the two equivalent conditions of Stacks 0833; the second tests a single
surjective étale scheme chart, and is proved equivalent to it below. It is *not* equivalent to
the scheme-theoretic closure of `U` itself being all of `X`.

Stacks 0836, the content of this file, characterises density by the injectivity of the
canonical homomorphism `𝒪_X ⟶ j_* 𝒪_U` of sheaves of commutative rings on the small étale
site of `X`, where `j : U ⟶ X` is the inclusion: that homomorphism is the structure map
`fSharp` of the morphism of small étale ringed topoi of Stacks 03G8,
`AlgebraicGeometry.Space.smallEtaleRingedToposHom`, and injectivity is its being a
monomorphism.

Both sides are tested on the étale scheme charts of `X`, and the proof consists of matching
the two chartwise descriptions.

For the structure map, `AlgebraicGeometry.Space.structureSharp` is injective over an étale
scheme chart `V` of `X` exactly when pullback of regular functions along the morphism of
schemes representing `U ×_X V` is injective. Indeed the sections of the direct image over `V`
are the limit of the sections of `𝒪_U` over the étale charts of `U` above `U ×_X V`
(`AlgebraicGeometry.Space.chartIsLimit`), and for a representable morphism — an open immersion
is one — that indexing category has the initial object
`AlgebraicGeometry.Space.chartBaseChangeArrow`, so the projection to it is injective and the
structure map read through it is literally that pullback of functions
(`AlgebraicGeometry.Space.chartProjection_structureMapApp`).

For density, the scheme-theoretic closure of `U ×_X V` in a chart `V` is all of `V` exactly
when the open immersion of schemes `j_V` representing `U ×_X V` is scheme-theoretically
dominant: a closed subspace of a representable presheaf is the range of a closed immersion of
schemes, and conversely the scheme-theoretic image of schemes is again an object of the site,
so the two minimality properties match up. Since the charts of `X` include every open
subscheme of every chart, dominance over all charts is the same as injectivity on global
sections over all charts, by Stacks 01RE,
`AlgebraicGeometry.isSchemeTheoreticallyDense_opensRange_iff_mono`.

Finally density, which quantifies over all étale morphisms from algebraic spaces, may be
tested on the scheme charts alone: an étale morphism from an algebraic space has a surjective
étale scheme chart, over which the closure is everything, and a subsheaf whose inverse image
along a surjective étale chart is everything is everything, the chart presenting its target as
a coequalizer (`AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale`).

## Main definitions

* `AlgebraicGeometry.Space.schemeTheoreticClosure` is **part (1) of Stacks 0834**: the
  scheme-theoretic closure of a subspace, namely the scheme-theoretic image of its inclusion.
* `AlgebraicGeometry.Space.IsSchemeTheoreticallyDense` is **part (2) of Stacks 0834**:
  scheme-theoretic density of an open subspace of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.isSchemeTheoreticallyDense_iff_exists_surjective_etale_chart` is
  **Stacks 0833**: an open subspace is scheme-theoretically dense exactly when, for one
  surjective étale scheme chart `V` of `X`, the scheme-theoretic closure of `U ×_X W` in `W` is
  all of `W` for every open subscheme `W` of `V`; that is, exactly when `U ×_X V` is a
  scheme-theoretically dense open subscheme of `V` in the sense of Stacks 01RB. The source
  states condition (2) as the bare equality of the scheme-theoretic closure of `U ×_X V` with
  `V`; read that way the lemma is false, and the docstring of the theorem records the
  counterexample, which is Stacks 01RC.
* `AlgebraicGeometry.Space.schemeTheoreticClosure_eq_top_of_isSurjective_isEtale` is the part
  of Stacks 0833 that does hold for the bare equality: if the scheme-theoretic closure of
  `U ×_X V` in `V` is all of `V` for one surjective étale scheme chart `V`, then the
  scheme-theoretic closure of `U` in `X` is all of `X`.
* `AlgebraicGeometry.Space.isSchemeTheoreticallyDense_iff_mono_fSharp` is **Stacks 0836**: an
  open subspace is scheme-theoretically dense exactly when the structure-sheaf map of its
  inclusion is injective.
* `AlgebraicGeometry.Space.isSchemeTheoreticallyDense_inf` is **Stacks 0837**: the intersection
  of two scheme-theoretically dense open subspaces is again a scheme-theoretically dense open
  subspace.
* `AlgebraicGeometry.Space.isSchemeTheoreticallyDense_preimage_of_isFlat`: the inverse image of
  a scheme-theoretically dense open subspace along a flat morphism of algebraic spaces locally
  of finite presentation is scheme-theoretically dense. This is Stacks 0832 transported to
  algebraic spaces by the chart criterion of Stacks 0833, and with the quasi-finiteness
  hypothesis of Stacks 0832 removed by Stacks 05IE.

## Implementation notes

`AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense` is the same notion for an open
subscheme of a scheme, Stacks 01RB; this file adds the notion for an open subspace of an
algebraic space, and the two are related through the charts by the proof of Stacks 0836. They
are not the same declaration because the subspace of an algebraic space is a subfunctor on the
big fppf site rather than an open of a topological space.

## Parts

* `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity.OpenSubspaceCharts`:
  open subspaces and their étale scheme charts.
* `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity.Density`:
  the definitions of Stacks 0834, and Stacks 0836 and 0837.
* `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity.ChartCriterion`:
  the chart criterion of Stacks 0833, and flat inverse images.

## References

* [Stacks Project, Tag 01RB](https://stacks.math.columbia.edu/tag/01RB)
* [Stacks Project, Tag 01RC](https://stacks.math.columbia.edu/tag/01RC)
* [Stacks Project, Tag 01RD](https://stacks.math.columbia.edu/tag/01RD)
* [Stacks Project, Tag 01RE](https://stacks.math.columbia.edu/tag/01RE)
* [Stacks Project, Tag 0832](https://stacks.math.columbia.edu/tag/0832)
* [Stacks Project, Tag 0833](https://stacks.math.columbia.edu/tag/0833)
* [Stacks Project, Tag 0834](https://stacks.math.columbia.edu/tag/0834)
* [Stacks Project, Tag 0836](https://stacks.math.columbia.edu/tag/0836)
* [Stacks Project, Tag 0837](https://stacks.math.columbia.edu/tag/0837)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 05IE](https://stacks.math.columbia.edu/tag/05IE)
-/
