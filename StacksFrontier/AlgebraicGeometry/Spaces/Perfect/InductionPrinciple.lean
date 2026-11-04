module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.OpenSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.SchemeCase
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.QcqsInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.OpenEnlargement
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.EnlargementInduction

/-!
# Induction on quasi-compact quasi-separated algebraic spaces

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` in a big
fppf site. A property of the objects of the spaces-étale site of `X` — of the algebraic
spaces étale over `X` — holds for every quasi-compact quasi-separated one as soon as it
holds for the affine ones and is inherited across an elementary distinguished square whose
étale member is affine. Reading the identity of `X` as an étale object gives the property
for `X` itself.

The property is carried by a presheaf together with its structure morphism to `X` rather
than by an object of the site, so that it can also be evaluated on an open subspace of such
an object and on the fibre product of a distinguished square, neither of which comes with a
preferred presentation as a site object. On site objects the two formulations agree.
Affineness of an étale object is `AlgebraicGeometry.Space.IsAffineSpace`: being isomorphic
to the presheaf represented by an object of the site with affine underlying scheme.

## Main results

* `AlgebraicGeometry.Space.qcqs_induction_on` is **Stacks 08GP**: the property holds for
  every quasi-compact quasi-separated object of the spaces-étale site of `X`.
* `AlgebraicGeometry.Space.qcqs_induction_on_self` is the particular case of the base space
  `X` with its identity morphism.
* `AlgebraicGeometry.Space.qcqs_induction_on_collection` is **Stacks 08GQ**: the same
  induction run inside a collection of objects of the spaces-étale site which consists of
  quasi-compact quasi-separated objects, is closed under quasi-compact open subspaces and
  contains the affine objects.

## Implementation notes

An arbitrary quasi-compact quasi-separated étale object is reduced to a finite descending
filtration by open subspaces, from the whole object down to the empty one, supplied by
`AlgebraicGeometry.Space.exists_finiteFiltration_of_isQuasiCompactSpace`. The stratum
between two consecutive terms is a reduced closed subspace which admits a quasi-compact
separated scheme as a surjective étale neighbourhood, isomorphic above the stratum; by
`AlgebraicGeometry.Space.IsElementaryDistinguishedSquare` that is exactly an elementary
distinguished square on the larger term with the smaller term as its open subspace. The
property therefore propagates from the empty open subspace at the top of the filtration
down to the object itself, the base case being the affine case applied to the empty scheme.

A square whose étale member is a scheme is treated by induction on the quasi-compact opens
of that scheme, `Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open`: an
affine open contributes an affine étale object, and the union of a quasi-compact open with
an affine open is realised as an elementary distinguished square whose fibre product is the
subfunctor cut out by their intersection. Enlarging an open subspace by one affine open at
a time, finitely many of them exhaust the scheme because it is quasi-compact, and the
hypothesis that it is quasi-separated is what keeps the intersections quasi-compact.

Every step is carried out for the auxiliary property of holding after precomposition with
an arbitrary isomorphism of presheaves. The fibre products and preimages produced by the
squares are determined only up to isomorphism, so the plain property is not directly
transportable along them, whereas this isomorphism-invariant strengthening is, and it
implies the plain property by taking the identity isomorphism.

A collection of étale objects is carried by the same data as the property, a presheaf
together with its structure morphism, and its closure under quasi-compact open subspaces is
phrased for an arbitrary open immersion with quasi-compact algebraic source. In that form it
applies to the fibre product of a distinguished square, which is a quasi-compact open
subspace of the affine étale member but is not presented as a subfunctor of it.

## Files

* `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.OpenSubobjects`
* `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.QuasiSeparated`
* `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.SchemeCase`
* `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.QcqsInduction`
* `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.OpenEnlargement`
* `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.EnlargementInduction`

## References

* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GQ](https://stacks.math.columbia.edu/tag/08GQ)
-/
