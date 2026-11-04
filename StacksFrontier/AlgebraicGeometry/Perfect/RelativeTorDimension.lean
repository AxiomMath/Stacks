module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimension
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedScalarRestriction

/-!
# Locally finite relative Tor dimension of a morphism of schemes

For a morphism of schemes `f : X ⟶ S`, condition (2) of Stacks 069C is that `𝒪_X`, viewed as a
sheaf of modules over `f^{-1}𝒪_S`, locally has finite Tor dimension on the inverse-image ringed
space `(X, f^{-1}𝒪_S)`. This file states that condition.

The two pieces it is assembled from are already in the library:
`AlgebraicGeometry.Scheme.Hom.derivedScalarRestriction` is restriction of scalars along
`f^{-1}𝒪_S ⟶ 𝒪_X` on derived categories, and
`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` is part (3) of Stacks 08CG.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.LocallyHasFiniteRelativeTorDimension` is condition (2) of
  Stacks 069C.

## Implementation notes

As everywhere in `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, the derived
tensor product is a parameter — here a family of certificates indexed by the opens of the
inverse-image ringed space, since part (3) of Stacks 08CG restricts to an open covering.

Stacks 069C, the equivalence of perfectness, this condition and finiteness of the Tor dimension
of every map of local rings, is `AlgebraicGeometry.perfect_tfae`, where this condition is read at
the canonical family of certificates
(`AlgebraicGeometry.Scheme.Hom.locallyHasFiniteRelativeTorDimension_canonical_iff`).

At an arbitrary family the condition can degenerate: at
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection`, by
`AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_firstProjection_iff`, it asks only that the
cohomology of the restricted object vanish outside some interval, which holds for every `f` with
the covering `{X}` and the interval `[0, 0]`.

What makes the condition say what Stacks 069C says is *pinning* the family by its underived
tensor product: requiring `(D U).tensor` to be the tensor product of sheaves of modules
`Stacks.SheafOfModules.Tensor.sheafTensor` of Stacks 06YM on each open subspace. That is all the
pinning the predicate admits, and it is enough.
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.hasTorAmplitudeIn_congr`,
`hasFiniteTorDimension_congr` and
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_congr` show that two families with
the same underived tensor products define the same predicate, since a total left derived functor
is unique up to canonical isomorphism. The pinning condition and the resulting well-definedness
of condition (2) are
`AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily` and
`AlgebraicGeometry.Scheme.Hom.locallyHasFiniteRelativeTorDimension_congr_of_isGenuine`, in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalks`.

The derived tensor product of Stacks 06YU *is* available in this development, on an arbitrary
ringed space: `Stacks.Cohomology.TorAmplitude.derTensor` is the canonical inhabitant of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` at the site of opens, built from
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, and the Tor-amplitude
vocabulary of Stacks 08CG is stated against it in
`StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace`.

A genuine family is exhibited, so the hypothesis of this definition is inhabited by the derived
tensor product it is meant to name and not only by a degenerate certificate.
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily` of
`StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionCanonicalCertificate` is the canonical
certificate on every open subspace at once: its `tensor` field is
`Stacks.SheafOfModules.Tensor.sheafTensor` on the nose, which is the pinning condition itself, its
`derivedTensor` field is `Stacks.Cohomology.TorAmplitude.derTensor`, and its
`CategoryTheory.Functor.IsLeftDerivedFunctor` field is
`Stacks.DerivedTensor.RingedSite.isLeftDerivedFunctor_sheafTensorComparison` — the two inputs that
turns on, the degree-zero collapse `Tot(K ⊗ ℱ[0]) ≅ K ⊗ ℱ` natural in the first variable
(`CochainComplex.KFlatBifunctor.totalSingleNatIso`) and the criterion that a comparison
invertible on K-flat complexes is the total left derived functor, are both proved there for
sheaves of modules on a ringed site. That the family is pinned is
`AlgebraicGeometry.Scheme.Hom.isGenuineRelativeTensorFamily_canonical` of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge`, and consequently the
universal and the existential quantification over pinned families agree, by
`AlgebraicGeometry.Scheme.Hom.forall_locallyHasFiniteRelativeTorDimension_iff_exists`.

## References

* [Stacks Project, Lemma 37.61.11 (Tag 069C)](https://stacks.math.columbia.edu/tag/069C)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
  [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
  [∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]

/-- **Condition (2) of Stacks 069C.** The structure sheaf `𝒪_X`, viewed as a sheaf of modules
over `f^{-1}𝒪_S` by restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X` and placed in degree zero,
locally has finite Tor dimension on the inverse-image ringed space `(X, f^{-1}𝒪_S)`.

The derived tensor product is the family of certificates `D`, one on each open subspace of the
inverse-image ringed space; at the canonical family this is
`Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension`, see
`AlgebraicGeometry.Scheme.Hom.locallyHasFiniteRelativeTorDimension_canonical_iff`. -/
public def LocallyHasFiniteRelativeTorDimension
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding)) :
    Prop :=
  RingedSpace.LocallyHasFiniteTorDimension
    (RingedSpace.inverseImage S.toRingedSpace f.base) D
    ((derivedScalarRestriction f).obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj
        (structureModule X.toRingedSpace)))

end AlgebraicGeometry.Scheme.Hom

end
