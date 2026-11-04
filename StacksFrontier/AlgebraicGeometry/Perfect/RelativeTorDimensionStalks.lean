module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimension
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionCertificate
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.OnARingedSpace

/-!
# Condition (2) of Stacks 069C at the genuine derived tensor product

`AlgebraicGeometry.Scheme.Hom.LocallyHasFiniteRelativeTorDimension` states condition (2) of
Stacks 069C relative to a family of certificates
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, one on each open subspace of the
inverse-image ringed space `(X, f^{-1}𝒪_S)`. A certificate carries an underived tensor product as
a free field, so the family has to be *pinned* before the condition says what Stacks 069C says:
at `AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` the underived
operation is the first projection, which is exact, and the condition degenerates to cohomological
boundedness.

This file states the pinning — the underived tensor product of every member of the family is the
genuine `Stacks.SheafOfModules.Tensor.sheafTensor` — and proves that it determines condition (2)
completely: any two pinned families give the same condition, so the universal and the existential
quantification over pinned families agree.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily` is the pinning condition on a
  family of certificates.

## Main results

* `AlgebraicGeometry.Scheme.Hom.locallyHasFiniteRelativeTorDimension_congr_of_isGenuine`: two
  pinned families define the same condition (2).
* `AlgebraicGeometry.Scheme.Hom.forall_locallyHasFiniteRelativeTorDimension_of_exists`: a pinned
  family witnessing condition (2) makes every pinned family witness it.

## Implementation notes

The pinning is on the `tensor` field alone, and that is all the pinning the predicate admits:
by `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_congr` the derived halves of two
certificates with the same underived half are total left derived functors of one functor, hence
isomorphic, hence define the same vanishing. This is the ringed-space analogue of what the ring
level gets by construction: the `tensor` field of
`StacksDraft.TorAmplitude.CertifiedDerivedTensoring` *is* the derived bifunctor and its
`comparison` and `isLeftDerived` fields tie it to the genuine module tensor product, so a
universal quantification over ring-level certificates is already unambiguous, whereas at the
ringed-space level the underived operation is free and the pinning has to be imposed.

The two quantified forms agree only up to the existence of one pinned family, which is the
hypothesis of `forall_locallyHasFiniteRelativeTorDimension_of_exists`, and that hypothesis is
satisfied. Both halves of such a family are available — the underived one is
`Stacks.SheafOfModules.Tensor.sheafTensor` and the derived one is
`Stacks.Cohomology.TorAmplitude.derTensor`, the canonical derived tensor product of Stacks 06YU
on a ringed space — and the `CategoryTheory.Functor.IsLeftDerivedFunctor` field tying them
together is `Stacks.DerivedTensor.RingedSite.isLeftDerivedFunctor_sheafTensorComparison`. The
resulting family, on every open subspace at once, is
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`; that it is pinned
is `AlgebraicGeometry.Scheme.Hom.isGenuineRelativeTensorFamily_canonical`, and the converse
implication is therefore
`AlgebraicGeometry.Scheme.Hom.forall_locallyHasFiniteRelativeTorDimension_iff_exists`, both in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge`.

Stacks 069C, the equivalence of perfectness, condition (2) and finiteness of the Tor dimension
of every local ring, is `AlgebraicGeometry.perfect_tfae`.

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
  [∀ U : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    HasDerivedCategory.{d'}
      (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
        U.isOpenEmbedding))]

/-- A family of certificates on the open subspaces of the inverse-image ringed space
`(X, f^{-1}𝒪_S)` is **genuine** when the underived tensor product of each member is the tensor
product of sheaves of modules `- ⊗_{f^{-1}𝒪_S} -` of Stacks 06YM, that is the sheafification of
`V ↦ ℱ(V) ⊗_{f^{-1}𝒪_S(V)} 𝒢(V)`.

This is the pinning that `AlgebraicGeometry.Scheme.Hom.LocallyHasFiniteRelativeTorDimension`
needs in order to state condition (2) of Stacks 069C: the `tensor` field of a certificate is
free, and at the first-projection certificate the condition degenerates. -/
public def IsGenuineRelativeTensorFamily
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding)) :
    Prop :=
  ∀ U : TopologicalSpace.Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
    (D U).tensor = Stacks.SheafOfModules.Tensor.sheafTensor
      ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding).sheaf

/-- **Condition (2) of Stacks 069C is determined by the genuine tensor product.** Two genuine
families of certificates define the same condition.

Both families have the same underived tensor product on every open subspace, so
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_congr` applies: a total left derived
functor is unique up to canonical isomorphism, and vanishing of cohomology transports along the
isomorphism. -/
public theorem locallyHasFiniteRelativeTorDimension_congr_of_isGenuine
    (D₁ D₂ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (h₁ : IsGenuineRelativeTensorFamily f D₁) (h₂ : IsGenuineRelativeTensorFamily f D₂) :
    LocallyHasFiniteRelativeTorDimension f D₁ ↔ LocallyHasFiniteRelativeTorDimension f D₂ :=
  RingedSpace.locallyHasFiniteTorDimension_congr _ D₁ D₂
    (fun U => (h₁ U).trans (h₂ U).symm) _

/-- **The existential and the universal pinned readings of condition (2) agree.** If some genuine
family of certificates witnesses condition (2) of Stacks 069C, then every genuine family does.

This is the content of the pinning: the condition is a property of `f` alone, not of the choice
of derived tensor product, so the quantifier in front of the pinned family is immaterial. The
converse implication is `fun h D hD => h ⟨D, hD, _⟩` at a genuine family, for instance
`AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`. -/
public theorem forall_locallyHasFiniteRelativeTorDimension_of_exists
    (h : ∃ D : ∀ U : TopologicalSpace.Opens
          (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
          RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
            ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding),
        IsGenuineRelativeTensorFamily f D ∧ LocallyHasFiniteRelativeTorDimension f D) :
    ∀ D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
        RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
          ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding),
      IsGenuineRelativeTensorFamily f D → LocallyHasFiniteRelativeTorDimension f D := by
  obtain ⟨D₀, hD₀, hcond⟩ := h
  exact fun D hD =>
    (locallyHasFiniteRelativeTorDimension_congr_of_isGenuine f D₀ D hD₀ hD).1 hcond

end AlgebraicGeometry.Scheme.Hom

end
