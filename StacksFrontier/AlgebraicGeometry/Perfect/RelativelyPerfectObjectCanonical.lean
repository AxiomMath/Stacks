module

public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalks
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject

/-!
# Relatively perfect objects, at the derived tensor product of Stacks 06YU

For a morphism of schemes `f : X ⟶ S` which is flat and locally of finite presentation, an object
`E` of `D(𝒪_X)` is *perfect relative to `S`* when it is pseudo-coherent and, viewed over
`f^{-1}𝒪_S`, locally has finite Tor dimension. This is Stacks 0DI0.

`AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` states the second clause against an arbitrary
family `D` of `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`s, one on each open
subspace of the inverse-image ringed space. The underived half of such a certificate is free
data, and at
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` the clause
degenerates to cohomological boundedness
(`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_firstProjectionFamily_iff`). This file states
Stacks 0DI0 at the genuine derived tensor product instead: the one of Stacks 06YU, obtained from
K-flat resolutions, which is `Stacks.Cohomology.TorAmplitude.derTensor` on each open subspace of
`(X, f^{-1}𝒪_S)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect` is relative perfectness, Stacks 0DI0, read
  at the derived tensor product of Stacks 06YU and with no parameter of its own.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_canonicalFamily_iff`: at the canonical family
  of certificates, the parameterised predicate is this one.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_iff_isRelativelyPerfect`: the same at any
  family pinned by `AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily`, so the
  parameterised predicate is a generalisation which recovers Stacks 0DI0 exactly on the pinned
  families.

## Implementation notes

The pseudo-coherence clause is unchanged: it carries no tensor product.

The Tor clause is `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension`, part (3) of
Stacks 08CG read against `Stacks.Cohomology.TorAmplitude.derTensor`. That derived tensor product
is the genuine one: `Stacks.DerivedTensor.RingedSite.isLeftDerivedFunctor_sheafTensorComparison`
exhibits it as the total left derived functor of `- ⊗_{f^{-1}𝒪_S} -`, the resolving class being
the K-flat complexes of Stacks 06YS.

Flatness and local finite presentation of `f` are the standing hypotheses of Stacks 0DI0. They
are carried as instance arguments and are not used by either clause, exactly as in
`AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo`.

The parameterised `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` is strictly more general, as
it is also readable at the degenerate family; it agrees with Stacks 0DI0 wherever its family is
pinned.

## References

* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Definition 20.47.1 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
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

/-- An object `E` of `D(𝒪_X)` is perfect relative to `S` when it is pseudo-coherent and, after
restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_X`, locally has finite Tor dimension on the
inverse-image ringed space `(X, f^{-1}𝒪_S)`.

Pseudo-coherence is part (3) of Stacks 08CB, and local finiteness of the Tor dimension is part (3)
of Stacks 08CG taken against the derived tensor product `- ⊗^{L}_{f^{-1}𝒪_S} -` of Stacks 06YU on
each open subspace, the total left derived functor of the tensor product of sheaves of modules. -/
@[stacks 0DI0]
public def IsRelativelyPerfect [Flat f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) : Prop :=
  RingedSpace.IsPseudoCoherent E ∧
    Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base)
      ((derivedScalarRestriction f).obj E)

/-- `E` is perfect relative to `S` if and only if it is pseudo-coherent and its restriction of
scalars to `f^{-1}𝒪_S` locally has finite Tor dimension. -/
public theorem isRelativelyPerfect_iff [Flat f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.IsRelativelyPerfect E ↔
      RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E ∧
        Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension
          (RingedSpace.inverseImage S.toRingedSpace f.base)
          ((derivedScalarRestriction f).obj E) :=
  Iff.rfl

/-- **At the canonical family of certificates the parameterised predicate is Stacks 0DI0.** The
canonical family is the derived tensor product of Stacks 06YU on each open subspace. -/
public theorem isPerfectRelativeTo_canonicalFamily_iff [Flat f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{d', u}
          (RingedSpace.inverseImage S.toRingedSpace f.base)) E ↔
      f.IsRelativelyPerfect E :=
  Iff.rfl

omit [HasDerivedCategory (OXMod X.toRingedSpace)]
  [HasDerivedCategory (OXMod (S.toRingedSpace.inverseImage f.base))] in
/-- **The canonical family is pinned.** Its underived half is the tensor product of sheaves of
modules of Stacks 06YM on every open subspace, on the nose. -/
public theorem isGenuineRelativeTensorFamily_canonicalFamily :
    IsGenuineRelativeTensorFamily f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{d', u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)) :=
  fun _ => rfl

/-- **At a pinned family the parameterised predicate is Stacks 0DI0.** For a family of
certificates whose underived tensor products are the tensor products of sheaves of modules on
every open subspace, `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` agrees with
`AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`. -/
public theorem isPerfectRelativeTo_iff_isRelativelyPerfect [Flat f]
    [LocallyOfFinitePresentation f]
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f.IsPerfectRelativeTo D E ↔ f.IsRelativelyPerfect E :=
  and_congr_right fun _ =>
    RingedSpace.locallyHasFiniteTorDimension_iff_of_tensor_eq _ D
      (fun U => (hD U).trans (isGenuineRelativeTensorFamily_canonicalFamily.{d', u} f U).symm) _

end AlgebraicGeometry.Scheme.Hom

end
