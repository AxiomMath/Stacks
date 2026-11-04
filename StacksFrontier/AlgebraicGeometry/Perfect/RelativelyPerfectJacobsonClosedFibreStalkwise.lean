module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibre
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject

/-!
# Stacks 0DJZ with its Tor clause reduced to the stalks

Let `(R, I)` be a ring with an ideal contained in its Jacobson radical, write `S = Spec R` and
`S₀ = Spec (R/I)`, and let `f : X ⟶ S` be proper, flat and locally of finite presentation. Stacks
0DJZ says that a pseudo-coherent object `E` of `D(𝒪_X)` whose derived restriction to
`X₀ = S₀ ×_S X` is `S₀`-perfect is itself `S`-perfect.

`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibre` states that lemma with
its Tor clause carried as the named hypothesis
`AlgebraicGeometry.Scheme.Hom.LocallyFiniteTorDimensionFromClosedFibre`, whose conclusion is a
condition on a *sheaf* on the inverse-image ringed space `(X, f^{-1}𝒪_S)`, read at a family of
certificates for the derived tensor product. This module replaces that hypothesis by the
*stalkwise* one the source's proof actually produces: a single interval bounding the Tor amplitude
of every stalk. Nothing else about the lemma changes.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.UniformStalkTorAmplitudeFromClosedFibre`: **the residual of
  Stacks 0DJZ, at the stalks.** It mentions no derived tensor product on `X` and no open covering:
  it asks for two integers `a`, `b` such that the stalk at every point of `X` of `E`, read over
  `f^{-1}𝒪_S`, has Tor amplitude in `[a, b]` over the stalk ring.

## Main results

* `AlgebraicGeometry.Scheme.Hom.locallyFiniteTorDimensionFromClosedFibre_of_uniformStalkBound`:
  the stalkwise residual implies the sheaf-level one, for every family of certificates pinned to
  the genuine tensor product of sheaves of modules.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_closedFibre_of_uniformStalkBound`:
  **Stacks 0DJZ carrying the stalkwise residual.**

## What this reduces, and what is left

The source's proof of the Tor clause produces exactly a uniform interval: it takes a *finite*
affine open covering of `X`, each member closed in some `𝐀^{d_i}_S`, gets an interval
`[a_i - d_i, b_i]` per member from the fibrewise criterion of Stacks 0DJH, and the covering being
finite the intervals combine into one. So
`UniformStalkTorAmplitudeFromClosedFibre` is the shape the source's argument has, while
`LocallyFiniteTorDimensionFromClosedFibre` is the shape relative perfectness is stated in; the
passage between them is Stacks 09U9 and is what is proved here.

Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`,
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent`.

## Implementation notes

**Why the family of certificates is pinned here and is not in the sibling module.** The conclusion
of relative perfectness quantifies over a family of certificates for the derived tensor product,
whose `tensor` field is free; at the first-projection certificate
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` the condition
degenerates, so a statement proved for *every* family is strictly stronger than Stacks 0DJZ and
need not be true. The repository's own convention for this is
`AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily`, used the same way by condition (2) of
Stacks 069C in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RelativeTorDimensionClause`; and by
`AlgebraicGeometry.Scheme.Hom.locallyHasFiniteRelativeTorDimension_congr_of_isGenuine` every pinned
family gives the same condition, the canonical family being one
(`AlgebraicGeometry.Scheme.Hom.isGenuineRelativeTensorFamily_canonical`). So pinning is not a
weakening of the source: it is what "`E` is `S`-perfect" means.

The family `D₀` on the closed fibre is left unpinned, exactly as in the sibling module: it occurs
only in a hypothesis, where a weaker reading makes the statement stronger.

`UniformStalkTorAmplitudeFromClosedFibre` does not quantify over `D₀` internally, for the reason
the sibling module records: quantifying it there would ask for the bound at the degenerate family
too.

## References

* [Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 20.48.8 (09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 15.85.9 (0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
* [Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 36.10.2 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (I : Ideal R)

/-- The stalk ring of the inverse-image ringed space of `f` is commutative, at every point. -/
local instance commRing_stalk_inverseImage_spec (y : X) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base)).obj y)) :=
  RingedSpace.commRing_stalk_structureSheafOfRings _ _

/-- **The residual of Stacks 0DJZ, at the stalks.** Given a pseudo-coherent `E` whose derived
restriction to the closed fibre is `S₀`-perfect, and given that every point of `X` specializes
into the closed fibre, there is a *single* interval containing the Tor amplitude of the stalk at
every point of `X` of `E` read over `f^{-1}𝒪_S`.

This is the shape the source's proof of the Tor clause has: its interval comes from a finite
affine open covering, so it is uniform on the whole of `X`. The sheaf-level form
`AlgebraicGeometry.Scheme.Hom.LocallyFiniteTorDimensionFromClosedFibre` follows from it by
Stacks 09U9, which is
`locallyFiniteTorDimensionFromClosedFibre_of_uniformStalkBound` below. -/
public def UniformStalkTorAmplitudeFromClosedFibre [Flat f] [LocallyOfFinitePresentation f]
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding)) : Prop :=
  ∀ E : DerivedCategory (OXMod.{u, u} X.toRingedSpace),
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E →
      (closedFibreToBase f I).IsPerfectRelativeTo D₀
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (closedFibreToTotal f I).toLRSHom.toShHom).obj E) →
        (∀ x : X, ∃ x₀ : X, x ⤳ x₀ ∧ x₀ ∈ Set.range (closedFibreToTotal f I).base) →
          ∃ a b : ℤ, ∀ y : X,
            HasTorAmplitudeCanonical
              (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
                (structureSheafOfRings.{u}
                  (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace
                    f.base)).obj y))
              ((AlgebraicGeometry.SheafOfModules.stalkFunctor
                  (structureSheafOfRings.{u}
                    (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace
                      f.base)) y).mapDerivedCategory.obj
                ((derivedScalarRestriction f).obj E)) a b

/-- **The stalkwise residual of Stacks 0DJZ implies the sheaf-level one**, for every family of
certificates pinned to the genuine tensor product of sheaves of modules.

This is Stacks 09U9 for the Tor clause of relative perfectness, namely the theorem
`locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_bound` in the namespace
`AlgebraicGeometry.Scheme.Hom`, with the one-member covering by `X` itself. -/
public theorem locallyFiniteTorDimensionFromClosedFibre_of_uniformStalkBound
    [Flat f] [LocallyOfFinitePresentation f]
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).restrict
          U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (h : UniformStalkTorAmplitudeFromClosedFibre f I D₀) :
    LocallyFiniteTorDimensionFromClosedFibre f I D D₀ :=
  fun E hE hE₀ hspec =>
    locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_bound f D hD E
      (h E hE hE₀ hspec)

/-- **Stacks 0DJZ carrying the stalkwise residual.** Let `R` be a ring, let `I` be an ideal
contained in the Jacobson radical of `R`, let `f : X ⟶ Spec R` be proper, flat and locally of
finite presentation, and let `X₀ = Spec (R/I) ×_{Spec R} X`. If `E` is a pseudo-coherent object of
`D(𝒪_X)` whose derived restriction to `X₀` is `Spec (R/I)`-perfect, then `E` is `Spec R`-perfect.

This is `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre` with
its carried hypothesis replaced by the stalkwise one, which is the form the source's proof produces
and the form in which the fibrewise criterion of Stacks 0DJH can be fed into it. The family of
certificates on `Spec R` is pinned to the genuine tensor product of sheaves of modules; see the
implementation notes of this module for why that is what the source asserts.

Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`,
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent`. -/
public theorem isPerfectRelativeTo_of_closedFibre_of_uniformStalkBound [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] (hI : I ≤ (⊥ : Ideal R).jacobson)
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base).restrict
          U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (hTor : UniformStalkTorAmplitudeFromClosedFibre f I D₀)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE₀ : (closedFibreToBase f I).IsPerfectRelativeTo D₀
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (closedFibreToTotal f I).toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo D E :=
  isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre f I hI D D₀
    (locallyFiniteTorDimensionFromClosedFibre_of_uniformStalkBound f I D hD D₀ hTor) E hE hE₀

end AlgebraicGeometry.Scheme.Hom

end
