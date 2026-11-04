module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectDegenerateCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreChartwise

/-!
# Stacks 0DJZ with the certificate on the closed fibre pinned

Let `(R, I)` be a ring with an ideal contained in its Jacobson radical, write `S = Spec R` and
`S₀ = Spec (R/I)`, let `f : X ⟶ S` be proper, flat and locally of finite presentation and put
`X₀ = S₀ ×_S X`. Stacks 0DJZ says that a pseudo-coherent object `E` of `D(𝒪_X)` whose derived
restriction to `X₀` is `S₀`-perfect is itself `S`-perfect.

The hypothesis of the lemma is that `E₀` is `S₀`-perfect, and `S₀`-perfectness is
`AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` at a family `D₀` of certified derived tensor
products on the open subspaces of `(X₀, f₀^{-1}𝒪_{S₀})`. The source means the genuine tensor
product of sheaves of modules there. A statement that leaves `D₀` free is therefore **not** the
source's: by `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_firstProjectionFamily_iff`, at
`AlgebraicGeometry.RingedSpace.firstProjectionFamily` the hypothesis says only that `E₀` is
pseudo-coherent with locally bounded cohomology, which carries no Tor-amplitude information;
and the conclusion of Stacks 0DJZ does not follow from that.

This module restates the residual of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreChartwise` with `D₀`
pinned by `AlgebraicGeometry.Scheme.Hom.IsGenuineRelativeTensorFamily`, and proves the lemma on
top of it. The family `D` on `S` is pinned the same way there and here.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.GenuineChartwiseStalkTorAmplitudeFromClosedFibre`: the chartwise
  residual of Stacks 0DJZ, demanded only of families of certificates on the closed fibre that are
  pinned to the genuine tensor product of sheaves of modules.

## Main results

* `AlgebraicGeometry.Scheme.Hom.genuineChartwiseStalkTorAmplitudeFromClosedFibre_of_forall`: the
  unpinned residual, if it held at every family, would give the pinned one — so the pinned
  residual is the weaker demand.
* `AlgebraicGeometry.Scheme.Hom.chartwiseStalkTorAmplitudeFromClosedFibre_of_genuine`: at a pinned
  family the pinned residual gives the unpinned predicate, which is how the existing chain is
  entered.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_closedFibre_of_genuineStalkBound`:
  **Stacks 0DJZ carrying the pinned chartwise residual.**
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_canonical_of_closedFibre_of_genuineStalkBound`:
  the same at the canonical families on both sides, where both pinnings are discharged by
  `AlgebraicGeometry.Scheme.Hom.isGenuineRelativeTensorFamily_canonical`. Nothing but the residual
  is assumed, which is also the certificate that the two pinnings are satisfiable.

## The lemma itself

Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`.
The pointwise bound its proof produces is
`AlgebraicGeometry.Scheme.Hom.exists_uniform_derivedStalk_bound_of_closedFibre`.

## References

* [Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
* [Stacks Project, Definition 36.35.1 (0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 15.85.9 (0DJH)](https://stacks.math.columbia.edu/tag/0DJH)
* [Stacks Project, Lemma 20.48.8 (09U9)](https://stacks.math.columbia.edu/tag/09U9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (I : Ideal R)

/-- **The chartwise residual of Stacks 0DJZ, demanded only at a pinned family of certificates on
the closed fibre.** For every family `D₀` whose underived tensor product on each open subspace of
`(X₀, f₀^{-1}𝒪_{S₀})` is the tensor product of sheaves of modules, and every pseudo-coherent `E`
whose derived restriction to the closed fibre is `S₀`-perfect for that family, and given that
every point of `X` specializes into the closed fibre: there is an open covering of `X` and, on
each member, a single interval containing the Tor amplitude of the stalk at every point of that
member of `E` read over `f^{-1}𝒪_S`.

`AlgebraicGeometry.Scheme.Hom.ChartwiseStalkTorAmplitudeFromClosedFibre` is the same demand with
`D₀` left free. That is a strictly larger demand, and not the source's: at
`AlgebraicGeometry.RingedSpace.firstProjectionFamily` its hypothesis degenerates to
pseudo-coherence and local boundedness of the cohomology, by
`isPerfectRelativeTo_firstProjectionFamily_iff`. -/
public def GenuineChartwiseStalkTorAmplitudeFromClosedFibre [Flat f]
    [LocallyOfFinitePresentation f] : Prop :=
  ∀ D₀ : ∀ U : TopologicalSpace.Opens
      (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
        (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding),
    IsGenuineRelativeTensorFamily (closedFibreToBase f I) D₀ →
      ChartwiseStalkTorAmplitudeFromClosedFibre f I D₀

/-- **The pinned residual is the weaker demand.** If the unpinned chartwise residual held at every
family of certificates on the closed fibre, it would in particular hold at the pinned ones.

This is the measurement that nothing is lost by proving only the pinned form, and it is the
analogue for the pinning of
`chartwiseStalkTorAmplitudeFromClosedFibre_of_uniform` for the covering. -/
public theorem genuineChartwiseStalkTorAmplitudeFromClosedFibre_of_forall [Flat f]
    [LocallyOfFinitePresentation f]
    (h : ∀ D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
        RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
          ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
            (closedFibreToBase f I).base).restrict U.isOpenEmbedding),
      ChartwiseStalkTorAmplitudeFromClosedFibre f I D₀) :
    GenuineChartwiseStalkTorAmplitudeFromClosedFibre f I :=
  fun D₀ _ => h D₀

/-- **The pinned residual, read at one pinned family.** The definition applied to a family and its
pinning, so that the chain of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonClosedFibreChartwise` can be
entered from the pinned residual. -/
public theorem chartwiseStalkTorAmplitudeFromClosedFibre_of_genuine [Flat f]
    [LocallyOfFinitePresentation f]
    (D₀ : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base).restrict U.isOpenEmbedding))
    (hD₀ : IsGenuineRelativeTensorFamily (closedFibreToBase f I) D₀)
    (h : GenuineChartwiseStalkTorAmplitudeFromClosedFibre f I) :
    ChartwiseStalkTorAmplitudeFromClosedFibre f I D₀ :=
  h D₀ hD₀

/-- **Stacks 0DJZ carrying the pinned chartwise residual.** Let `R` be a ring, let `I` be an ideal
contained in the Jacobson radical of `R`, let `f : X ⟶ Spec R` be proper, flat and locally of
finite presentation, and let `X₀ = Spec (R/I) ×_{Spec R} X`. If `E` is a pseudo-coherent object of
`D(𝒪_X)` whose derived restriction to `X₀` is `Spec (R/I)`-perfect, then `E` is `Spec R`-perfect.

Both families of certificates are pinned to the genuine tensor product of sheaves of modules, the
one on `Spec R` as in `isPerfectRelativeTo_of_closedFibre_of_chartwiseStalkBound` and the one on
the closed fibre in addition.

Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`,
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent`. -/
public theorem isPerfectRelativeTo_of_closedFibre_of_genuineStalkBound [IsProper f] [Flat f]
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
    (hD₀ : IsGenuineRelativeTensorFamily (closedFibreToBase f I) D₀)
    (hTor : GenuineChartwiseStalkTorAmplitudeFromClosedFibre f I)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE₀ : (closedFibreToBase f I).IsPerfectRelativeTo D₀
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (closedFibreToTotal f I).toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo D E :=
  isPerfectRelativeTo_of_closedFibre_of_chartwiseStalkBound f I hI D hD D₀
    (chartwiseStalkTorAmplitudeFromClosedFibre_of_genuine f I D₀ hD₀ hTor) E hE hE₀

/-- **Stacks 0DJZ at the canonical derived tensor product on both sides.** The previous statement
with both families of certificates taken to be the canonical ones, whose pinnings are discharged
by `isGenuineRelativeTensorFamily_canonical`. Nothing is assumed beyond the residual `hTor`, and
the two instances of that pinning are also the certificate that the hypotheses of the previous
statement are satisfiable.

Stacks 0DJZ with no hypothesis beyond the source's is
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_of_isPerfectRelativeTo_closedFibre_of_genuine`,
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent`. -/
public theorem isPerfectRelativeTo_canonical_of_closedFibre_of_genuineStalkBound [IsProper f]
    [Flat f] [LocallyOfFinitePresentation f] (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hTor : GenuineChartwiseStalkTorAmplitudeFromClosedFibre f I)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hE₀ : (closedFibreToBase f I).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of (R ⧸ I))).toRingedSpace
          (closedFibreToBase f I).base))
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (closedFibreToTotal f I).toLRSHom.toShHom).obj E)) :
    f.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage (Spec (CommRingCat.of R)).toRingedSpace f.base)) E :=
  isPerfectRelativeTo_of_closedFibre_of_genuineStalkBound f I hI _
    (isGenuineRelativeTensorFamily_canonical f) _
    (isGenuineRelativeTensorFamily_canonical (closedFibreToBase f I)) hTor E hE hE₀

end AlgebraicGeometry.Scheme.Hom

end
