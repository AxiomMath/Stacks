module

public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism

/-!
# Transport of locally finite Tor dimension along an isomorphism of ringed spaces

Part (3) of Stacks 08CG — an object of `D(𝒪_X)` *locally has finite Tor dimension* — is a
condition on a ringed space, and it depends on that ringed space only up to isomorphism.  This
file proves that, on a quasi-compact space, and in both of the two spellings the development
carries: the pinned `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension`, read against
the derived tensor product of Stacks 06YU, and the certificate-carrying
`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` of Stacks 0DI0, read at the
canonical certificate family.

The object is transported by derived pullback along the isomorphism, which is the form a consumer
wants: if `e : X ≅ Y` is an isomorphism of ringed spaces and `E` is an object of `D(𝒪_Y)`, then
`Le^*E` locally has finite Tor dimension on `X` exactly when `E` does on `Y`.

Nothing monoidal is needed.  Tor amplitude in a fixed interval is *preserved* by derived pullback
along an arbitrary morphism of ringed spaces — that is Stacks 09U8, proved as
`Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback` — so applying it to `e`
and to `e⁻¹` and cancelling the two pullbacks with the composition and unit coherences of Tag
0D5S gives the equivalence for a fixed interval, hence for finite Tor dimension.  The passage
from finite Tor dimension to the *local* condition is where quasi-compactness enters: on a
quasi-compact ringed space the two coincide, by
`locallyHasFiniteTorDimension_iff_hasFiniteTorDimension` of
`AlgebraicGeometry.AffineRelativeTorAmplitude`.

## Main definitions

* `Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso`: the derived pullbacks along the
  two directions of an isomorphism of ringed spaces cancel.

## Main results

* `Stacks.Cohomology.TorAmplitude.hasFiniteTorDimension_derivedPullback_iso_iff`: the same for
  finite Tor dimension.
* `Stacks.Cohomology.TorAmplitude.compactSpace_of_iso`: an isomorphism of ringed spaces is a
  homeomorphism of the underlying spaces, so quasi-compactness passes along it.
* `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_derivedPullback_iso_iff`:
  **the transport**, for the pinned predicate, on a quasi-compact space.
* `AlgebraicGeometry.RingedSpace.compactSpace_inverseImage`: an inverse-image ringed space is
  quasi-compact when its space is, the space being unchanged.
* `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iso_iff`:
  the transport for the certificate-carrying predicate of Stacks 0DI0, at the canonical
  certificate family.

## Implementation notes

**Why quasi-compactness, and what it would take to remove it.**  Only the last two statements
need it; Tor amplitude in a fixed interval and finite Tor dimension transport with no hypothesis
at all.  The local condition quantifies over an open covering of the space, so transporting it
directly would need the order-isomorphism `Opens X ≃o Opens Y` induced by the homeomorphism
together with isomorphisms `X.restrict (e⁻¹U) ≅ Y.restrict U` of the restricted ringed spaces,
compatible with the two restriction functors — the analogue for an arbitrary isomorphism of
`AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso`, which this development has only
for an open subspace of an open subspace.  Nothing of that kind is carried here.  Quasi-compactness
collapses the local condition to the global one on both sides and is harmless for the intended
consumer, where both spaces are spectra of rings.

**What the intended consumer still owes.**  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentAffineEssentialSurjectivity.lean` record
that the affine case of the essential-surjectivity half of Stacks 0DI8 is restricted to a literal
system of `Spec`s because "nothing transports
`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` on an inverse-image ringed space
along an isomorphism of the base".  That transport is
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iso_iff`
below, and the quasi-compactness it asks for is available, by
`AlgebraicGeometry.RingedSpace.compactSpace_inverseImage`, as soon as the source of the structure
morphism is an affine scheme.  Two comparisons are still owed before the lift can be made: the
isomorphism of ringed spaces between `(X, f⁻¹𝒪_S)` and
`(Spec Γ(X), (Spec f^♯)⁻¹𝒪_{Spec Γ(S)})` induced by `AlgebraicGeometry.Scheme.isoSpec`, and the
identification of `(derivedScalarRestriction f).obj E` with the derived pullback along it of the
corresponding object on the `Spec` side.  Neither is constructed here.

**Why the stalkwise predicate is not used.**  The notes of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativelyPerfectFibres.lean` suggest routing the Tor
clause of Stacks 0DI0 through `AlgebraicGeometry.HasTorAmplitudeOver`, the stalkwise predicate of
Stacks 0C0V, for which transports along isomorphisms of schemes already exist.  That route is not
taken, and it is not available: the only identification of `HasTorAmplitudeOver` with a
`LocallyHasFiniteTorDimension` in this development is
`exists_hasTorAmplitudeOver_iff_locallyHasFiniteTorDimension` of
`AlgebraicGeometry.AffineRelativeTorAmplitude`,
whose morphism is `Spec` of a ring map on the nose and whose object is a literal sheafification of
a complex of modules; no statement for a general morphism exists in either direction.  The route
taken here avoids the question, because Stacks 09U8 is proved for the Stacks 08CG predicate
itself.

**No `@[stacks]` attribute.**  No tag of the Stacks project states these; they are the
invariance of part (3) of Stacks 08CG under isomorphism of the ringed space, assembled from Stacks
09U8 and Tag 0D5S.  Tag 09U8 is registered at
`Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback` and Tag 0D5S at
`Stacks.DerivedPullback.Composition.isIso_derivedPullbackCompComparisonCanonical`.

## References

* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 20.28.9 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Lemma 20.57.5 (Tag 09U8)](https://stacks.math.columbia.edu/tag/09U8)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.10.4 (Tag 0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Lemma 36.35.6 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

namespace Stacks.Cohomology.TorAmplitude

universe u

attribute [local instance] HasDerivedCategory.standard

section Transport

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (e : X ≅ Y)

/-- **The derived pullbacks along the two directions of an isomorphism of ringed spaces
cancel.**  `Le^* ⋙ L(e⁻¹)^* ≅ 𝟭`, by the composition coherence of Tag 0D5S at the factorisation
`e⁻¹ ≫ e = 𝟙` and the unit coherence `L(𝟙)^* ≅ 𝟭`. -/
def derivedPullbackHomCompInvIso :
    derivedPullback e.hom ⋙ derivedPullback e.inv ≅
      𝟭 (DerivedCategory (OXMod.{u} Y)) :=
  Stacks.DerivedPullback.factorIso e.inv e.hom (𝟙 Y) e.inv_hom_id ≪≫
    Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso Y

/-- **Finite Tor dimension transports along an isomorphism of ringed spaces.**  Finite Tor
dimension is Tor amplitude in some interval, and the interval is not changed by the transport. -/
theorem hasFiniteTorDimension_derivedPullback_iso_iff (E : DerivedCategory (OXMod.{u} Y)) :
    HasFiniteTorDimension X ((derivedPullback e.hom).obj E) ↔ HasFiniteTorDimension Y E :=
  exists_congr fun a => exists_congr fun b =>
    Stacks.Cohomology.TransportAlongIso.hasTorAmplitude_derivedPullback_iff e E a b

include e in
/-- **An isomorphism of ringed spaces is a homeomorphism of the underlying spaces**, so
quasi-compactness passes along it.  The forgetful functor to topological spaces carries the
isomorphism to an isomorphism of `TopCat`, hence to a homeomorphism. -/
theorem compactSpace_of_iso [CompactSpace X.carrier] : CompactSpace Y.carrier := by
  have h : CompactSpace ((AlgebraicGeometry.SheafedSpace.forget CommRingCat.{u}).obj X) :=
    inferInstanceAs (CompactSpace X.carrier)
  exact (TopCat.homeoOfIso
    ((AlgebraicGeometry.SheafedSpace.forget CommRingCat.{u}).mapIso e)).compactSpace

open AlgebraicGeometry.AffineRelativeTorAmplitude
  (locallyHasFiniteTorDimension_iff_hasFiniteTorDimension) in
/-- **Locally finite Tor dimension transports along an isomorphism of a quasi-compact ringed
space.**  For `e : X ≅ Y` with `X` quasi-compact and `E` in `D(𝒪_Y)`, the derived pullback `Le^*E`
locally has finite Tor dimension on `X` exactly when `E` does on `Y`.

On a quasi-compact ringed space the local condition is the global one, and the global one
transports with no hypothesis; `Y` is quasi-compact too, by
`Stacks.Cohomology.TorAmplitude.compactSpace_of_iso`.  This is the pinned predicate of Stacks
08CG (3); for the certificate-carrying predicate of Stacks 0DI0 see
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iso_iff`. -/
theorem locallyHasFiniteTorDimension_derivedPullback_iso_iff [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u} Y)) :
    LocallyHasFiniteTorDimension X ((derivedPullback e.hom).obj E) ↔
      LocallyHasFiniteTorDimension Y E := by
  have hY := compactSpace_of_iso e
  have hX := locallyHasFiniteTorDimension_iff_hasFiniteTorDimension
    (X := X) ((derivedPullback e.hom).obj E)
  have hYiff := locallyHasFiniteTorDimension_iff_hasFiniteTorDimension (X := Y) E
  exact hX.trans ((hasFiniteTorDimension_derivedPullback_iso_iff e E).trans hYiff.symm)

end Transport

end Stacks.Cohomology.TorAmplitude

namespace AlgebraicGeometry.RingedSpace

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The inverse-image ringed space has the same underlying topological space, so it is
quasi-compact as soon as that space is. -/
instance compactSpace_inverseImage (X : RingedSpace.{u, u}) {Z : TopCat.{u}}
    (i : Z ⟶ X.carrier) [CompactSpace Z] :
    CompactSpace (RingedSpace.inverseImage X i).carrier :=
  inferInstanceAs (CompactSpace Z)

/-- **The Tor-dimension clause of Stacks 0DI0 transports along an isomorphism of ringed spaces.**
At the canonical certificate family and on a quasi-compact space, locally finite Tor dimension of
`Le^*E` on `X` is locally finite Tor dimension of `E` on `Y`.

The certificate-carrying predicate is the pinned one at the canonical certificate family, by
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iff`, so this is
`Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_derivedPullback_iso_iff` read through
that identification.  It is the transport the implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentAffineEssentialSurjectivity.lean` report
missing; see the implementation notes above for what a consumer still owes. -/
theorem locallyHasFiniteTorDimension_canonicalCertificate_iso_iff
    {X Y : RingedSpace.{u, u}} (e : X ≅ Y) [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u, u} Y)) :
    LocallyHasFiniteTorDimension X (canonicalCertifiedDerivedSheafTensoringFamily X)
        ((derivedPullback e.hom).obj E) ↔
      LocallyHasFiniteTorDimension Y (canonicalCertifiedDerivedSheafTensoringFamily Y) E :=
  (locallyHasFiniteTorDimension_canonicalCertificate_iff X _).trans
    ((Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_derivedPullback_iso_iff e
        E).trans
      (locallyHasFiniteTorDimension_canonicalCertificate_iff Y E).symm)

end AlgebraicGeometry.RingedSpace

end
