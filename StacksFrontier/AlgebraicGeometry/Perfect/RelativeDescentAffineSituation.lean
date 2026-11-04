module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimensionBaseTransport
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.Comp

/-!
# Relative perfectness across an isomorphism of a morphism of schemes

Relative perfectness of Stacks 0DI0 is a condition on a morphism `f : X ⟶ S` and an object of
`D(𝒪_X)`. Its second clause reads finite Tor dimension on the inverse-image ringed space
`(X, f^{-1}𝒪_S)`, so it is not visibly invariant under replacing `f` by an isomorphic morphism.
This file compares the inverse-image ringed spaces over two isomorphic bases, and transports
relative perfectness along an isomorphism of morphisms of schemes, granted a matching of derived
restriction of scalars with derived pullback.

The comparison is the isomorphism of ringed spaces
`(Z, i^{-1}𝒪_S) ≅ (Z', i'^{-1}𝒪_{S'})` attached to an isomorphism `β : S ≅ S'` of ringed spaces
and a homeomorphism `h : Z ≅ Z'` over it. At `β = S.isoSpec`, `h = X.isoSpec` and `i = f.base` it
is the isomorphism `(X, f^{-1}𝒪_S) ≅ (Spec Γ(X), (Spec f^{♯})^{-1}𝒪_{Spec Γ(S)})`. Its
construction needs nothing about schemes: pullback of sheaves along the inverse of a
homeomorphism is pushforward along it, the structure sheaf of `S` is the pullback of that of `S'`
because the structure-sheaf datum of an isomorphism of ringed spaces is itself an isomorphism,
and the composition coherence of Stacks 008I splices the two.

The identification of `(derivedScalarRestriction f).obj (Lα^*E)` with the derived pullback along
that isomorphism of `(derivedScalarRestriction f').obj E` is a hypothesis of
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_derivedPullback_iso_iff`. Given it, the
pseudo-coherence clause transports with no hypothesis at all, and the Tor-dimension clause
transports by
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iso_iff`.

## Main definitions

* `AlgebraicGeometry.Scheme.forgetToRingedSpace`: a scheme, and a morphism of schemes, read as a
  ringed space and a morphism of ringed spaces.
* `AlgebraicGeometry.RingedSpace.baseHomeo`: the underlying homeomorphism of an isomorphism of
  ringed spaces.
* `AlgebraicGeometry.RingedSpace.sheafPushforwardEquivOfIso` and
  `AlgebraicGeometry.RingedSpace.sheafPullbackInvIsoPushforward`: pushforward of sheaves of
  commutative rings along a homeomorphism is an equivalence, and pullback along the inverse
  homeomorphism is that pushforward.
* `AlgebraicGeometry.RingedSpace.structureSheafIsoPullback`: the structure sheaf of `S` is the
  inverse image of the structure sheaf of `S'` along the base homeomorphism of `β : S ≅ S'`.
* `AlgebraicGeometry.RingedSpace.inverseImageIsoOfBaseIso`: the isomorphism of inverse-image
  ringed spaces over an isomorphism of the base.
* `AlgebraicGeometry.Scheme.Hom.inverseImageIsoSpec`: that comparison at
  `AlgebraicGeometry.Scheme.isoSpec`.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedPullback_iso_iff`: pseudo-coherence
  transports along an isomorphism of ringed spaces, in both directions and with no hypothesis.
* `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_of_iso`: at
  the canonical certificate family, locally finite Tor dimension depends only on the isomorphism
  class of the object.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_derivedPullback_iso_iff`: relative
  perfectness of Stacks 0DI0 transports along an isomorphism of a morphism of schemes, granted
  the matching of derived restriction of scalars with derived pullback.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_isoSpec_iff`: the same at
  `AlgebraicGeometry.Scheme.isoSpec`, where the isomorphism of inverse-image ringed spaces is
  `AlgebraicGeometry.Scheme.Hom.inverseImageIsoSpec` and the matching is the only hypothesis.

## Implementation notes

**The affineness hypothesis carried.** Quasi-compactness of the source, as
`CompactSpace X.carrier`, in `isPerfectRelativeTo_derivedPullback_iso_iff`, and affineness of
both schemes in `isPerfectRelativeTo_isoSpec_iff`, where it is what makes
`AlgebraicGeometry.Scheme.isoSpec` exist. Quasi-compactness is inherited by the inverse-image
ringed space, whose space is unchanged, through
`AlgebraicGeometry.RingedSpace.compactSpace_inverseImage`, and it is what
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iso_iff` asks
for: the local condition quantifies over an open covering. The comparisons of this file need
neither hypothesis; `inverseImageIsoOfBaseIso` is stated for arbitrary ringed spaces and an
arbitrary continuous map.

**Universes and the derived-category model.** Everything is at
`CategoryTheory.HasDerivedCategory.standard`, installed with priority `10000` as the import
closure requires, and at `AlgebraicGeometry.RingedSpace.{u, u}`, the only universe pattern at
which `Stacks.Cohomology.TorAmplitude.HasTorAmplitude` and the two spellings of the category of
`𝒪_X`-modules can both be stated.

## References

* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Lemma 36.35.6 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Lemma 36.10.4 (Tag 0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 20.46.13 (Tag 09U7)](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Lemma 20.57.5 (Tag 09U8)](https://stacks.math.columbia.edu/tag/09U8)
* [Stacks Project, Tag 008I](https://stacks.math.columbia.edu/tag/008I)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme read as a ringed space, and a morphism of schemes as a morphism of ringed spaces.
This is the composite of the two forgetful functors, and it agrees on objects with
`AlgebraicGeometry.Scheme.toRingedSpace` and on morphisms with `f.toLRSHom.toShHom`, both by
`rfl`; it is introduced only so that an isomorphism of schemes can be carried to an isomorphism
of ringed spaces. -/
abbrev forgetToRingedSpace : Scheme.{u} ⥤ RingedSpace.{u, u} :=
  Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.RingedSpace

/-! ### Pullback of sheaves of rings along a homeomorphism -/

/-- **Pushforward of sheaves of commutative rings along a homeomorphism is an equivalence**, with
inverse the pushforward along the inverse homeomorphism. The two unit isomorphisms are the
composition coherence of Stacks 008I at `h ≫ h⁻¹` and at `h⁻¹ ≫ h`, together with the fact that
pushforward along an identity is the identity functor, which holds definitionally. -/
def sheafPushforwardEquivOfIso {Z Z' : TopCat.{u}} (h : Z ≅ Z') :
    TopCat.Sheaf CommRingCat.{u} Z ≌ TopCat.Sheaf CommRingCat.{u} Z' :=
  CategoryTheory.Equivalence.mk (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom)
    (TopCat.Sheaf.pushforward CommRingCat.{u} h.inv)
    (by
      refine ?_ ≪≫ sheafPushforwardCompIso h.hom h.inv CommRingCat.{u}
      rw [h.hom_inv_id]
      exact Iso.refl _)
    (by
      refine (sheafPushforwardCompIso h.inv h.hom CommRingCat.{u}).symm ≪≫ ?_
      rw [h.inv_hom_id]
      exact Iso.refl _)

/-- **Pullback of sheaves of commutative rings along the inverse of a homeomorphism is
pushforward along the homeomorphism.** Both are left adjoint to pushforward along the inverse,
the second by `AlgebraicGeometry.RingedSpace.sheafPushforwardEquivOfIso`, so they agree by
uniqueness of left adjoints. -/
def sheafPullbackInvIsoPushforward {Z Z' : TopCat.{u}} (h : Z ≅ Z') :
    TopCat.Sheaf.pullback CommRingCat.{u} h.inv ≅
      TopCat.Sheaf.pushforward CommRingCat.{u} h.hom :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} h.inv).leftAdjointUniq
    (sheafPushforwardEquivOfIso h).toAdjunction

/-! ### The inverse-image ringed space over an isomorphic base -/

/-- The underlying homeomorphism of an isomorphism of ringed spaces: the image of the
isomorphism under the forgetful functor to topological spaces. -/
abbrev baseHomeo {S S' : RingedSpace.{u, u}} (β : S ≅ S') : S.carrier ≅ S'.carrier :=
  (AlgebraicGeometry.SheafedSpace.forget CommRingCat.{u}).mapIso β

/-- **The structure sheaf of `S` is the inverse image of the structure sheaf of `S'`** along the
base homeomorphism of an isomorphism `β : S ≅ S'` of ringed spaces.

The structure-sheaf datum of the isomorphism `β⁻¹` is an isomorphism of presheaves of rings, by
`AlgebraicGeometry.PresheafedSpace.sheafIsoOfIso`; that identifies `𝒪_S` with the pushforward of
`𝒪_{S'}` along the inverse homeomorphism, which is the pullback along the homeomorphism by
`AlgebraicGeometry.RingedSpace.sheafPullbackInvIsoPushforward`. -/
def structureSheafIsoPullback {S S' : RingedSpace.{u, u}} (β : S ≅ S') :
    S.sheaf ≅ (TopCat.Sheaf.pullback CommRingCat.{u} (baseHomeo β).hom).obj S'.sheaf := by
  refine ?_ ≪≫ ((sheafPullbackInvIsoPushforward (baseHomeo β).symm).app S'.sheaf).symm
  refine (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology S.carrier)
    CommRingCat.{u}).preimageIso ?_
  exact PresheafedSpace.sheafIsoOfIso (SheafedSpace.forgetToPresheafedSpace.mapIso β.symm)

/-- **The inverse-image ringed spaces of two isomorphic bases agree.** Let `β : S ≅ S'` be an
isomorphism of ringed spaces, let `h : Z ≅ Z'` be a homeomorphism, and let `i : Z ⟶ S` and
`i' : Z' ⟶ S'` be continuous maps with `i ≫ β = h ≫ i'`. Then `(Z, i^{-1}𝒪_S)` and
`(Z', i'^{-1}𝒪_{S'})` are isomorphic ringed spaces, over `h`.

The structure-sheaf datum is assembled from the composition coherence of Stacks 008I: pushing
`i^{-1}𝒪_S` forward along `h` is pulling it back along `h⁻¹`, hence is
`(h^{-1} ≫ i)^{-1}𝒪_S`, which by
`AlgebraicGeometry.RingedSpace.structureSheafIsoPullback` is
`((h^{-1} ≫ i) ≫ β)^{-1}𝒪_{S'}`, and the hypothesis says that base morphism is `i'`. -/
def inverseImageIsoOfBaseIso {S S' : RingedSpace.{u, u}} (β : S ≅ S') {Z Z' : TopCat.{u}}
    (h : Z ≅ Z') (i : Z ⟶ S.carrier) (i' : Z' ⟶ S'.carrier)
    (w : i ≫ (baseHomeo β).hom = h.hom ≫ i') :
    inverseImage S i ≅ inverseImage S' i' := by
  have hw : (h.inv ≫ i) ≫ (baseHomeo β).hom = i' := by
    rw [Category.assoc, w, ← Category.assoc, h.inv_hom_id, Category.id_comp]
  have A : (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} i).obj S.sheaf) ≅
      (TopCat.Sheaf.pullback CommRingCat.{u} i').obj S'.sheaf :=
    ((sheafPullbackInvIsoPushforward h).app _).symm ≪≫
      ((sheafPullbackCompIso h.inv i CommRingCat.{u}).app S.sheaf).symm ≪≫
      (TopCat.Sheaf.pullback CommRingCat.{u} (h.inv ≫ i)).mapIso (structureSheafIsoPullback β) ≪≫
      ((sheafPullbackCompIso (h.inv ≫ i) (baseHomeo β).hom CommRingCat.{u}).app S'.sheaf).symm ≪≫
      eqToIso (congrArg (fun k => (TopCat.Sheaf.pullback CommRingCat.{u} k).obj S'.sheaf) hw)
  exact SheafedSpace.forgetToPresheafedSpace.preimageIso
    (PresheafedSpace.isoOfComponents h ((TopCat.Sheaf.forget CommRingCat.{u} Z').mapIso A))

/-! ### The two clauses of Stacks 0DI0 across an isomorphism -/

/-- **Pseudo-coherence transports along an isomorphism of ringed spaces**, in both directions and
with no hypothesis on the spaces. One direction is the unbounded form of Stacks 09U7 at `e`; the
other is that form at `e⁻¹` followed by cancelling the two derived pullbacks with
`Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso`, pseudo-coherence being invariant
under isomorphism in the derived category. -/
theorem isPseudoCoherent_derivedPullback_iso_iff {X Y : RingedSpace.{u, u}} (e : X ≅ Y)
    (E : DerivedCategory (OXMod.{u, u} Y)) :
    IsPseudoCoherent (X := X) ((derivedPullback e.hom).obj E) ↔ IsPseudoCoherent (X := Y) E := by
  refine ⟨fun h => ?_, fun h =>
    KFlatDerivedPullback.isPseudoCoherent_derivedPullback e.hom E h⟩
  exact (KFlatDerivedPullback.isPseudoCoherent_derivedPullback e.inv _ h).of_iso
    ((Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso e).app E)

/-- **At the canonical certificate family, locally finite Tor dimension depends only on the
isomorphism class of the object.** The same open covering serves, restriction to an open subspace
is a functor, and Tor amplitude on each member is invariant under isomorphism. -/
theorem locallyHasFiniteTorDimension_canonicalCertificate_of_iso {Y : RingedSpace.{u, u}}
    {E E' : DerivedCategory (OXMod.{u, u} Y)} (e : E ≅ E')
    (h : LocallyHasFiniteTorDimension Y (canonicalCertifiedDerivedSheafTensoringFamily Y) E) :
    LocallyHasFiniteTorDimension Y (canonicalCertifiedDerivedSheafTensoringFamily Y) E' := by
  rw [locallyHasFiniteTorDimension_canonicalCertificate_iff] at h ⊢
  obtain ⟨J, U, hU, hfin⟩ := h
  refine ⟨J, U, hU, fun i => ?_⟩
  obtain ⟨a, b, hab⟩ := hfin i
  exact ⟨a, b, Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso hab
    ((PseudoCoherence.restrictModules Y (U i)).mapDerivedCategory.mapIso e).symm⟩

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Hom

/-- **The inverse-image ringed space of an affine morphism of affine schemes, read on spectra.**
For `f : X ⟶ S` with `X` and `S` affine, the ringed space `(X, f^{-1}𝒪_S)` is isomorphic to
`(Spec Γ(X, ⊤), (Spec f^{♯})^{-1}𝒪_{Spec Γ(S, ⊤)})`.

This is `AlgebraicGeometry.RingedSpace.inverseImageIsoOfBaseIso` at
`AlgebraicGeometry.Scheme.isoSpec` on both schemes; the square it needs is the naturality of
`AlgebraicGeometry.Scheme.toSpecΓ`, read on underlying spaces. -/
def inverseImageIsoSpec {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S] :
    RingedSpace.inverseImage S.toRingedSpace f.base ≅
      RingedSpace.inverseImage (Spec Γ(S, ⊤)).toRingedSpace (Spec.map f.appTop).base :=
  RingedSpace.inverseImageIsoOfBaseIso (Scheme.forgetToRingedSpace.mapIso S.isoSpec)
    (RingedSpace.baseHomeo (Scheme.forgetToRingedSpace.mapIso X.isoSpec)) f.base
    (Spec.map f.appTop).base (by
      have h0 : (f ≫ S.toSpecΓ).base = (X.toSpecΓ ≫ Spec.map f.appTop).base := by
        rw [Scheme.toSpecΓ_naturality f]
      change f.base ≫ S.toSpecΓ.base = X.toSpecΓ.base ≫ (Spec.map f.appTop).base
      simpa using h0)

/-- **Relative perfectness of Stacks 0DI0 transports along an isomorphism of a morphism of
schemes**, granted the matching of derived restriction of scalars with derived pullback.

Let `f : X ⟶ S` and `f' : X' ⟶ S'` be flat and locally of finite presentation, with `X`
quasi-compact, let `α : X ≅ X'` be an isomorphism of the underlying ringed spaces and
`e : (X, f^{-1}𝒪_S) ≅ (X', f'^{-1}𝒪_{S'})` an isomorphism of the inverse-image ringed spaces, and
let `E` be an object of `D(𝒪_{X'})`. If derived restriction of scalars along `f` of `Lα^*E` is the
derived pullback along `e` of derived restriction of scalars along `f'` of `E`, then `Lα^*E` is
`S`-perfect exactly when `E` is `S'`-perfect, relative perfectness being read at the canonical
certificate family on both sides.

The pseudo-coherence clause is
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedPullback_iso_iff` and needs neither the
hypothesis nor the quasi-compactness; the Tor-dimension clause is
`AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iso_iff`, which
is where both enter. -/
theorem isPerfectRelativeTo_derivedPullback_iso_iff {X X' S S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') [Flat f] [LocallyOfFinitePresentation f] [Flat f']
    [LocallyOfFinitePresentation f'] [CompactSpace X.carrier]
    (α : X.toRingedSpace ≅ X'.toRingedSpace)
    (e : RingedSpace.inverseImage S.toRingedSpace f.base ≅
      RingedSpace.inverseImage S'.toRingedSpace f'.base)
    (E : DerivedCategory (OXMod.{u, u} X'.toRingedSpace))
    (hmatch : (derivedScalarRestriction f).obj ((derivedPullback α.hom).obj E) ≅
      (derivedPullback e.hom).obj ((derivedScalarRestriction f').obj E)) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        ((derivedPullback α.hom).obj E) ↔
      f'.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E := by
  refine and_congr (RingedSpace.isPseudoCoherent_derivedPullback_iso_iff α E) ?_
  refine Iff.trans ⟨fun h =>
      RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_of_iso hmatch h,
    fun h => RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_of_iso hmatch.symm h⟩ ?_
  exact RingedSpace.locallyHasFiniteTorDimension_canonicalCertificate_iso_iff e _

/-- **Relative perfectness of Stacks 0DI0 on an affine morphism of affine schemes, read on
spectra**, granted the matching of derived restriction of scalars with derived pullback.

This is `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_derivedPullback_iso_iff` with both
isomorphisms taken to be `AlgebraicGeometry.Scheme.isoSpec`, so that the isomorphism of
inverse-image ringed spaces is the one constructed in
`AlgebraicGeometry.Scheme.Hom.inverseImageIsoSpec` and the only remaining hypothesis is the
matching. -/
theorem isPerfectRelativeTo_isoSpec_iff {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S]
    [Flat f] [LocallyOfFinitePresentation f] [Flat (Spec.map f.appTop)]
    [LocallyOfFinitePresentation (Spec.map f.appTop)] [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u, u} (Spec Γ(X, ⊤)).toRingedSpace))
    (hmatch : (derivedScalarRestriction f).obj
        ((derivedPullback (Scheme.forgetToRingedSpace.mapIso X.isoSpec).hom).obj E) ≅
      (derivedPullback (inverseImageIsoSpec f).hom).obj
        ((derivedScalarRestriction (Spec.map f.appTop)).obj E)) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        ((derivedPullback (Scheme.forgetToRingedSpace.mapIso X.isoSpec).hom).obj E) ↔
      (Spec.map f.appTop).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E :=
  isPerfectRelativeTo_derivedPullback_iso_iff f (Spec.map f.appTop)
    (Scheme.forgetToRingedSpace.mapIso X.isoSpec) (inverseImageIsoSpec f) E hmatch

end AlgebraicGeometry.Scheme.Hom

end
