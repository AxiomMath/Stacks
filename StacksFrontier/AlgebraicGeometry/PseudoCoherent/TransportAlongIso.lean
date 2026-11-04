module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeAffineTransport
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBridge
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback

/-!
# Transport of pseudo-coherence and of finite Tor dimension along a morphism of schemes

Two hypotheses of the affine case of Stacks 0DI7 are conditions on the module-level avatars of
objects of `D(𝒪_{V₀})` over an affine open `V₀`: pseudo-coherence, and finite Tor dimension over
the ring of sections of an affine open of the base. Both are obtained from the corresponding
condition upstairs by transporting it along `AlgebraicGeometry.IsAffineOpen.isoSpec` and reading
the result through Stacks 08E7, resp. Stacks 0DHY.

The pseudo-coherence half needs no hypothesis on the morphism at all: Stacks 09U7 is already the
statement for an arbitrary morphism of ringed spaces, and what is recorded here is its unbounded
form together with both forms in the spelling of a morphism of schemes. An isomorphism, and more
generally an open immersion, is a special case.

## Main results

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback`: the
  derived pullback of a pseudo-coherent object along a morphism of ringed spaces is
  pseudo-coherent.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback` and
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherent_derivedPullback`: the same for a morphism of
  schemes, `m`-bounded and unbounded.
* `AlgebraicGeometry.hasFiniteTorDimensionCanonical_of_hasTorAmplitudeOver_resLE`:
  an object of `D(𝒪_V)` of finite Tor dimension relative to `f.resLE U V e`, whose transport to
  `Spec Γ(X, V)` is the derived sheafification of an object `𝕃` of `D(Γ(X, V))`, has for `𝕃` an
  object of finite Tor dimension over `Γ(Y, U)`.
* `AlgebraicGeometry.hasFiniteTorDimensionCanonical_appTop_of_hasTorAmplitudeOver_resLE`:
  the same with `V` identified with `Spec Γ(V.toScheme, ⊤)` instead, so that the base ring is
  `Γ(U.toScheme, ⊤)` and the algebra structure is the one given by `(f.resLE U V e).appTop`.

## Implementation notes

The unbounded pseudo-coherence predicate asks for a *single* complex which is
`m`-pseudo-coherent for every `m`, so it is not the conjunction over `m` of the bounded one; it
is nevertheless equivalent to that conjunction, by
`AlgebraicGeometry.RingedSpace.isPseudoCoherent_iff_forall`, which is what reduces the unbounded
statement to Stacks 09U7.

The Tor-dimension half is a composite of existing results, the only work being the passage between
the two descriptions of derived sheafification and of restriction of scalars: the hypothesis and
the conclusion are phrased at `CategoryTheory.Functor.mapDerivedCategory`, whereas Stacks 0DHY
is available at `CategoryTheory.Functor.mapHomologicalComplex` followed by the localisation
functor, and `CategoryTheory.Functor.mapDerivedCategoryFactors` crosses between them at the
canonical complex representing `𝕃`.

Which ring the module-level avatar lives over is decided by which identification of `V` with a
spectrum is used, and both are available without any comparison of the two:
`AlgebraicGeometry.IsAffineOpen.isoSpec` is `AlgebraicGeometry.Scheme.isoSpec` followed by
`AlgebraicGeometry.Scheme.Opens.topIso`, so the first lands on `Spec Γ(X, V)` and the second on
`Spec Γ(V.toScheme, ⊤)`, and Stacks 0DHY is available at each — at `f.appLE U V e` by
`AlgebraicGeometry.exists_hasTorAmplitudeOver_resLE_iff` and at `(f.resLE U V e).appTop` by
`AlgebraicGeometry.exists_hasTorAmplitudeOver_specMap_appTop_iff`. Each statement below is
therefore proved from the existing result at its own spelling; no transport of finite Tor dimension
along `AlgebraicGeometry.Scheme.Opens.topIso` is needed, and none is carried out.

Everything is stated at `CategoryTheory.HasDerivedCategory.standard`, the model in which the
derived pullback and its coherences are built. The local instance is given a high priority
because part of the import closure supplies a global instance of the same class.

## References

* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.46.9 (Tag 08CC)](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Lemma 20.46.13 (Tag 09U7)](https://stacks.math.columbia.edu/tag/09U7)
* [Stacks Project, Lemma 36.10.2 (Tag 08E7)](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Lemma 35.9.1 (Tag 0DI7)](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Lemma 36.21.3 (Tag 0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open RingedSpaceModuleAdjunction
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

/-- **The derived pullback of a pseudo-coherent object along a morphism of ringed spaces is
pseudo-coherent.** The unbounded form of Stacks 09U7. -/
public theorem isPseudoCoherent_derivedPullback {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (E : DerivedCategory (OXMod.{u, u} Y)) (hE : IsPseudoCoherent (X := Y) E) :
    IsPseudoCoherent (X := X) ((derivedPullback f).obj E) :=
  (isPseudoCoherent_iff_forall ((derivedPullback f).obj E)).2 fun m =>
    isPseudoCoherentFrom_derivedPullback f E m ((isPseudoCoherent_iff_forall E).1 hE m)

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

namespace AlgebraicGeometry.Scheme.Hom

/-- **The derived pullback of an `m`-pseudo-coherent object along a morphism of schemes is
`m`-pseudo-coherent.** Stacks 09U7 read at the morphism of ringed spaces underlying `f`. -/
public theorem isPseudoCoherentFrom_derivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory (OXMod.{u, u} Y.toRingedSpace)) (m : ℤ)
    (hE : RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) E m) :
    RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace)
      ((derivedPullback f.toLRSHom.toShHom).obj E) m :=
  RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback f.toLRSHom.toShHom E m hE

/-- **The derived pullback of a pseudo-coherent object along a morphism of schemes is
pseudo-coherent.** The unbounded form of
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback`. -/
public theorem isPseudoCoherent_derivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategory (OXMod.{u, u} Y.toRingedSpace))
    (hE : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent (X := X.toRingedSpace)
      ((derivedPullback f.toLRSHom.toShHom).obj E) :=
  RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback f.toLRSHom.toShHom E hE

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- Finite Tor dimension over `R` of the restriction of scalars of `𝕃 : D(A)`, from Tor amplitude
over `Spec A ⟶ Spec R` of an object isomorphic to the derived sheafification of `𝕃`. -/
private theorem hasFiniteTorDimensionCanonical_restrictScalars_of_iso (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] {T : DerivedCategory (Spec (CommRingCat.of A)).Modules}
    (𝕃 : DerivedCategory (ModuleCat.{u} A))
    (eL : T ≅ (tilde.functor (CommRingCat.of A)).mapDerivedCategory.obj 𝕃)
    (hT : ∃ a b : ℤ, HasTorAmplitudeOver (AffineRelativeTorAmplitude.specMap R A) T a b) :
    HasFiniteTorDimensionCanonical R
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj 𝕃) := by
  obtain ⟨M, eQ⟩ : Σ' M : CochainComplex (ModuleCat.{u} A) ℤ, DerivedCategory.Q.obj M ≅ 𝕃 :=
    ⟨DerivedCategory.Q.objPreimage 𝕃, DerivedCategory.Q.objObjPreimageIso 𝕃⟩
  have eT : T ≅ DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M) :=
    eL ≪≫ (tilde.functor (CommRingCat.of A)).mapDerivedCategory.mapIso eQ.symm ≪≫
      (tilde.functor (CommRingCat.of A)).mapDerivedCategoryFactors.app M
  have h₃ := (AffineRelativeTorAmplitude.exists_hasTorAmplitudeOver_tildeComplex_iff R A M).1
    (by
      obtain ⟨a, b, hab⟩ := hT
      exact ⟨a, b, hasTorAmplitudeOver_of_iso eT a b hab⟩)
  obtain ⟨a, b, hab⟩ :=
    (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).1 h₃
  refine (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).2 ⟨a, b, ?_⟩
  exact hasTorAmplitudeCanonical_of_iso
    (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.app M).symm ≪≫
      (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.mapIso eQ) a b hab

/-- **Finite Tor dimension over an affine open of the base, read on the module-level avatar.**
Let `V` be an affine open of `X` contained in the preimage of an affine open `U` of `Y`, let `E`
be an object of `D(𝒪_V)` of finite Tor dimension relative to `f.resLE U V e`, and let `𝕃` be an
object of `D(Γ(X, V))` whose derived sheafification is the transport of `E` to `Spec Γ(X, V)`.
Then `𝕃`, read over `Γ(Y, U)` along `f.appLE U V e`, has finite Tor dimension. -/
public theorem hasFiniteTorDimensionCanonical_of_hasTorAmplitudeOver_resLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) (E : DerivedCategory V.toScheme.Modules)
    (𝕃 : DerivedCategory (ModuleCat.{u} Γ(X, V)))
    (eL : (derivedPullback hV.isoSpec.inv.toLRSHom.toShHom).obj E ≅
      (tilde.functor Γ(X, V)).mapDerivedCategory.obj 𝕃)
    (hE : ∃ a b : ℤ, HasTorAmplitudeOver (f.resLE U V e) E a b) :
    letI : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
    HasFiniteTorDimensionCanonical Γ(Y, U)
      ((ModuleCat.restrictScalars
        (algebraMap Γ(Y, U) Γ(X, V))).mapDerivedCategory.obj 𝕃) := by
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
  exact hasFiniteTorDimensionCanonical_restrictScalars_of_iso Γ(Y, U) Γ(X, V) 𝕃 eL
    ((exists_hasTorAmplitudeOver_resLE_iff f hU hV e E).2 hE)

/-- **Finite Tor dimension over an affine open of the base, on the sections of the restricted
schemes.** The same statement as
`AlgebraicGeometry.hasFiniteTorDimensionCanonical_of_hasTorAmplitudeOver_resLE`,
with `V` identified with the spectrum of `Γ(V.toScheme, ⊤)` by
`AlgebraicGeometry.Scheme.isoSpec` and the base ring taken to be `Γ(U.toScheme, ⊤)`, so that the
algebra structure is the one given by `(f.resLE U V e).appTop`. -/
public theorem hasFiniteTorDimensionCanonical_appTop_of_hasTorAmplitudeOver_resLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) (E : DerivedCategory V.toScheme.Modules)
    (𝕃 : DerivedCategory (ModuleCat.{u} Γ(V.toScheme, ⊤)))
    (eL :
      haveI : IsAffine V.toScheme := hV
      (derivedPullback V.toScheme.isoSpec.inv.toLRSHom.toShHom).obj E ≅
        (tilde.functor Γ(V.toScheme, ⊤)).mapDerivedCategory.obj 𝕃)
    (hE : ∃ a b : ℤ, HasTorAmplitudeOver (f.resLE U V e) E a b) :
    letI : Algebra Γ(U.toScheme, ⊤) Γ(V.toScheme, ⊤) :=
      ((f.resLE U V e).appTop).hom.toAlgebra
    HasFiniteTorDimensionCanonical Γ(U.toScheme, ⊤)
      ((ModuleCat.restrictScalars
        (algebraMap Γ(U.toScheme, ⊤) Γ(V.toScheme, ⊤))).mapDerivedCategory.obj 𝕃) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let : Algebra Γ(U.toScheme, ⊤) Γ(V.toScheme, ⊤) := ((f.resLE U V e).appTop).hom.toAlgebra
  exact hasFiniteTorDimensionCanonical_restrictScalars_of_iso Γ(U.toScheme, ⊤) Γ(V.toScheme, ⊤) 𝕃 eL
    ((exists_hasTorAmplitudeOver_specMap_appTop_iff (f.resLE U V e) E).2 hE)

end AlgebraicGeometry

end
