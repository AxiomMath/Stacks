module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity

/-!
# Transporting Tor amplitude over the base along an isomorphism of schemes

Tor amplitude over the base, `AlgebraicGeometry.HasTorAmplitudeOver`, is read at a literal
morphism of schemes. The comparison of Stacks 0DHY with the Tor amplitude of a complex of
modules is available at the morphism `Spec A ⟶ Spec R` of a ring map; a morphism of affine
schemes met in practice — for instance the restriction `f.resLE U V e` of a morphism to an
affine open of the source over an affine open of the target, which is the shape in which Stacks
0DI7 reduces to the affine case — is such a morphism only up to the isomorphisms
`AlgebraicGeometry.Scheme.isoSpec`. This file transports the predicate across those
isomorphisms.

The transport is stated for an arbitrary square whose two horizontal legs are isomorphisms,
with no affineness hypothesis; the affine statements are the instances of it at `isoSpec`. An
object of the derived category is carried from one source to the other by derived pullback along
the inverse isomorphism.

All results sit at the standard derived-category model
`CategoryTheory.HasDerivedCategory.standard`, which is the model of both ends of the comparison
(`AlgebraicGeometry.HasTorAmplitudeOver` in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange` and Stacks 0DHY in
`StacksFrontier.AlgebraicGeometry.RelativeTorAmplitudeAffine`), so no transport between models
intervenes.

## Main definitions

* `ModuleCat.restrictScalarsCompSymmIso`: restriction of scalars along a ring isomorphism is undone
  by restriction along its inverse.
* `AlgebraicGeometry.derivedPullbackSelfIso`: derived pullback along an isomorphism of schemes
  is undone by derived pullback along its inverse.

## Main results

* `AlgebraicGeometry.hasTorAmplitudeOver_derivedPullback_iff`: for a square of schemes whose two
  horizontal legs are isomorphisms, an object of the derived category of the source has Tor
  amplitude in `[a, b]` over one vertical leg exactly when its derived pullback has Tor
  amplitude in `[a, b]` over the other, and
  `AlgebraicGeometry.exists_hasTorAmplitudeOver_derivedPullback_iff` is the same statement for
  finite Tor dimension over the base.
* `AlgebraicGeometry.hasTorAmplitudeOver_specMap_appTop_iff` and
  `AlgebraicGeometry.exists_hasTorAmplitudeOver_specMap_appTop_iff`: the instance at
  `AlgebraicGeometry.Scheme.isoSpec`, for a morphism of affine schemes and the morphism of
  spectra of its ring of global sections.
* `AlgebraicGeometry.hasTorAmplitudeOver_resLE_iff` and
  `AlgebraicGeometry.exists_hasTorAmplitudeOver_resLE_iff`: the instance at
  `AlgebraicGeometry.IsAffineOpen.isoSpec`, for the restriction of a morphism to an affine open
  of the source over an affine open of the target.
* `AlgebraicGeometry.hasTorAmplitudeOver_comp_iff`: Tor amplitude over the base is unchanged by
  composing the base morphism with an isomorphism.
* `AlgebraicGeometry.hasTorAmplitudeOver_derivedPullback_inv_comp_iff`: Tor amplitude over the
  base is unchanged by replacing the source by an isomorphic one.
* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonicalLift_restrictScalars_ringEquiv_iff` and
  `StacksDraft.TorAmplitude.hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff`: the
  ring-level invariance the two geometric steps rest on.

## Implementation notes

The predicate is stalkwise, so the two steps of the transport are of different kinds. Changing
the source is a base change along an isomorphism, which is a base change along an open
immersion, so it is
`AlgebraicGeometry.hasTorAmplitudeOver_derivedPullback_of_isOpenImmersion` in one direction and
that lemma along the inverse isomorphism, composed with `derivedPullbackSelfIso`, in the other.
Changing the base keeps the representing complex and changes only the ring over which its stalk
complexes are read, by the germ isomorphism of the base isomorphism; that is the ring-level
invariance of Tor amplitude under restriction of scalars along a ring isomorphism.

The ring-level statements take the three ring maps abstractly, with the factorisation as a
hypothesis, rather than mentioning the germ maps: `(f ≫ d).base x` and `d.base (f.base x)` are
definitionally but not reducibly equal, so a goal naming both spellings of the base ring does
not elaborate at instance transparency. `Stacks.ModuleSkyscraper.stalkMap_hom_comp` supplies the
factorisation at the application.

The identification of `Γ(V.toScheme, ⊤)` with `Γ(X, V)` needed by the `resLE` statement is
already folded into `AlgebraicGeometry.IsAffineOpen.isoSpec` through
`AlgebraicGeometry.Scheme.Opens.topIso`, and the commuting square is
`AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE`; the statement therefore comes out in
terms of `Γ(X, V)`, `Γ(Y, U)` and `AlgebraicGeometry.Scheme.Hom.appLE` with no further
comparison.

The morphism `Spec A ⟶ Spec R` of a ring map is `Spec.map (CommRingCat.ofHom (algebraMap R A))`,
so `hasTorAmplitudeOver_derivedPullback_iff` applies to it with no further work: it is the
general statement at `f'` that spelling, with the two isomorphisms exhibiting the source and the
base as spectra.

## References

* [Stacks Project, Tag 0DHY](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0C0V](https://stacks.math.columbia.edu/tag/0C0V)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction of scalars along a ring isomorphism -/

namespace ModuleCat

/-- **Restriction of scalars along a ring isomorphism is undone by restriction along its
inverse.** -/
public def restrictScalarsCompSymmIso {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    restrictScalars.{u} e.toRingHom ⋙ restrictScalars.{u} e.symm.toRingHom ≅
      𝟭 (ModuleCat.{u} S) :=
  (restrictScalarsComp'.{u} e.symm.toRingHom e.toRingHom
      (e.toRingHom.comp e.symm.toRingHom) rfl).symm ≪≫
    restrictScalarsId'.{u} _ (by ext x; simp)

end ModuleCat

namespace StacksDraft.TorAmplitude

/-- **Tor amplitude is unchanged by restricting scalars along a ring isomorphism.** -/
public theorem hasTorAmplitudeCanonicalLift_restrictScalars_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (N : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ)
    (hN : HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj N) a b) :
    HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)) a b :=
  hasTorAmplitudeCanonical_moduleLift _ a b
    (hasTorAmplitudeCanonical_of_iso
      ((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategoryFactors.app N) a b
      (hasTorAmplitudeCanonical_restrictScalars_ringEquiv e (DerivedCategory.Q.obj N) a b
        (hasTorAmplitudeCanonical_of_moduleLift N a b hN)))

/-- **Restricting scalars along a ring isomorphism changes neither the Tor amplitude nor its
interval**, in either direction: the inverse isomorphism restricts back. -/
public theorem hasTorAmplitudeCanonicalLift_restrictScalars_ringEquiv_iff
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (N : CochainComplex (ModuleCat.{u} S) ℤ) (a b : ℤ) :
    HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)) a b ↔
      HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj N) a b := by
  refine ⟨fun h => ?_, hasTorAmplitudeCanonicalLift_restrictScalars_ringEquiv e N a b⟩
  exact hasTorAmplitudeCanonicalLift_of_iso (DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsCompSymmIso e)
        (ComplexShape.up ℤ)).app N ≪≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} S) (ComplexShape.up ℤ)).app N))
    a b (hasTorAmplitudeCanonicalLift_restrictScalars_ringEquiv e.symm _ a b h)

/-- **Tor amplitude over a ring is unchanged by precomposing the ring map with an
isomorphism.** If `τ = σ ∘ ρ` with `ρ` the ring map of an isomorphism `e`, then a complex
restricted along `τ` has Tor amplitude in `[a, b]` exactly when restricted along `σ` it does. -/
public theorem hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    (σ : S →+* A) (ρ : R →+* S) (τ : R →+* A) (e : R ≃+* S)
    (he : e.toRingHom = ρ) (hτ : τ = σ.comp ρ)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) :
    HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars τ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) a b ↔
      HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))
        a b := by
  subst he
  refine Iff.trans ?_ (hasTorAmplitudeCanonicalLift_restrictScalars_ringEquiv_iff e
    (((ModuleCat.restrictScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) a b)
  have hiso := (Functor.mapHomologicalComplexCompIso
    (ModuleCat.restrictScalarsComp'.{u} e.toRingHom σ τ hτ).symm (ComplexShape.up ℤ)).app M
  exact ⟨fun h => hasTorAmplitudeCanonicalLift_of_iso (DerivedCategory.Q.mapIso hiso.symm) a b h,
    fun h => hasTorAmplitudeCanonicalLift_of_iso (DerivedCategory.Q.mapIso hiso) a b h⟩

end StacksDraft.TorAmplitude

namespace AlgebraicGeometry

/-! ### Changing the base along an isomorphism -/

/-- **Tor amplitude over the base is unchanged by composing the base morphism with an
isomorphism.** The representing complex is the same on both sides; only the ring over which its
stalk complexes are read changes, by the germ isomorphism of the base isomorphism. -/
public theorem hasTorAmplitudeOver_comp_iff {X Y Z : Scheme.{u}} (f : X ⟶ Y) (d : Y ⟶ Z)
    [IsIso d] (E : DerivedCategory X.Modules) (a b : ℤ) :
    HasTorAmplitudeOver (f ≫ d) E a b ↔ HasTorAmplitudeOver f E a b := by
  have key : ∀ (K : CochainComplex X.Modules ℤ) (x : X),
      HasTorAmplitudeCanonicalLift.{u, u, u}
          (DerivedCategory.Q.obj (relativeStalkComplex (f ≫ d) K x)) a b ↔
        HasTorAmplitudeCanonicalLift.{u, u, u}
          (DerivedCategory.Q.obj (relativeStalkComplex f K x)) a b := fun K x =>
    hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff (f.stalkMap x).hom
      (d.stalkMap (f.base x)).hom ((f ≫ d).stalkMap x).hom
      (asIso (d.stalkMap (f.base x))).commRingCatIsoToRingEquiv rfl
      (Stacks.ModuleSkyscraper.stalkMap_hom_comp f d x) _ a b
  exact ⟨fun ⟨K, hK, h⟩ => ⟨K, hK, fun x => (key K x).1 (h x)⟩,
    fun ⟨K, hK, h⟩ => ⟨K, hK, fun x => (key K x).2 (h x)⟩⟩

/-! ### Changing the source along an isomorphism -/

/-- The morphism of ringed spaces underlying an isomorphism of schemes composed with the one
underlying its inverse is the identity. -/
public theorem toShHom_hom_inv_id {X X' : Scheme.{u}} (e : X ≅ X') :
    e.hom.toLRSHom.toShHom ≫ e.inv.toLRSHom.toShHom = 𝟙 X.toRingedSpace := by
  rw [show e.hom.toLRSHom.toShHom ≫ e.inv.toLRSHom.toShHom
      = (e.hom ≫ e.inv).toLRSHom.toShHom from rfl, e.hom_inv_id]
  rfl

/-- **Derived pullback along an isomorphism of schemes is undone by derived pullback along its
inverse.** This is Stacks 0D5S, the composition isomorphism of derived pullback, together with
the identification of derived pullback along an identity with the identity functor. -/
public def derivedPullbackSelfIso {X X' : Scheme.{u}} (e : X ≅ X')
    (E : DerivedCategory X.Modules) :
    (derivedPullback e.hom.toLRSHom.toShHom).obj
        ((derivedPullback e.inv.toLRSHom.toShHom).obj E) ≅ E :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      e.hom.toLRSHom.toShHom e.inv.toLRSHom.toShHom).app E ≪≫
    eqToIso (congrArg (fun m : X.toRingedSpace ⟶ X.toRingedSpace => (derivedPullback m).obj E)
      (toShHom_hom_inv_id e)) ≪≫
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso
      X.toRingedSpace).app E

/-- **Tor amplitude over the base is unchanged by replacing the source by an isomorphic
scheme.** An object of `D(𝒪_X)` has Tor amplitude in `[a, b]` relative to `f : X ⟶ S` exactly
when its derived pullback along `e.inv : X' ⟶ X` has Tor amplitude in `[a, b]` relative to
`e.inv ≫ f`. -/
public theorem hasTorAmplitudeOver_derivedPullback_inv_comp_iff {X X' Y : Scheme.{u}}
    (e : X ≅ X') (f : X ⟶ Y) (E : DerivedCategory X.Modules) (a b : ℤ) :
    HasTorAmplitudeOver (e.inv ≫ f) ((derivedPullback e.inv.toLRSHom.toShHom).obj E) a b ↔
      HasTorAmplitudeOver f E a b := by
  refine ⟨fun h => ?_, hasTorAmplitudeOver_derivedPullback_of_isOpenImmersion f e.inv E a b⟩
  have h' := hasTorAmplitudeOver_derivedPullback_of_isOpenImmersion (e.inv ≫ f) e.hom
    ((derivedPullback e.inv.toLRSHom.toShHom).obj E) a b h
  rw [show e.hom ≫ e.inv ≫ f = f by rw [← Category.assoc, e.hom_inv_id, Category.id_comp]] at h'
  exact hasTorAmplitudeOver_of_iso (derivedPullbackSelfIso e E) a b h'

/-! ### The transport -/

/-- **Tor amplitude over the base transports across a square whose horizontal legs are
isomorphisms.** For `f : X ⟶ Y`, `f' : X' ⟶ Y'` and isomorphisms `eX : X ≅ X'`, `eY : Y ≅ Y'`
with `f ≫ eY.hom = eX.hom ≫ f'`, an object of `D(𝒪_X)` has Tor amplitude in `[a, b]` relative
to `f` exactly when its derived pullback along `eX.inv` has Tor amplitude in `[a, b]` relative
to `f'`. -/
public theorem hasTorAmplitudeOver_derivedPullback_iff {X X' Y Y' : Scheme.{u}}
    (eX : X ≅ X') (eY : Y ≅ Y') (f : X ⟶ Y) (f' : X' ⟶ Y') (w : f ≫ eY.hom = eX.hom ≫ f')
    (E : DerivedCategory X.Modules) (a b : ℤ) :
    HasTorAmplitudeOver f' ((derivedPullback eX.inv.toLRSHom.toShHom).obj E) a b ↔
      HasTorAmplitudeOver f E a b := by
  have hw : eX.inv ≫ f = f' ≫ eY.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact w
  refine Iff.trans ?_ (hasTorAmplitudeOver_derivedPullback_inv_comp_iff eX f E a b)
  rw [hw]
  exact (hasTorAmplitudeOver_comp_iff f' eY.inv _ a b).symm

/-- **Finite Tor dimension over the base transports across a square whose horizontal legs are
isomorphisms.** The interval version is `hasTorAmplitudeOver_derivedPullback_iff`. -/
public theorem exists_hasTorAmplitudeOver_derivedPullback_iff {X X' Y Y' : Scheme.{u}}
    (eX : X ≅ X') (eY : Y ≅ Y') (f : X ⟶ Y) (f' : X' ⟶ Y') (w : f ≫ eY.hom = eX.hom ≫ f')
    (E : DerivedCategory X.Modules) :
    (∃ a b : ℤ, HasTorAmplitudeOver f' ((derivedPullback eX.inv.toLRSHom.toShHom).obj E) a b) ↔
      ∃ a b : ℤ, HasTorAmplitudeOver f E a b :=
  exists_congr fun a => exists_congr fun b =>
    hasTorAmplitudeOver_derivedPullback_iff eX eY f f' w E a b

/-- **Tor amplitude over the base of a morphism of affine schemes is Tor amplitude over the
morphism of spectra of its rings of global sections.** For `f : X ⟶ Y` with `X` and `Y` affine,
an object of `D(𝒪_X)` has Tor amplitude in `[a, b]` relative to `f` exactly when its derived
pullback along `X.isoSpec.inv` has Tor amplitude in `[a, b]` relative to
`Spec.map f.appTop : Spec Γ(X, ⊤) ⟶ Spec Γ(Y, ⊤)`. -/
public theorem hasTorAmplitudeOver_specMap_appTop_iff {X Y : Scheme.{u}} [IsAffine X]
    [IsAffine Y] (f : X ⟶ Y) (E : DerivedCategory X.Modules) (a b : ℤ) :
    HasTorAmplitudeOver (Spec.map f.appTop)
        ((derivedPullback X.isoSpec.inv.toLRSHom.toShHom).obj E) a b ↔
      HasTorAmplitudeOver f E a b :=
  hasTorAmplitudeOver_derivedPullback_iff X.isoSpec Y.isoSpec f (Spec.map f.appTop)
    (Scheme.isoSpec_hom_naturality f).symm E a b

/-- **Finite Tor dimension over the base of a morphism of affine schemes is finite Tor dimension
over the morphism of spectra of its rings of global sections.** -/
public theorem exists_hasTorAmplitudeOver_specMap_appTop_iff {X Y : Scheme.{u}} [IsAffine X]
    [IsAffine Y] (f : X ⟶ Y) (E : DerivedCategory X.Modules) :
    (∃ a b : ℤ, HasTorAmplitudeOver (Spec.map f.appTop)
        ((derivedPullback X.isoSpec.inv.toLRSHom.toShHom).obj E) a b) ↔
      ∃ a b : ℤ, HasTorAmplitudeOver f E a b :=
  exists_congr fun a => exists_congr fun b =>
    hasTorAmplitudeOver_specMap_appTop_iff f E a b

/-- **Tor amplitude over the restriction of a morphism to affine opens is Tor amplitude over the
morphism of spectra of the sections on them.** For `f : X ⟶ Y`, an affine open `V` of `X` and an
affine open `U` of `Y` with `V ≤ f ⁻¹ᵁ U`, an object of `D(𝒪_V)` has Tor amplitude in `[a, b]`
relative to `f.resLE U V e` exactly when its derived pullback along `hV.isoSpec.inv` has Tor
amplitude in `[a, b]` relative to `Spec.map (f.appLE U V e) : Spec Γ(X, V) ⟶ Spec Γ(Y, U)`. -/
public theorem hasTorAmplitudeOver_resLE_iff {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (E : DerivedCategory V.toScheme.Modules) (a b : ℤ) :
    HasTorAmplitudeOver (Spec.map (f.appLE U V e))
        ((derivedPullback hV.isoSpec.inv.toLRSHom.toShHom).obj E) a b ↔
      HasTorAmplitudeOver (f.resLE U V e) E a b :=
  hasTorAmplitudeOver_derivedPullback_iff hV.isoSpec hU.isoSpec (f.resLE U V e)
    (Spec.map (f.appLE U V e)) (Scheme.Opens.toSpecΓ_SpecMap_appLE f U V e).symm E a b

/-- **Finite Tor dimension over the restriction of a morphism to affine opens is finite Tor
dimension over the morphism of spectra of the sections on them.** -/
public theorem exists_hasTorAmplitudeOver_resLE_iff {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (E : DerivedCategory V.toScheme.Modules) :
    (∃ a b : ℤ, HasTorAmplitudeOver (Spec.map (f.appLE U V e))
        ((derivedPullback hV.isoSpec.inv.toLRSHom.toShHom).obj E) a b) ↔
      ∃ a b : ℤ, HasTorAmplitudeOver (f.resLE U V e) E a b :=
  exists_congr fun a => exists_congr fun b =>
    hasTorAmplitudeOver_resLE_iff f hU hV e E a b

end AlgebraicGeometry

end
