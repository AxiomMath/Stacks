module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeAffineTransport
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChange

/-!
# Precomposing the coefficient map with an isomorphism, at an arbitrary object

Let `ρ : R →+* S` be the ring map of an isomorphism `e : R ≃+* S`, let `σ : S →+* A` and let
`τ = σ ∘ ρ`. Then an object of `D(A)` restricted along `τ` has Tor amplitude in `[a, b]` over `R`
exactly when restricted along `σ` it has Tor amplitude in `[a, b]` over `S`.

`StacksDraft.TorAmplitude.hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff` is this statement
for a *cochain complex* and the `ULift`-based Tor amplitude of Stacks 066K. What is added here is
the passage to an arbitrary object of `D(A)` and to
`StacksDraft.TorAmplitude.HasTorAmplitudeCanonical`, which is the form every stalk computation in
this directory is stated at.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_restrictScalars_comp_obj_iff`: the statement.

## Implementation notes

The route is the one
`AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff` takes
for the isomorphism case: `CategoryTheory.Functor.objObjPreimageIso` replaces the object by
`DerivedCategory.Q` of a representative, `Functor.mapDerivedCategoryFactors` moves the restriction
of scalars inside `DerivedCategory.Q`, and
`StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_lift` exchanges the two Tor-amplitude
predicates at an arbitrary object. Only then is the complex-level engine applied.

**Why this avoids the obstruction recorded for `stalkOverBase`.** The implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject` record that the descent
of `AlgebraicGeometry.Scheme.Hom.stalkOverBase` to the derived categories cannot be formed, because
`CategoryTheory.Functor.mapDerivedCategory` of that three-fold composite needs exactness instances
that instance search rejects at the two spellings of the stalk ring's `NonAssocSemiring`. Nothing
here forms the derived functor of a composite: the statement mentions `ModuleCat.restrictScalars`
only at the *individual* ring homomorphisms `τ` and `σ`, and the factorisation `τ = σ ∘ ρ` enters
as an equation between ring homomorphisms rather than as an isomorphism of composed functors. So
the obstruction is an artefact of that route and not of the mathematics, and the coefficient
crossing is available without it.

The three exactness facts are nonetheless re-seated for a *variable* ring homomorphism at high
priority, exactly as `RelativeTorDimensionStalkObject` does and for the same reason: `τ` and `σ`
are arbitrary here, so no fixed-homomorphism instance applies.

No `stacks` attribute is placed. This is a change-of-rings bookkeeping statement about Tor
amplitude, not a clause of any tag.

## References

* [Stacks Project, Lemma 15.65.2 (0652)](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Lemma 15.65.6 (0654)](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Section 15.66 (066K)](https://stacks.math.columbia.edu/tag/066K)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace StacksDraft.TorAmplitude

/-- Restriction of scalars along any ring homomorphism is additive. -/
local instance (priority := 10000) additive_restrictScalars_comp_any
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u} φ).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along any ring homomorphism preserves finite limits. -/
local instance (priority := 10000) preservesFiniteLimits_restrictScalars_comp_any
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits φ

/-- Restriction of scalars along any ring homomorphism preserves finite colimits. -/
local instance (priority := 10000) preservesFiniteColimits_restrictScalars_comp_any
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits φ

/-- Restriction of scalars of an object of `D(A)` along a ring homomorphism, compared with
`DerivedCategory.Q` of the degreewise restriction of a representative. -/
private def restrictScalarsObjIso {A B : Type u} [CommRing A] [CommRing B] (φ : B →+* A)
    (E : DerivedCategory (ModuleCat.{u} A)) :
    (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj E ≅
      DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (DerivedCategory.Q.objPreimage E)) :=
  (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
    (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.app _

/-- **Tor amplitude over a ring is unchanged by precomposing the coefficient map with an
isomorphism**, for an arbitrary object of the derived category. If `τ = σ ∘ ρ` with `ρ` the ring
map of an isomorphism `e : R ≃+* S`, then `E` restricted along `τ` has Tor amplitude in `[a, b]`
over `R` exactly when `E` restricted along `σ` has Tor amplitude in `[a, b]` over `S`.

`hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff` is the same statement for a cochain
complex and the lifted predicate; the passage to an arbitrary object and to
`HasTorAmplitudeCanonical` is the content here. -/
public theorem hasTorAmplitudeCanonical_restrictScalars_comp_obj_iff
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    (σ : S →+* A) (ρ : R →+* S) (τ : R →+* A) (e : R ≃+* S)
    (he : e.toRingHom = ρ) (hτ : τ = σ.comp ρ)
    (E : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ) :
    HasTorAmplitudeCanonical R
        ((ModuleCat.restrictScalars.{u} τ).mapDerivedCategory.obj E) a b ↔
      HasTorAmplitudeCanonical S
        ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategory.obj E) a b := by
  rw [hasTorAmplitudeCanonical_iff_lift, hasTorAmplitudeCanonical_iff_lift]
  refine Iff.trans ⟨fun h => hasTorAmplitudeCanonicalLift_of_iso
      (restrictScalarsObjIso τ E) a b h,
    fun h => hasTorAmplitudeCanonicalLift_of_iso (restrictScalarsObjIso τ E).symm a b h⟩ ?_
  refine Iff.trans
    (hasTorAmplitudeCanonicalLift_restrictScalars_comp_iff σ ρ τ e he hτ
      (DerivedCategory.Q.objPreimage E) a b) ?_
  exact ⟨fun h => hasTorAmplitudeCanonicalLift_of_iso (restrictScalarsObjIso σ E).symm a b h,
    fun h => hasTorAmplitudeCanonicalLift_of_iso (restrictScalarsObjIso σ E) a b h⟩

end StacksDraft.TorAmplitude

end
