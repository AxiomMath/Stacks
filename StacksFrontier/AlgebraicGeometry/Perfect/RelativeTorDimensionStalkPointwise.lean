module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject

/-!
# The Tor clause of relative perfectness from a bound over the local rings of the base

Let `f : X ⟶ S` be a morphism of schemes and let `E` be an object of `D(𝒪_X)`. The Tor-dimension
conjunct of relative perfectness (Stacks 0DI0) is a condition on `E` read over `f^{-1}𝒪_S` on the
inverse-image ringed space `(X, f^{-1}𝒪_S)`. This module reduces that condition to a **pointwise**
statement about the derived stalks of `E` read over the local rings `𝒪_{S, f x}` of the base: if a
single interval `[a, b]` contains the Tor amplitude of the derived stalk of `E` at `x` over
`𝒪_{S, f x}` for every point `x` of `X`, then the Tor conjunct holds.

## Main results

* `locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_base_bound`: a single
  interval bounding the Tor amplitude of the derived stalk of `E` at every point of `X`, read over
  the local ring of the base, gives the Tor conjunct of relative perfectness.

## Implementation notes

The three exactness instances for a restriction of scalars are declared here as `local instance`s
at a **variable** ring homomorphism, as in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkObject`: at the fixed spelling in
the hypothesis below instance search does not find them, because the implicit `Ring` arguments
agree with the ones it offers only at default transparency. They are needed to state the
hypothesis, since `CategoryTheory.Functor.mapDerivedCategory` asks for all three, and a
`local instance` does not reach an importing module.

## References

* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Exactness of a restriction of scalars, seated for an arbitrary ring homomorphism -/

/-- Restriction of scalars along any ring homomorphism is additive. -/
local instance (priority := 10000) additive_restrictScalars_any'
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u} φ).Additive :=
  ⟨fun {_ _} {_ _} => rfl⟩

/-- Restriction of scalars along any ring homomorphism preserves finite limits. -/
local instance (priority := 10000) preservesFiniteLimits_restrictScalars_any'
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits φ

/-- Restriction of scalars along any ring homomorphism preserves finite colimits. -/
local instance (priority := 10000) preservesFiniteColimits_restrictScalars_any'
    {A B : Type u} [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits φ

/-- The stalk ring of the inverse-image ringed space is commutative, at every point. -/
local instance commRing_stalk_inverseImage_pointwise (y : X) :
    CommRing (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafOfRings.{u}
        (RingedSpace.inverseImage S.toRingedSpace f.base)).obj y)) :=
  RingedSpace.commRing_stalk_structureSheafOfRings _ _

/-! ### The Tor conjunct from a pointwise bound over the base -/

/-- **A single interval bounding every derived stalk over the base gives the Tor conjunct of
relative perfectness.** If one interval `[a, b]` contains the Tor amplitude over `𝒪_{S, f y}` of
the derived stalk of `E` at `y`, read over `𝒪_{S, f y}` along the stalk map of `f`, for *every*
point `y` of `X`, then `E` read over `f^{-1}𝒪_S` locally has finite Tor dimension, for every family
of certificates pinned to the genuine tensor product of sheaves of modules. -/
public theorem
    locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_base_bound
    (D : ∀ U : TopologicalSpace.Opens
        (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : IsGenuineRelativeTensorFamily f D)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (h : ∃ a b : ℤ, ∀ y : X,
      HasTorAmplitudeCanonical (ToType (S.presheaf.stalk (f.base y)))
        ((ModuleCat.restrictScalars.{u}
            ((SemilinearStalk.commStalkRingEquiv X.presheaf y).symm.toRingHom.comp
              (f.stalkMap y).hom)).mapDerivedCategory.obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafOfRings.{u} X.toRingedSpace) y).mapDerivedCategory.obj E)) a b) :
    RingedSpace.LocallyHasFiniteTorDimension
      (RingedSpace.inverseImage S.toRingedSpace f.base) D
      ((derivedScalarRestriction f).obj E) := by
  obtain ⟨a, b, hbound⟩ := h
  exact locallyHasFiniteTorDimension_derivedScalarRestriction_of_exists_uniform_bound f D hD E
    ⟨a, b, fun y =>
      (hasTorAmplitudeCanonical_derivedStalk_relative_iff f y E a b).mpr (hbound y)⟩

end AlgebraicGeometry.Scheme.Hom

end
