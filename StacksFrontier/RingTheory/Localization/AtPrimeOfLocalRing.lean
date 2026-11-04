module

public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# A localization whose target is a local ring

Let `R → W` exhibit `W` as the localization of `R` at a submonoid `M`, and suppose that `W`
happens to be a local ring. Then `M` is not the only submonoid witnessing this: `W` is already
the localization of `R` at the prime ideal lying under the maximal ideal of `W`.

Indeed every element of `M` becomes a unit in `W`, hence avoids the maximal ideal, hence avoids
the prime below it; and conversely an element of `R` avoiding that prime has image outside the
maximal ideal, so it is a unit because `W` is local. Enlarging the localizing submonoid from `M`
to the complement of that prime is therefore harmless.

This is the standard device for recognising an a priori anonymous localization as a localization
at a prime: a localization of a localization at a prime is again local, and this lemma names the
prime it localizes at.
-/

@[expose] public section

/-- **A localization whose target is a local ring is the localization at the prime lying under
the maximal ideal.** The localizing submonoid `M` plays no role in the conclusion. -/
theorem isLocalization_atPrime_under_maximalIdeal {R : Type*} [CommRing R] (W : Type*)
    [CommRing W] [Algebra R W] [IsLocalRing W] (M : Submonoid R) [IsLocalization M W] :
    IsLocalization.AtPrime W ((IsLocalRing.maximalIdeal W).under R) :=
  IsLocalization.of_le M _
    (fun m hm h ↦ IsLocalRing.notMem_maximalIdeal.mpr (IsLocalization.map_units W ⟨m, hm⟩) h)
    (fun _ hr ↦ IsLocalRing.notMem_maximalIdeal.mp hr)

/-- A localization whose target is a local ring is the localization at any prime that is known
to lie under the maximal ideal. This is the form in which the previous lemma is applied, the
prime at hand usually having a description independent of the maximal ideal. -/
theorem isLocalization_atPrime_of_eq_under_maximalIdeal {R : Type*} [CommRing R] (W : Type*)
    [CommRing W] [Algebra R W] [IsLocalRing W] (M : Submonoid R) [IsLocalization M W]
    {P : Ideal R} [P.IsPrime] (hP : P = (IsLocalRing.maximalIdeal W).under R) :
    IsLocalization.AtPrime W P := by
  subst hP
  exact isLocalization_atPrime_under_maximalIdeal W M

end
