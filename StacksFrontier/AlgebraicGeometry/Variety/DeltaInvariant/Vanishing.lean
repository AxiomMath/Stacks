module

public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.RingTheory.Noetherian.Spec

/-!
# Vanishing of the delta invariant

The delta invariant of a reduced one-dimensional Nagata local ring vanishes exactly when the
ring is a discrete valuation ring.

## Main results

* `Ring.deltaInvariant_eq_zero_iff_isDiscreteValuationRing` characterizes vanishing of the
  delta invariant.

## Implementation notes

The delta invariant is the extended-natural-valued invariant defined in Tag 0C3T, and a
discrete valuation ring is expressed by Mathlib's `IsDiscreteValuationRing` predicate.

## References

* [Stacks Project, Tag 0C3U](https://stacks.math.columbia.edu/tag/0C3U)
-/

@[expose] public section

namespace Ring

/-- The delta invariant of a ring vanishes if and only if the ring is integrally closed. -/
private lemma deltaInvariant_eq_zero_iff_isIntegrallyClosed
    {A : Type*} [CommRing A] : deltaInvariant A = 0 ↔ IsIntegrallyClosed A := by
  rw [deltaInvariant, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    LinearMap.range_eq_top, isIntegrallyClosed_iff (K := FractionRing A)]
  refine ⟨fun h x hx => ?_, fun h x => ?_⟩
  · obtain ⟨a, ha⟩ := h ⟨x, hx⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  · obtain ⟨a, ha⟩ := h x.2
    exact ⟨a, Subtype.ext ha⟩


/-- For an integrally closed ring, the canonical map to its integral closure in the total ring
of fractions is already surjective. -/
private lemma integralClosure_range_eq_top_of_isIntegrallyClosed
    {A : Type*} [CommRing A] (hA : IsIntegrallyClosed A) :
    LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) = ⊤ :=
  LinearMap.range_eq_top.mpr fun x => by
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff (K := FractionRing A)).mp hA x.2
    exact ⟨a, Subtype.ext ha⟩

/-- An integrally closed ring has vanishing delta invariant. -/
private lemma deltaInvariant_eq_zero_of_isIntegrallyClosed
    {A : Type*} [CommRing A] (hA : IsIntegrallyClosed A) :
    deltaInvariant A = 0 := by
  rw [deltaInvariant, integralClosure_range_eq_top_of_isIntegrallyClosed hA]
  exact Module.length_eq_zero_iff.mpr (Submodule.Quotient.subsingleton_iff.mpr rfl)


/-- A reduced one-dimensional Nagata local ring has delta invariant zero if and only if it is a
discrete valuation ring. -/
@[stacks 0C3U]
public lemma deltaInvariant_eq_zero_iff_isDiscreteValuationRing
    {A : Type*} [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : IsNagataRing A) (hdim : ringKrullDim A = 1) :
    deltaInvariant A = 0 ↔ ∃ _ : IsDomain A, IsDiscreteValuationRing A := by
  let : IsNoetherianRing A := hA.1
  constructor
  · intro hδ
    have hIC : IsIntegrallyClosed A := deltaInvariant_eq_zero_iff_isIntegrallyClosed.mp hδ
    have hnormal :=
      (isIntegrallyClosed_tfae_of_finite_minimalPrimes
        (minimalPrimes.finite_of_isNoetherianRing A)).out 2 1 |>.mp hIC
    let : (IsLocalRing.maximalIdeal A).IsPrime := inferInstance
    let : IsLocalization.AtPrime A (IsLocalRing.maximalIdeal A) :=
      IsLocalization.self fun x hx => IsLocalRing.notMem_maximalIdeal.mp hx
    let e : Localization.AtPrime (IsLocalRing.maximalIdeal A) ≃ₐ[A] A :=
      IsLocalization.algEquiv (IsLocalRing.maximalIdeal A).primeCompl
        (Localization.AtPrime (IsLocalRing.maximalIdeal A)) A
    let : IsDomain (Localization.AtPrime (IsLocalRing.maximalIdeal A)) :=
      (hnormal (IsLocalRing.maximalIdeal A)).1
    let : IsDomain A :=
      Function.Injective.isDomain
        (e.symm : A →+* Localization.AtPrime (IsLocalRing.maximalIdeal A))
        e.symm.injective
    have h5 : IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧ IsIntegrallyClosed A ∧
        ringKrullDim A = 1 := ⟨inferInstance, inferInstance, inferInstance, hIC, hdim⟩
    exact ((isDiscreteValuationRing_tfae A).out 5 1).mp h5
  · rintro ⟨hdom, hDVR⟩
    have h5 : IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧ IsIntegrallyClosed A ∧
        ringKrullDim A = 1 :=
      ((isDiscreteValuationRing_tfae A).out 1 5).mp
        (show ∃ _ : IsDomain A, IsDiscreteValuationRing A from ⟨hdom, hDVR⟩)
    exact deltaInvariant_eq_zero_iff_isIntegrallyClosed.mpr h5.2.2.2.1

end Ring
