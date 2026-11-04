module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Localizations of valuation rings

A valuation ring is a domain whose elements are totally ordered by divisibility.  Both
conditions survive localization and isomorphism: a localization of a valuation ring which is a
domain is again a valuation ring, because every element of the localization is an element of
the ring up to a unit, and a ring isomorphic to a valuation ring is one.

## Main results

* `ValuationRing.of_isLocalization`: a localization of a valuation ring, if it is a domain, is a
  valuation ring.
* `ValuationRing.of_ringEquiv`: a domain isomorphic to a valuation ring is a valuation ring.
-/

@[expose] public section

namespace ValuationRing

/-- **A localization of a valuation ring is a valuation ring.**  Writing two elements of the
localization as fractions `x / s` and `y / t`, a divisibility `x ∣ y` or `y ∣ x` in the ring gives
the corresponding divisibility between the fractions, the denominators being units. -/
theorem of_isLocalization {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    {S : Type*} [CommRing S] [IsDomain S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] : ValuationRing S where
  cond' a b := by
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective M a
    obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalization.mk'_surjective M b
    obtain ⟨c, h | h⟩ := ValuationRing.cond x y
    · refine ⟨IsLocalization.mk' S (c * s) t, Or.inl ?_⟩
      rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq, ← h]
      congr 1
      simp only [Submonoid.coe_mul]
      ring
    · refine ⟨IsLocalization.mk' S (c * t) s, Or.inr ?_⟩
      rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq, ← h]
      congr 1
      simp only [Submonoid.coe_mul]
      ring

/-- **A domain isomorphic to a valuation ring is a valuation ring.** -/
theorem of_ringEquiv {A : Type*} [CommRing A] [IsDomain A] {B : Type*} [CommRing B] [IsDomain B]
    [ValuationRing B] (e : A ≃+* B) : ValuationRing A where
  cond' a b := by
    obtain ⟨c, h | h⟩ := ValuationRing.cond (e a) (e b)
    · exact ⟨e.symm c, Or.inl (e.injective (by rw [map_mul, e.apply_symm_apply, h]))⟩
    · exact ⟨e.symm c, Or.inr (e.injective (by rw [map_mul, e.apply_symm_apply, h]))⟩

end ValuationRing

end
