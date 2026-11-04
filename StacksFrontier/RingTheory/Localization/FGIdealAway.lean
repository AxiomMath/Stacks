module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Descending an equality of localized finitely generated ideals to one inverted element

Two finitely generated ideals `I`, `J` of a commutative ring `A` that become equal in a
localization `A → B` at a submonoid `M` already become equal after inverting a single element
of `M`.  Only finitely many memberships have to be witnessed — one for each generator of `I` and
one for each generator of `J` — and the product of the finitely many denominators appearing in
those witnesses is the element to invert.

This is the step that turns a statement about the local ring at a point of a scheme into a
statement on a standard open neighbourhood of that point; for `M` the complement of a prime `p`
it says that an equality of ideals holding at `p` holds on a Zariski neighbourhood of `p`.

## Main results

* `Stacks.Localization.exists_mem_map_eq_map_localizationAway`: the descent statement above.

## Implementation notes

The localization in the hypothesis is an arbitrary `IsLocalization M B`, while the conclusion is
stated for `Localization.Away s`, the localization at the powers of the chosen element.  The
generators are produced by `Submodule.FG`, which hands back a `Finset`, and the chosen
denominators are turned into a single element by taking the product over that `Finset`; each
individual denominator then divides the product, so its image in `Localization.Away s` is a unit
and may be cancelled.
-/

@[expose] public section

namespace Stacks.Localization

/-- If `I` is spanned by the finset `G` and `I` extends into `J` in a localization at `M`, then
some `m ∈ M` is such that `I` extends into `J` in `A[1/s]` whenever `m ∣ s`. -/
private theorem map_le_map_localizationAway_of_dvd {A : Type*} [CommRing A] (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B] {I J : Ideal A} (G : Finset A)
    (hG : Ideal.span (G : Set A) = I) (h : I.map (algebraMap A B) ≤ J.map (algebraMap A B)) :
    ∃ m ∈ M, ∀ s : A, m ∣ s →
      I.map (algebraMap A (Localization.Away s)) ≤ J.map (algebraMap A (Localization.Away s)) := by
  classical
  have hex : ∀ y ∈ G, ∃ m ∈ M, m * y ∈ J := fun y hy =>
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M (S := B) J y).mp
      (h (Ideal.mem_map_of_mem _ (hG ▸ Ideal.subset_span hy)))
  choose! f hfM hfJ using hex
  refine ⟨∏ y ∈ G, f y, Submonoid.prod_mem _ fun y hy => hfM y hy, fun s hs => ?_⟩
  rw [← hG, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨y, hy, rfl⟩
  have hu : IsUnit (algebraMap A (Localization.Away s) (f y)) :=
    isUnit_of_dvd_unit (map_dvd _ ((Finset.dvd_prod_of_mem _ hy).trans hs))
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s)
  refine (Ideal.unit_mul_mem_iff_mem _ hu).mp ?_
  rw [← map_mul]
  exact Ideal.mem_map_of_mem _ (hfJ y hy)

/-- **An equality of finitely generated ideals that holds in a localization holds after
inverting one element of the submonoid.**  If `I` and `J` are finitely generated ideals of `A`
whose extensions to a localization `B` of `A` at a submonoid `M` agree, then there is `s ∈ M`
such that the extensions of `I` and `J` to `A[1/s]` already agree. -/
theorem exists_mem_map_eq_map_localizationAway {A : Type*} [CommRing A] (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra A B] [IsLocalization M B] {I J : Ideal A}
    (hI : I.FG) (hJ : J.FG)
    (h : I.map (algebraMap A B) = J.map (algebraMap A B)) :
    ∃ s ∈ M, I.map (algebraMap A (Localization.Away s))
      = J.map (algebraMap A (Localization.Away s)) := by
  classical
  obtain ⟨GI, hGI⟩ := hI
  obtain ⟨GJ, hGJ⟩ := hJ
  obtain ⟨m₁, hm₁, h₁⟩ := map_le_map_localizationAway_of_dvd M B GI hGI h.le
  obtain ⟨m₂, hm₂, h₂⟩ := map_le_map_localizationAway_of_dvd M B GJ hGJ h.ge
  exact ⟨m₁ * m₂, M.mul_mem hm₁ hm₂, le_antisymm (h₁ _ (dvd_mul_right _ _))
    (h₂ _ (dvd_mul_left _ _))⟩

end Stacks.Localization

end
