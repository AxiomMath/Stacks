module

public import Mathlib.Algebra.Polynomial.Roots

/-! # Roots of polynomials -/

@[expose] public section

namespace Polynomial

open Finset

/-- Over an integral domain, the product `∏ i ∈ s, (X - C i)` divides a polynomial `f`
if and only if every element of `s` is a root of `f`. -/
theorem prod_X_sub_C_dvd_iff {R : Type*} [CommRing R] [IsDomain R] (f : R[X]) (s : Finset R) :
    (∏ i ∈ s, (X - C i)) ∣ f ↔ ∀ x ∈ s, IsRoot f x := by
  obtain rfl | hf0 := eq_or_ne f 0
  · simp
  rw [Finset.prod, Multiset.prod_X_sub_C_dvd_iff_le_roots hf0, Finset.val_le_iff_val_subset]
  simp [Multiset.subset_iff, hf0]

/-- If every element of a finite set `s` is a root of `f`, then `∏ i ∈ s, (X - C i)`
divides `f`. -/
theorem prod_X_sub_C_dvd {R : Type*} [CommRing R] [IsDomain R] {f : R[X]} {s : Finset R}
    (h : ∀ x ∈ s, IsRoot f x) : (∏ i ∈ s, (X - C i)) ∣ f := (prod_X_sub_C_dvd_iff ..).mpr h

/-- A monic polynomial `f` of degree at most `#s` that vanishes on every element of a finite
set `s` factors as `f = ∏ i ∈ s, (X - C i)`. -/
theorem Monic.eq_prod_X_sub_C_of_card {R : Type*} [CommRing R] [IsDomain R] {f : R[X]}
    {s : Finset R} (hfm : f.Monic) (hcard : f.natDegree ≤ s.card) (hroot : ∀ x ∈ s, IsRoot f x) :
    f = ∏ i ∈ s, (X - C i) := by
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_X_sub_C ..) hfm ?_ ?_
  · exact prod_X_sub_C_dvd fun x hx ↦ by simpa using hroot x hx
  · simpa

/-- Indexed variant of `Monic.eq_prod_X_sub_C_of_card`: a monic polynomial `f` of degree at most
`#s` whose roots include `r i` for every `i ∈ s` (with `r` injective on `s`) factors as
`f = ∏ i ∈ s, (X - C (r i))`. -/
theorem Monic.eq_prod_X_sub_C_of_card' {R : Type*} [CommRing R] [IsDomain R] {f : R[X]}
    {ι : Type*} {s : Finset ι} {r : ι → R} (hfm : f.Monic) (hr : Set.InjOn r s)
    (hcard : f.natDegree ≤ s.card) (hroot : ∀ x ∈ s, IsRoot f (r x)) :
    f = ∏ i ∈ s, (X - C (r i)) := by
  classical
  simpa [hr] using hfm.eq_prod_X_sub_C_of_card (s := s.image r) (by simpa [card_image_of_injOn hr])
    (by simpa using hroot)

end Polynomial
