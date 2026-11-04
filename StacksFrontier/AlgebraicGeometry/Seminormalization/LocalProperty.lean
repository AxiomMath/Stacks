module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.Seminormalization.Defs

/-!
# Seminormality is a local property of rings

This file proves the seminormal half of
[Stacks, Tag 0EUM](https://stacks.math.columbia.edu/tag/0EUM): seminormality is preserved by
localization away from an element, and descends along a family of such localizations whose
elements generate the unit ideal.

Both halves are shortened by `isSeminormalRing_iff_exists`, which says that the uniqueness
clause of seminormality follows from its existence clause.  So neither half has to transport a
uniqueness statement along a localization map:

* *Preservation.*  Given `x', y'` in a localization `S` of `A` away from `f` with
  `x' ^ 3 = y' ^ 2`, write `x' * f ^ (2 * n) = x` and `y' * f ^ (3 * n) = y` with `x, y` coming
  from `A`.  Then `x ^ 3` and `y ^ 2` have the same image in `S`, hence agree after
  multiplication by a power `f ^ m`; rescaling `x, y` by `f ^ (2 * m)` and `f ^ (3 * m)` makes
  them agree in `A`.  Seminormality of `A` yields a common root `a₀` there, and
  `a₀ / f ^ (n + m)` is the required root in `S`.
* *Descent.*  The elements `f i` generate the unit ideal, so `A` injects into the product of
  the localizations `A_{f i}`; this already gives that `A` is reduced.  A pair `x, y` with
  `x ^ 3 = y ^ 2` has a unique root `a i` in each `A_{f i}`, and the two images of `a i` and
  `a j` in `A_{f i f j}` have the same square and the same cube, so are equal because that
  ring is reduced.  The sheaf condition for the structure sheaf on `Spec A`
  (`Localization.existsUnique_algebraMap_eq_of_span_eq_top`) then glues them to an element of
  `A`, which is a common root because it is one after localizing at each `f i`.

## Main results

* `Stacks.RingTheory.Seminormal.IsSeminormalRing.of_ringEquiv` and
  `Stacks.RingTheory.Seminormal.IsSeminormalRing.ofIsLocalization`: seminormality is invariant
  under ring isomorphism, hence passes between any two localizations at one submonoid.
* `Stacks.RingTheory.Seminormal.IsSeminormalRing.localizationAway`: a localization away from an
  element of a seminormal ring is seminormal.
* `Stacks.RingTheory.Seminormal.isSeminormalRing_of_span_eq_top`: if the elements of a set
  spanning the unit ideal all have seminormal localizations, the ring is seminormal.
* `Stacks.RingTheory.Seminormal.isSeminormalRing_of_span_range_eq_top`: the same, for an
  indexed family.

## Implementation notes

Preservation is stated for an arbitrary ring `S` satisfying `IsLocalization.Away f S`, not just
for `Localization.Away f`, since that is the form in which it is applied to the ring of
sections over a basic open.  Descent is stated for `Localization.Away` because this is the form
of Mathlib's gluing lemma `Localization.existsUnique_algebraMap_eq_of_span_eq_top`; the
spanning family is an arbitrary set, with no finiteness hypothesis, as the gluing lemma
already reduces to a finite subfamily internally.

The universes of `A` and of `S` are unconstrained relative to each other.

Only the seminormal half of Tag 0EUM is proved here.  The absolutely weakly normal half needs
the uniqueness clause of the prime-power condition to be transported along the localization
maps, for which there is no analogue of Costa's observation (see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Seminormalization.Defs`).

## References

* [Stacks Project, Tag 0EUM](https://stacks.math.columbia.edu/tag/0EUM)
-/

@[expose] public section

namespace Stacks.RingTheory.Seminormal

section Away

/-- Seminormality is invariant under ring isomorphism. -/
theorem IsSeminormalRing.of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (hA : IsSeminormalRing A) : IsSeminormalRing B := by
  rw [isSeminormalRing_iff_exists] at hA ⊢
  intro x y hxy
  obtain ⟨a, ha2, ha3⟩ := hA (e.symm x) (e.symm y) (by
    rw [← map_pow, ← map_pow, hxy])
  exact ⟨e a, by rw [← map_pow, ← ha2, e.apply_symm_apply],
    by rw [← map_pow, ← ha3, e.apply_symm_apply]⟩

/-- Seminormality of one localization of `A` at a submonoid transfers to any other. -/
theorem IsSeminormalRing.ofIsLocalization {A S S' : Type*} [CommRing A] [CommRing S]
    [CommRing S'] [Algebra A S] [Algebra A S'] (M : Submonoid A) [IsLocalization M S]
    [IsLocalization M S'] (hS : IsSeminormalRing S) : IsSeminormalRing S' :=
  IsSeminormalRing.of_ringEquiv (IsLocalization.algEquiv M S S').toRingEquiv hS

/-- Raise the exponent in a presentation `z * f ^ i = a` of an element of a localization away
from `f`: the same element is witnessed at any larger exponent by rescaling the numerator. -/
theorem mul_pow_eq_algebraMap_of_le {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (f : A) {z : S} {i : ℕ} {a : A}
    (ha : z * algebraMap A S f ^ i = algebraMap A S a) {m : ℕ} (hm : i ≤ m) :
    z * algebraMap A S f ^ m = algebraMap A S (a * f ^ (m - i)) := by
  rw [map_mul, map_pow, ← ha, mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]

/-- If `z * F ^ (k * N) = d ^ k` with `F` a unit, then `z = (d * F⁻¹ ^ N) ^ k`. -/
private theorem eq_pow_of_mul_pow_eq {S : Type*} [CommRing S] {F : S} (hF : IsUnit F) {z d : S}
    {k N : ℕ} (h : z * F ^ (k * N) = d ^ k) : z = (d * ↑hF.unit⁻¹ ^ N) ^ k := by
  calc z = z * (F * ↑hF.unit⁻¹) ^ (k * N) := by rw [hF.mul_val_inv, one_pow, mul_one]
    _ = z * F ^ (k * N) * (↑hF.unit⁻¹ ^ N) ^ k := by rw [mul_pow, ← pow_mul, mul_comm N k]; ring
    _ = _ := by rw [h, mul_pow]

/-- A localization away from an element of a seminormal ring is seminormal.  This is the
localization half of the seminormal part of
[Stacks, Tag 0EUM](https://stacks.math.columbia.edu/tag/0EUM). -/
theorem IsSeminormalRing.localizationAway {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (f : A) [IsLocalization.Away f S] (hA : IsSeminormalRing A) : IsSeminormalRing S := by
  rw [isSeminormalRing_iff_exists] at hA ⊢
  intro x' y' hxy
  obtain ⟨i, a, ha⟩ := IsLocalization.Away.surj f x'
  obtain ⟨j, b, hb⟩ := IsLocalization.Away.surj f y'
  have hx := mul_pow_eq_algebraMap_of_le f ha (show i ≤ 2 * (i + j) by omega)
  have hy := mul_pow_eq_algebraMap_of_le f hb (show j ≤ 3 * (i + j) by omega)
  set n := i + j with hn
  set x := a * f ^ (2 * n - i) with hxdef
  set y := b * f ^ (3 * n - j) with hydef
  -- `x ^ 3` and `y ^ 2` have the same image in `S`.
  have hcube : algebraMap A S (x ^ 3) = algebraMap A S (y ^ 2) := by
    rw [map_pow, map_pow, ← hx, ← hy, mul_pow, mul_pow, ← pow_mul, ← pow_mul, hxy]
    ring_nf
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq f hcube
  -- after rescaling they agree in `A`.
  have hcube' : (f ^ (2 * m) * x) ^ 3 = (f ^ (3 * m) * y) ^ 2 := by
    calc (f ^ (2 * m) * x) ^ 3 = f ^ (5 * m) * (f ^ m * x ^ 3) := by ring
      _ = f ^ (5 * m) * (f ^ m * y ^ 2) := by rw [hm]
      _ = (f ^ (3 * m) * y) ^ 2 := by ring
  obtain ⟨c, hc2, hc3⟩ := hA _ _ hcube'
  -- transport the root back to `S`.
  have key : ∀ (k : ℕ) (z : S) (w : A), z * algebraMap A S f ^ (k * n) = algebraMap A S w →
      f ^ (k * m) * w = c ^ k → z * algebraMap A S f ^ (k * (n + m)) = algebraMap A S c ^ k := by
    intro k z w hz hc
    rw [mul_add, pow_add, ← mul_assoc, hz, ← map_pow, ← map_mul, ← map_pow, ← hc, mul_comm]
  exact ⟨_, eq_pow_of_mul_pow_eq (IsLocalization.Away.algebraMap_isUnit f) (key 2 x' x hx hc2),
    eq_pow_of_mul_pow_eq (IsLocalization.Away.algebraMap_isUnit f) (key 3 y' y hy hc3)⟩

end Away

section Descent

variable {A : Type*} [CommRing A] {s : Set A}

/-- Two elements of a ring agreeing in every localization away from a member of a spanning set
are equal: this is injectivity of `A → ∏ A_g`. -/
theorem eq_of_forall_localizationAway_eq (hs : Ideal.span s = ⊤) {x y : A}
    (h : ∀ g : s, algebraMap A (Localization.Away (g : A)) x
      = algebraMap A (Localization.Away (g : A)) y) : x = y :=
  Localization.algebraMap_injective_of_span_eq_top s hs
    (funext fun g => by simpa only [Pi.algebraMap_apply] using h g)

/-- If the localizations of `A` away from the members of a spanning set are all reduced, then
`A` is reduced. -/
theorem isReduced_of_span_eq_top (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, IsReduced (Localization.Away (g : A))) : IsReduced A := by
  rw [isReduced_iff_pow_one_lt 2 one_lt_two]
  intro z hz
  refine eq_of_forall_localizationAway_eq hs fun g => ?_
  have : IsNilpotent (algebraMap A (Localization.Away (g : A)) z) :=
    ⟨2, by rw [← map_pow, hz, map_zero]⟩
  rw [(h g).eq_zero _ this, map_zero]

/-- Seminormality descends along a family of localizations away from the members of a set
spanning the unit ideal.  This is the descent half of the seminormal part of
[Stacks, Tag 0EUM](https://stacks.math.columbia.edu/tag/0EUM). -/
theorem isSeminormalRing_of_span_eq_top (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, IsSeminormalRing (Localization.Away (g : A))) : IsSeminormalRing A := by
  have hred : IsReduced A := isReduced_of_span_eq_top hs fun g => IsSeminormalRing.isReduced (h g)
  rw [isSeminormalRing_iff_exists]
  intro x y hxy
  -- the root over each member of the spanning set
  have hroot : ∀ g : s, ∃ a : Localization.Away (g : A),
      algebraMap A (Localization.Away (g : A)) x = a ^ 2 ∧
        algebraMap A (Localization.Away (g : A)) y = a ^ 3 := fun g =>
    (h g _ _ (by rw [← map_pow, ← map_pow, hxy])).exists
  choose a ha using hroot
  -- the roots agree pairwise, because `A_{g g'}` is reduced
  have hagree : ∀ g g' : s, IsLocalization.Away.awayToAwayRight
      (P := Localization.Away ((g : A) * (g' : A))) (g : A) (g' : A) (a g)
      = IsLocalization.Away.awayToAwayLeft (g' : A) (g : A) (a g') := by
    intro g g'
    refine eq_of_sq_eq_of_cube_eq ?_ ?_
    · rw [← map_pow, ← map_pow, ← (ha g).1, ← (ha g').1,
        IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq]
    · rw [← map_pow, ← map_pow, ← (ha g).2, ← (ha g').2,
        IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq]
  obtain ⟨c, hc, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top s hs a hagree
  refine ⟨c, ?_, ?_⟩
  · refine eq_of_forall_localizationAway_eq hs fun g => ?_
    rw [map_pow, hc g]
    exact (ha g).1
  · refine eq_of_forall_localizationAway_eq hs fun g => ?_
    rw [map_pow, hc g]
    exact (ha g).2

/-- Seminormality descends along a family of localizations away from the members of an indexed
family generating the unit ideal. -/
theorem isSeminormalRing_of_span_range_eq_top {ι : Type*} (f : ι → A)
    (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ g : Set.range f, IsSeminormalRing (Localization.Away (g : A))) :
    IsSeminormalRing A :=
  isSeminormalRing_of_span_eq_top hf h

end Descent

end Stacks.RingTheory.Seminormal

end
