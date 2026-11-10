module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.ReducedBranchSpecialFiber

/-!
# Abhyankar's lemma: away localizations that are fields

Part of the namespace `ReducedTensorLocalization`: idempotents of a localization away from an
element, and the criterion that such an away localization is a field when it is Artinian with
only trivial idempotents.

## References

* [The Stacks Project, Tag 09EQ](https://stacks.math.columbia.edu/tag/09EQ)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe uA uB uK uL uK₁ uL₁ uA₁ uB₁

open scoped TensorProduct

noncomputable section

namespace ReducedTensorLocalization

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem local_power_idempotent_numerator
    (R : Type*) [CommRing R] [IsLocalRing R]
    (π : R) (hreg : π ∈ nonZeroDivisors R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span {π}) :
    ∀ (n : ℕ) (a : R), a * a = a * π ^ n → a = 0 ∨ a = π ^ n := by
  intro n
  induction n with
  | zero =>
      intro a ha
      simp only [pow_zero, mul_one] at ha ⊢
      have hzero : a * (1 - a) = 0 := by
        calc
          a * (1 - a) = a - a * a := by ring
          _ = 0 := by rw [ha, sub_self]
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
      · right
        exact (sub_eq_zero.mp ((IsUnit.mul_left_eq_zero hu).mp
          (by simpa only [mul_comm] using hzero))).symm
      · left
        exact (IsUnit.mul_left_eq_zero hu).mp hzero
  | succ n ih =>
      intro a ha
      by_cases hunit : IsUnit a
      · right
        have hz : a * (a - π ^ (n + 1)) = 0 := by
          calc
            a * (a - π ^ (n + 1)) = a * a - a * π ^ (n + 1) := by ring
            _ = 0 := by rw [ha, sub_self]
        exact sub_eq_zero.mp ((IsUnit.mul_left_eq_zero hunit).mp
          (by simpa only [mul_comm] using hz))
      · have hmem : a ∈ IsLocalRing.maximalIdeal R := by
          simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hunit
        have hdiv : π ∣ a := by
          rwa [hmax, Ideal.mem_span_singleton] at hmem
        obtain ⟨b, hb⟩ := hdiv
        have hr : IsRegular (π ^ 2) :=
          (isRegular_iff_mem_nonZeroDivisors).mpr (pow_mem hreg 2)
        have hbEq : b * b = b * π ^ n := by
          apply sub_eq_zero.mp
          apply (isRegular_iff_eq_zero_of_mul.mp hr).1
          calc
            π ^ 2 * (b * b - b * π ^ n) = a * a - a * π ^ (n + 1) := by
              rw [hb]
              ring
            _ = 0 := by rw [ha, sub_self]
        rcases ih b hbEq with hb0 | hbpow
        · left
          rw [hb, hb0, mul_zero]
        · right
          rw [hb, hbpow, pow_succ]
          ring

/-- The map to the localization away from a non-zero-divisor is injective. -/
private theorem algebraMap_away_injective
    (R : Type*) [CommRing R] (π : R) (hreg : π ∈ nonZeroDivisors R) :
    Function.Injective (algebraMap R (Localization.Away π)) :=
  IsLocalization.injective (Localization.Away π) ((Submonoid.powers_le).mpr hreg)

private theorem away_idempotent_eq_zero_or_one
    (R : Type*) [CommRing R] [IsLocalRing R]
    (π : R) (hreg : π ∈ nonZeroDivisors R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (e : Localization.Away π) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have hinj := algebraMap_away_injective R π hreg
  obtain ⟨a, s, hs⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers π) e
  obtain ⟨n, hn⟩ := s.property
  have hmap : algebraMap R (Localization.Away π) a =
      e * algebraMap R (Localization.Away π) (π ^ n) := by
    have hspec := IsLocalization.mk'_spec (Localization.Away π) a s
    rw [hs] at hspec
    simpa only [← hn] using hspec.symm
  have hnum : a * a = a * π ^ n := by
    apply hinj
    simp only [map_mul]
    calc
      algebraMap R (Localization.Away π) a *
          algebraMap R (Localization.Away π) a =
        (e * algebraMap R (Localization.Away π) (π ^ n)) *
          (e * algebraMap R (Localization.Away π) (π ^ n)) := by rw [hmap]
      _ = (e * e) * (algebraMap R (Localization.Away π) (π ^ n) *
          algebraMap R (Localization.Away π) (π ^ n)) := by ring
      _ = e * (algebraMap R (Localization.Away π) (π ^ n) *
          algebraMap R (Localization.Away π) (π ^ n)) := by rw [he]
      _ = algebraMap R (Localization.Away π) a *
          algebraMap R (Localization.Away π) (π ^ n) := by rw [hmap]; ring
  rcases local_power_idempotent_numerator R π hreg hmax n a hnum with ha | ha
  · left
    have hezero : IsLocalization.mk' (Localization.Away π) a s = 0 := by
      rw [ha]
      exact IsLocalization.mk'_zero s
    simpa only [hs] using hezero
  · right
    have heone : IsLocalization.mk' (Localization.Away π) a s = 1 := by
      rw [ha]
      simpa only [hn] using IsLocalization.mk'_self' (Localization.Away π) (x := s)
    simpa only [hs] using heone

private theorem artinian_local_of_trivial_idempotents
    (W : Type*) [CommRing W] [Nontrivial W] [IsArtinianRing W]
    (hid : ∀ e : W, IsIdempotentElem e → e = 0 ∨ e = 1) : IsLocalRing W := by
  classical
  obtain ⟨p, hp⟩ := Ideal.exists_maximal W
  let : p.IsPrime := hp.isPrime
  refine IsLocalRing.of_unique_max_ideal ⟨p, hp, ?_⟩
  intro q hq
  by_contra hne
  obtain ⟨e, hnotp, he, hother⟩ :=
    IsArtinianRing.exists_notMem_forall_mem_of_ne p
  rcases hid e he with hzero | hone
  · exact hnotp (hzero ▸ p.zero_mem)
  · have hmem : e ∈ q := hother q hq.isPrime hne
    exact hq.ne_top (q.eq_top_iff_one.mpr (hone ▸ hmem))

theorem away_field_of_artinian
    (R : Type*) [CommRing R] [IsLocalRing R]
    (π : R) (hreg : π ∈ nonZeroDivisors R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span {π})
    [IsArtinianRing (Localization.Away π)]
    [IsReduced (Localization.Away π)] :
    IsField (Localization.Away π) := by
  have hinj := algebraMap_away_injective R π hreg
  have : Nontrivial (Localization.Away π) :=
    nontrivial_of_ne 0 1 (by
      intro heq
      have hr : (0 : R) = 1 := hinj (by simpa using heq)
      exact zero_ne_one hr)
  let : IsLocalRing (Localization.Away π) :=
    artinian_local_of_trivial_idempotents _
      (away_idempotent_eq_zero_or_one R π hreg hmax)
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing _

end ReducedTensorLocalization

end

end

end IsDiscreteValuationRing
