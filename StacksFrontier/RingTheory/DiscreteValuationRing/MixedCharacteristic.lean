module

public import Mathlib.Algebra.CharP.MixedCharZero
public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import StacksCore.Tactic.StacksAttribute

/-!
# Mixed characteristic and the absolute ramification index

A discrete valuation ring has mixed characteristic `(0, p)` when its residue field has
characteristic `p > 0` and its fraction field has characteristic zero. Such a ring is canonically
an algebra over `ℤ_(p)`, and its absolute ramification index is the ramification index of this
extension.

All declarations below live in the `IsDiscreteValuationRing` namespace.

## Main definitions

* `HasMixedCharacteristic`: mixed characteristic `(0, p)` for a discrete valuation ring.
* `integerLocalization`: the ring `ℤ_(p)` determined by a mixed-characteristic witness.
* `mixedCharacteristicRingHom`: the canonical map `ℤ_(p) → A`.
* `absoluteRamificationIndex`: the ramification index of this canonical extension.

## Main results

* `hasMixedCharacteristic_iff_mixedCharZero_and_integerLocalization_extension`: relates the
  residue-field definition to `MixedCharZero` and records the properties of the canonical DVR
  extension.

## Implementation notes

The parameter `p` is prime because it is the positive characteristic of a field. This supplies the
prime ideal needed for `Localization.AtPrime (Ideal.span {(p : ℤ)})`. The canonical map is obtained
from the universal property of localization.

## References

* [Stacks Project, Tag 09EK](https://stacks.math.columbia.edu/tag/09EK)
-/

@[expose] public section

namespace IsDiscreteValuationRing

/-- A discrete valuation ring has mixed characteristic `(0, p)` if `p` is positive, its residue
field has characteristic `p`, and its fraction field has characteristic zero. -/
@[stacks 09EK]
abbrev HasMixedCharacteristic (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (p : ℕ) : Prop :=
  0 < p ∧ CharP (IsLocalRing.ResidueField A) p ∧ CharZero (FractionRing A)

/-- The localization `ℤ_(p)` associated to a mixed-characteristic discrete valuation ring. -/
@[stacks 09EK]
noncomputable abbrev integerLocalization (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {p : ℕ} (h : HasMixedCharacteristic A p) : Type := by
  letI : CharP (IsLocalRing.ResidueField A) p := h.2.1
  letI : Fact (Nat.Prime p) := ⟨(CharP.char_is_prime_or_zero
    (IsLocalRing.ResidueField A) p).resolve_right (Nat.ne_of_gt h.1)⟩
  exact Localization.AtPrime (Ideal.span {(p : ℤ)})

/-- The canonical map `ℤ_(p) → A` attached to a mixed-characteristic discrete valuation ring. -/
@[stacks 09EK]
noncomputable def mixedCharacteristicRingHom (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {p : ℕ} (h : HasMixedCharacteristic A p) :
    integerLocalization A h →+* A := by
  letI : CharP (IsLocalRing.ResidueField A) p := h.2.1
  letI : Fact (Nat.Prime p) := ⟨(CharP.char_is_prime_or_zero
    (IsLocalRing.ResidueField A) p).resolve_right (Nat.ne_of_gt h.1)⟩
  apply IsLocalization.lift (M := (Ideal.span {(p : ℤ)}).primeCompl)
    (S := Localization.AtPrime (Ideal.span {(p : ℤ)})) (P := A) (g := algebraMap ℤ A)
  intro y
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hy
  apply y.2
  have heq : (IsLocalRing.maximalIdeal A).under ℤ = Ideal.span {(p : ℤ)} := by
    ext x
    change algebraMap ℤ A x ∈ IsLocalRing.maximalIdeal A ↔ _
    rw [← IsLocalRing.residue_eq_zero_iff]
    change algebraMap ℤ (IsLocalRing.ResidueField A) x = 0 ↔ _
    rw [← RingHom.mem_ker]
    exact SetLike.ext_iff.mp
      (CharP.ker_intAlgebraMap_eq_span (R := IsLocalRing.ResidueField A) p) x
  have hy' : (y : ℤ) ∈ (IsLocalRing.maximalIdeal A).under ℤ := hy
  exact (SetLike.ext_iff.mp heq (y : ℤ)).mp hy'

/-- The absolute ramification index of a mixed-characteristic discrete valuation ring, namely the
ramification index of its canonical extension `ℤ_(p) → A`. -/
@[stacks 09EK]
noncomputable def absoluteRamificationIndex (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {p : ℕ} (h : HasMixedCharacteristic A p) : ℕ := by
  letI : Algebra (integerLocalization A h) A := (mixedCharacteristicRingHom A h).toAlgebra
  exact (IsLocalRing.maximalIdeal A).ramificationIdx (integerLocalization A h)

/-- For a discrete valuation ring, the residue-field formulation of mixed characteristic agrees
with Mathlib's `MixedCharZero`; moreover, the maximal ideal lies over `(p)` and the canonical map
from `ℤ_(p)` is an injective local homomorphism whose source is a discrete valuation ring. -/
@[stacks 09EK]
theorem hasMixedCharacteristic_iff_mixedCharZero_and_integerLocalization_extension
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (p : ℕ) :
    (HasMixedCharacteristic A p ↔
      0 < p ∧ CharP (IsLocalRing.ResidueField A) p ∧ MixedCharZero A p) ∧
      ∀ h : HasMixedCharacteristic A p,
        (IsLocalRing.maximalIdeal A).under ℤ = Ideal.span {(p : ℤ)} ∧
          Function.Injective (mixedCharacteristicRingHom A h) ∧
          IsLocalHom (mixedCharacteristicRingHom A h) ∧
          IsDiscreteValuationRing (integerLocalization A h) := by
  constructor
  · constructor
    · intro h
      have := h.2.2
      have : CharZero A := (algebraMap A (FractionRing A)).charZero
      exact ⟨h.1, h.2.1, ⟨⟨IsLocalRing.maximalIdeal A,
        (IsLocalRing.maximalIdeal.isMaximal A).ne_top, h.2.1⟩⟩⟩
    · rintro ⟨hp, hres, hmixed⟩
      have : CharZero A := hmixed.toCharZero
      exact ⟨hp, hres, inferInstance⟩
  · intro h
    have : CharP (IsLocalRing.ResidueField A) p := h.2.1
    have : Fact (Nat.Prime p) := ⟨(CharP.char_is_prime_or_zero
      (IsLocalRing.ResidueField A) p).resolve_right (Nat.ne_of_gt h.1)⟩
    have heq : (IsLocalRing.maximalIdeal A).under ℤ = Ideal.span {(p : ℤ)} := by
      ext x
      change algebraMap ℤ A x ∈ IsLocalRing.maximalIdeal A ↔ _
      rw [← IsLocalRing.residue_eq_zero_iff]
      change algebraMap ℤ (IsLocalRing.ResidueField A) x = 0 ↔ _
      rw [← RingHom.mem_ker]
      exact SetLike.ext_iff.mp
        (CharP.ker_intAlgebraMap_eq_span (R := IsLocalRing.ResidueField A) p) x
    refine ⟨heq, ?_, ?_, ?_⟩
    · have : CharZero (FractionRing A) := h.2.2
      have : CharZero A := (algebraMap A (FractionRing A)).charZero
      change Function.Injective (IsLocalization.lift _)
      rw [IsLocalization.lift_injective_iff]
      refine fun x y => ⟨fun e => ?_, fun e =>
        congr_arg (algebraMap ℤ (integerLocalization A h)) (Int.cast_injective e)⟩
      simpa only [mixedCharacteristicRingHom, IsLocalization.lift_eq] using
        congr_arg (mixedCharacteristicRingHom A h) e
    · refine ⟨fun x hx => ?_⟩
      rcases IsLocalization.exists_mk'_eq (Ideal.span {(p : ℤ)}).primeCompl x with ⟨r, s, rfl⟩
      rw [IsLocalization.AtPrime.isUnit_mk'_iff]
      intro hr
      rw [mixedCharacteristicRingHom, IsLocalization.lift_mk', IsUnit.mul_iff] at hx
      exact IsLocalRing.notMem_maximalIdeal.mpr hx.1 ((SetLike.ext_iff.mp heq r).mpr hr)
    · change IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(p : ℤ)}))
      exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        (P := Ideal.span {(p : ℤ)}) ℤ
        (Ideal.span_singleton_eq_bot.not.mpr
          (Int.ofNat_ne_zero.mpr h.1.ne'))
        (Localization.AtPrime (Ideal.span {(p : ℤ)}))

end IsDiscreteValuationRing
