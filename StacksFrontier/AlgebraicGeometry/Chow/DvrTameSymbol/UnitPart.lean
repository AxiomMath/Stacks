module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# The unit part of a nonzerodivisor in a discrete valuation ring

Let `A` be a discrete valuation ring and `ϖ` a uniformizer. Every nonzero `a ∈ A` is `u ϖ ^ n` for
a unique unit `u` and a unique `n : ℕ`, and that `n` is the order of vanishing
`length_A (A / aA)`, which is Mathlib's `Ring.ord A a`.

This file records the decomposition as two functions on the monoid `nonZeroDivisors A`:
`Stacks.Chow.dvrOrd` for the exponent and `Stacks.Chow.dvrUnitPart` for the unit. The exponent is
additive, the unit is multiplicative, and the pair is determined by any presentation
`a = u ϖ ^ n`.

## Main definitions

* `Stacks.Chow.dvrOrd` — `length_A (A / aA)`, as a natural number.
* `Stacks.Chow.dvrUnitPart` — the unit `u` with `a = u ϖ ^ dvrOrd a`.

## Main results

* `Stacks.Chow.dvrOrd_eq_of_eq_unit_mul_pow` and
  `Stacks.Chow.dvrUnitPart_eq_of_eq_unit_mul_pow` — the decomposition is unique.
* `Stacks.Chow.dvrOrd_mul` and `Stacks.Chow.dvrUnitPart_mul` — it is multiplicative.
* `Stacks.Chow.residue_eq_zero_of_irreducible` and
  `Stacks.Chow.residue_eq_zero_of_dvrOrd_ne_zero` — a uniformizer, and more generally anything of
  positive order of vanishing, has vanishing residue, while
  `Stacks.Chow.isUnit_of_residue_ne_zero` recognizes a unit from a nonzero residue.

## References

* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

universe u

namespace Stacks.Chow

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- The order of vanishing of a nonzerodivisor of a discrete valuation ring, as a natural number:
`dvrOrd a = length_A (A / aA)`, which is the exponent of a uniformizer in `a`. -/
def dvrOrd (a : nonZeroDivisors A) : ℕ := (Ring.ord A (a : A)).toNat

/-- `Ring.ord A a` is the natural number `dvrOrd a`, viewed in `ℕ∞`. -/
theorem ord_eq_dvrOrd (a : nonZeroDivisors A) : Ring.ord A (a : A) = dvrOrd a :=
  (ENat.natCast_toNat (Ring.ord_ne_top a.2)).symm

/-- The order of vanishing is additive: `dvrOrd (a * b) = dvrOrd a + dvrOrd b`. -/
theorem dvrOrd_mul (a b : nonZeroDivisors A) : dvrOrd (a * b) = dvrOrd a + dvrOrd b := by
  rw [dvrOrd, Submonoid.coe_mul, Ring.ord_mul A b.2]
  exact ENat.toNat_add (Ring.ord_ne_top a.2) (Ring.ord_ne_top b.2)

/-- For a uniformizer `ϖ` and a unit `u`, the order of vanishing of `u ϖ ^ n` is `n`. -/
theorem ord_unit_mul_pow {ϖ : A} (hϖ : Irreducible ϖ) (u : Aˣ) (n : ℕ) :
    Ring.ord A ((u : A) * ϖ ^ n) = (n : ℕ∞) := by
  rw [Ring.ord_mul_of_isUnit_left u.isUnit,
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ,
    nsmul_one]

/-- If `a = u ϖ ^ n` with `u` a unit and `ϖ` a uniformizer, then `dvrOrd a = n`. -/
theorem dvrOrd_eq_of_eq_unit_mul_pow {ϖ : A} (hϖ : Irreducible ϖ) {a : nonZeroDivisors A}
    {u : Aˣ} {n : ℕ} (ha : (a : A) = (u : A) * ϖ ^ n) : dvrOrd a = n := by
  rw [dvrOrd, ha, ord_unit_mul_pow hϖ, ENat.toNat_natCast]

/-- Every nonzerodivisor of a discrete valuation ring is a unit times the power of a uniformizer
whose exponent is its order of vanishing. -/
theorem exists_unit_mul_pow_dvrOrd {ϖ : A} (hϖ : Irreducible ϖ) (a : nonZeroDivisors A) :
    ∃ u : Aˣ, (a : A) = (u : A) * ϖ ^ dvrOrd a := by
  obtain ⟨n, u, hn⟩ :=
    eq_unit_mul_pow_irreducible (mem_nonZeroDivisors_iff_ne_zero.mp a.2) hϖ
  exact ⟨u, by rw [dvrOrd_eq_of_eq_unit_mul_pow hϖ hn, hn]⟩

/-- The unit part of a nonzerodivisor of a discrete valuation ring with respect to a uniformizer
`ϖ`: the unit `u` with `a = u ϖ ^ dvrOrd a`. -/
def dvrUnitPart {ϖ : A} (hϖ : Irreducible ϖ) (a : nonZeroDivisors A) : Aˣ :=
  (exists_unit_mul_pow_dvrOrd hϖ a).choose

/-- A nonzerodivisor `a` equals `dvrUnitPart hϖ a * ϖ ^ dvrOrd a`. -/
theorem dvrUnitPart_spec {ϖ : A} (hϖ : Irreducible ϖ) (a : nonZeroDivisors A) :
    (a : A) = (dvrUnitPart hϖ a : A) * ϖ ^ dvrOrd a :=
  (exists_unit_mul_pow_dvrOrd hϖ a).choose_spec

/-- If `a = u ϖ ^ n` with `u` a unit and `ϖ` a uniformizer, then the unit part of `a` is `u`. -/
theorem dvrUnitPart_eq_of_eq_unit_mul_pow {ϖ : A} (hϖ : Irreducible ϖ) {a : nonZeroDivisors A}
    {u : Aˣ} {n : ℕ} (ha : (a : A) = (u : A) * ϖ ^ n) : dvrUnitPart hϖ a = u :=
  unit_mul_pow_congr_unit hϖ _ _ (dvrOrd a) n ((dvrUnitPart_spec hϖ a).symm.trans ha)

/-- The unit part is multiplicative: the unit part of `a * b` is the product of those of `a` and
`b`. -/
theorem dvrUnitPart_mul {ϖ : A} (hϖ : Irreducible ϖ) (a b : nonZeroDivisors A) :
    dvrUnitPart hϖ (a * b) = dvrUnitPart hϖ a * dvrUnitPart hϖ b := by
  refine dvrUnitPart_eq_of_eq_unit_mul_pow hϖ (n := dvrOrd a + dvrOrd b) ?_
  rw [Submonoid.coe_mul, dvrUnitPart_spec hϖ a, dvrUnitPart_spec hϖ b, Units.val_mul, pow_add]
  ring

/-- A nonzerodivisor that is a unit has order of vanishing zero. -/
theorem dvrOrd_eq_zero_of_coe_eq_unit {ϖ : A} (hϖ : Irreducible ϖ) {a : nonZeroDivisors A}
    {u : Aˣ} (ha : (a : A) = (u : A)) : dvrOrd a = 0 :=
  dvrOrd_eq_of_eq_unit_mul_pow hϖ (n := 0) (by simpa using ha)

/-- The unit part of a nonzerodivisor that is the unit `u` is `u`. -/
theorem dvrUnitPart_of_coe_eq_unit {ϖ : A} (hϖ : Irreducible ϖ) {a : nonZeroDivisors A}
    {u : Aˣ} (ha : (a : A) = (u : A)) : dvrUnitPart hϖ a = u :=
  dvrUnitPart_eq_of_eq_unit_mul_pow hϖ (n := 0) (by simpa using ha)

/-- The residue of a uniformizer vanishes. -/
theorem residue_eq_zero_of_irreducible {ϖ : A} (hϖ : Irreducible ϖ) : residue A ϖ = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ)

/-- An element of a discrete valuation ring whose residue is nonzero is a unit. -/
theorem isUnit_of_residue_ne_zero {a : A} (ha : residue A a ≠ 0) : IsUnit a :=
  notMem_maximalIdeal.mp fun h ↦ ha (Ideal.Quotient.eq_zero_iff_mem.mpr h)

/-- A nonzerodivisor of positive order of vanishing has vanishing residue. -/
theorem residue_eq_zero_of_dvrOrd_ne_zero {ϖ : A} (hϖ : Irreducible ϖ) {a : nonZeroDivisors A}
    (ha : dvrOrd a ≠ 0) : residue A (a : A) = 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero ha
  rw [dvrUnitPart_spec hϖ a, hn]
  simp [residue_eq_zero_of_irreducible hϖ]

end Stacks.Chow

end
