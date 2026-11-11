module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Discrete valuation rings in the sense of their value group

Stacks (Definition 00IE (3)) calls a valuation ring `A` a *discrete valuation ring* when its
value group `Γ = Kˣ/Aˣ` is isomorphic to `ℤ`. Mathlib's `IsDiscreteValuationRing` is a local
principal ideal domain which is not a field. This file proves that the two notions agree for a
valuation ring.

The value group of `A` is `ValuationRing.ValueGroup A K`, the quotient of `K` by the action of
`Aˣ`; it is a group with zero, and its units are `Γ = Kˣ/Aˣ`.

## Main results

* `ValuationRing.valuation_eq_one_iff`: `v x = 1` exactly when `x` is the image of a unit of `A`.
* `ValuationRing.isDiscreteValuationRing_iff_nonempty_mulEquiv_int`: a valuation ring is a
  discrete valuation ring if and only if its value group is isomorphic to `ℤ`.
-/

@[expose] public section

namespace ValuationRing

variable (A : Type*) [CommRing A] [IsDomain A] [ValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- The valuation of a valuation ring takes the value `1` exactly on the units of the ring. -/
theorem valuation_eq_one_iff (x : K) :
    valuation A K x = 1 ↔ ∃ u : Aˣ, algebraMap A K u = x := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := Quotient.exact' h
    exact ⟨u, by simpa [Units.smul_def, Algebra.smul_def] using hu⟩
  · rintro ⟨u, rfl⟩
    exact Quotient.sound' ⟨u, by simp [Units.smul_def, Algebra.smul_def]⟩

/-- The valuation of an element of a valuation ring is at most `1`. -/
theorem valuation_algebraMap_le_one (a : A) : valuation A K (algebraMap A K a) ≤ 1 :=
  ((valuation A K).mem_integer_iff _).mp ((mem_integer_iff A K _).mpr ⟨a, rfl⟩)

/-- An element of `K` of valuation at most `1` lies in the valuation ring. -/
theorem exists_eq_algebraMap_of_valuation_le_one {x : K} (hx : valuation A K x ≤ 1) :
    ∃ a : A, algebraMap A K a = x :=
  (mem_integer_iff A K x).mp (((valuation A K).mem_integer_iff x).mpr hx)

variable {A K} in
/-- Two nonzero elements of a valuation ring with the same valuation are associated. -/
theorem exists_unit_mul_eq_of_valuation_eq {a b : A} (hb : b ≠ 0)
    (h : valuation A K (algebraMap A K a) = valuation A K (algebraMap A K b)) :
    ∃ u : Aˣ, a = u * b := by
  have hb' : algebraMap A K b ≠ 0 := (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hb))
  have hb'' : valuation A K (algebraMap A K b) ≠ 0 := by simpa using hb'
  obtain ⟨u, hu⟩ := (valuation_eq_one_iff A K (algebraMap A K a / algebraMap A K b)).mp
    (by rw [map_div₀, h, div_self hb''])
  refine ⟨u, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hu, div_mul_cancel₀ _ hb']

/-- **Stacks 00IE (3)**: a valuation ring `A` with fraction field `K` is a discrete valuation
ring (a local principal ideal domain which is not a field) if and only if its value group
`Γ = Kˣ/Aˣ`, here `(ValuationRing.ValueGroup A K)ˣ`, is isomorphic to `ℤ`.

The isomorphism is one of groups. Stacks writes `Γ ≅ ℤ` and remarks that there is then a unique
such isomorphism with `1 ≥ 0`, so any group isomorphism is order preserving up to the sign of
`ℤ`; the proof below works with a generator of `Γ` which is `< 1`. -/
@[stacks 00IE "(3) a valuation ring is a DVR (Mathlib's IsDiscreteValuationRing) iff its value \
group (ValuationRing.ValueGroup A K)ˣ = Kˣ/Aˣ is isomorphic to ℤ (as a group, written \
multiplicatively)."]
theorem isDiscreteValuationRing_iff_nonempty_mulEquiv_int :
    IsDiscreteValuationRing A ↔ Nonempty ((ValueGroup A K)ˣ ≃* Multiplicative ℤ) := by
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hne : ∀ {a : A}, a ≠ 0 → valuation A K (algebraMap A K a) ≠ 0 := fun ha ↦ by
    simpa using (map_ne_zero_iff _ hinj).mpr ha
  constructor
  · intro hA
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    set g : (ValueGroup A K)ˣ := Units.mk0 _ (hne hϖ.ne_zero) with hg
    have hg1 : g ≠ 1 := by
      intro h
      have h' : valuation A K (algebraMap A K ϖ) = 1 := by
        simpa [hg] using congrArg Units.val h
      obtain ⟨u, hu⟩ := (valuation_eq_one_iff A K _).mp h'
      exact hϖ.not_isUnit (hinj hu ▸ u.isUnit)
    have hpow : ∀ a : A, a ≠ 0 →
        ∃ n : ℕ, valuation A K (algebraMap A K a) = (g : ValueGroup A K) ^ n := by
      intro a ha
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
      refine ⟨n, ?_⟩
      rw [map_mul, map_mul, map_pow, map_pow,
        (valuation_eq_one_iff A K _).mpr ⟨u, rfl⟩, one_mul, hg, Units.val_mk0]
    refine ⟨(MulEquiv.ofBijective (zpowersHom (ValueGroup A K)ˣ g) ⟨?_, ?_⟩).symm⟩
    · intro a b hab
      exact Multiplicative.toAdd.injective
        (injective_zpow_iff_not_isOfFinOrder.mpr (fun h ↦ hg1 h.eq_one') hab)
    · intro y
      obtain ⟨x, hx⟩ := Quotient.exists_rep (y : ValueGroup A K)
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact y.ne_zero (by rw [← hx]; simp; rfl)
      obtain ⟨m, hm⟩ := hpow a ha0
      obtain ⟨k, hk⟩ := hpow b hb0
      refine ⟨Multiplicative.ofAdd ((m : ℤ) - k), Units.ext ?_⟩
      have hy : (y : ValueGroup A K) =
          valuation A K (algebraMap A K a / algebraMap A K b) := hx.symm
      rw [hy, map_div₀, hm, hk, zpowersHom_apply, toAdd_ofAdd, Units.val_zpow_eq_zpow_val,
        zpow_sub₀ g.ne_zero, zpow_natCast, zpow_natCast]
  · rintro ⟨e⟩
    set t := e.symm (Multiplicative.ofAdd 1) with ht
    have ht1 : t ≠ 1 := by
      intro h
      have := congrArg e h
      rw [ht, MulEquiv.apply_symm_apply, map_one e] at this
      exact one_ne_zero (Multiplicative.ofAdd.injective this)
    have htgen : ∀ y, ∃ n : ℤ, y = t ^ n := fun y ↦
      ⟨Multiplicative.toAdd (e y), by
        rw [ht, ← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd,
          MulEquiv.symm_apply_apply]⟩
    -- a generator `g < 1` of the value group
    obtain ⟨g, hg1, hggen⟩ : ∃ g : (ValueGroup A K)ˣ, g < 1 ∧ ∀ y, ∃ n : ℤ, y = g ^ n := by
      rcases lt_or_gt_of_ne ht1 with h | h
      · exact ⟨t, h, htgen⟩
      · refine ⟨t⁻¹, inv_lt_one'.mpr h, fun y ↦ ?_⟩
        obtain ⟨n, rfl⟩ := htgen y
        exact ⟨-n, by rw [zpow_neg, inv_zpow, inv_inv]⟩
    -- the elements of value at most `1` are the nonnegative powers of `g`
    have hle : ∀ y, y ≤ 1 → ∃ n : ℕ, y = g ^ n := by
      intro y hy
      obtain ⟨n, rfl⟩ := hggen y
      rcases n with n | n
      · exact ⟨n, by simp⟩
      · refine absurd hy (not_le.mpr ?_)
        rw [zpow_negSucc]
        exact one_lt_inv'.mpr (pow_lt_one' hg1 (Nat.succ_ne_zero n))
    obtain ⟨x₀, hx₀⟩ := Quotient.exists_rep (g : ValueGroup A K)
    have hvx₀ : valuation A K x₀ = g := hx₀
    obtain ⟨p, rfl⟩ := exists_eq_algebraMap_of_valuation_le_one A K
      (by rw [hvx₀]; exact_mod_cast hg1.le)
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact g.ne_zero (by rw [← hvx₀]; simp)
    have hpunit : ¬IsUnit p := by
      rintro ⟨u, rfl⟩
      exact hg1.ne (Units.ext (by rw [← hvx₀, (valuation_eq_one_iff A K _).mpr ⟨u, rfl⟩]; rfl))
    -- every nonzero element of `A` is a unit times a power of `p`
    have hfac : ∀ a : A, a ≠ 0 → ∃ n : ℕ, ∃ u : Aˣ, a = u * p ^ n := by
      intro a ha
      obtain ⟨n, hn⟩ := hle (Units.mk0 _ (hne ha))
        (by exact_mod_cast valuation_algebraMap_le_one A K a)
      refine ⟨n, exists_unit_mul_eq_of_valuation_eq (K := K) (pow_ne_zero n hp0) ?_⟩
      rw [map_pow, map_pow, hvx₀, ← Units.val_pow_eq_pow_val, ← hn, Units.val_mk0]
    have hmax : IsLocalRing.maximalIdeal A = Ideal.span {p} := by
      refine le_antisymm (fun a ha ↦ ?_) ((Ideal.span_singleton_le_iff_mem _).mpr hpunit)
      by_cases ha0 : a = 0
      · rw [ha0]; exact Ideal.zero_mem _
      obtain ⟨n, u, rfl⟩ := hfac a ha0
      rcases n with _ | n
      · exact absurd ha (by simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff])
      · exact Ideal.mem_span_singleton.mpr
          (Dvd.dvd.mul_left (dvd_pow_self p (Nat.succ_ne_zero n)) _)
    exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
      ⟨p, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal p hp0 hmax, fun {a} ha ↦
        let ⟨n, u, hu⟩ := hfac a ha
        ⟨n, ⟨u, by rw [hu, mul_comm]⟩⟩⟩

end ValuationRing
