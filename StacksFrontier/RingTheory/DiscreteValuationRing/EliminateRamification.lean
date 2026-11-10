module

public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow

/-!
# Eliminating ramification: congruences for the Kummer polynomial

Let `B` be a discrete valuation ring containing a primitive `p`-th root of unity `ζ`, write
`w = 1 - ζ`, and let `P` be the Kummer polynomial of Stacks 09F2, so that `P` has the shape
`z ^ p - z + ∑_{0 < i < p} a i * z ^ i` with every `a i` in the ideal `(w)`. This file records
the two congruences that drive the elimination-of-ramification argument.

If `w` is associated to `π ^ e₁` for a uniformizer `π` and `π ^ n * P(z)` is integral, then
`P(z)` differs from `z ^ p - z` by an element of the fractional ideal `π ^ (e₁ - n) B`.
Dually, if `ξ₁` and `ξ₂` lie in the fractional ideal `π ^ (-n) B`, then the correction term
`w ^ p * ξ₁ * ξ₂` appearing in the group law lies in `π ^ (-2 n + p e₁) B`, so adding it does
not change `ξ₁ + ξ₂` modulo that fractional ideal.

## Main results

* `IsDiscreteValuationRing.eval_sub_pow_sub_mem_uniformizer_zpow`: the fractional-ideal
  congruence `P(z) ≡ z ^ p - z` modulo `π ^ (e₁ - n) B` for the Kummer polynomial.
* `IsDiscreteValuationRing.add_mul_correction_sModEq`: the finite-level congruence saying that
  the product correction `w ^ p * ξ₁ * ξ₂` vanishes modulo `π ^ (-2 n + p e₁) B`.

## Implementation notes

Membership in the fractional principal ideal `π ^ (e₁ - n) B` is expressed for the first result
by writing the difference as `π ^ (e₁ - n)` times the image of an element of `B` in its fraction
field; for the second it is expressed through `FractionalIdeal.spanSingleton` and `SModEq`. The
second result is stated for an arbitrary domain because the congruence only uses the association
of `w` and `π ^ e₁`, not the discrete valuation ring structure.

## References

* [Stacks Project, Tag 09F6](https://stacks.math.columbia.edu/tag/09F6)
* [Stacks Project, Tag 09F7](https://stacks.math.columbia.edu/tag/09F7)
* [Stacks Project, Tag 09F2](https://stacks.math.columbia.edu/tag/09F2)
-/

@[expose] public section

universe uB uK

namespace IsDiscreteValuationRing

open Polynomial

private lemma valuation_eval₂_eq_pow_of_monic_of_one_lt
    {B : Type uB} {K : Type uK} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (P : B[X]) (hP : P.Monic) (z : K)
    (hz : 1 < (IsDiscreteValuationRing.maximalIdeal B).valuation K z) :
    (IsDiscreteValuationRing.maximalIdeal B).valuation K
        (P.eval₂ (algebraMap B K) z) =
      ((IsDiscreteValuationRing.maximalIdeal B).valuation K z) ^ P.natDegree := by
  let v := (IsDiscreteValuationRing.maximalIdeal B).valuation K
  have hlead : v ((monomial P.natDegree P.leadingCoeff).eval₂
      (algebraMap B K) z) = v z ^ P.natDegree := by
    simp [← C_mul_X_pow_eq_monomial, hP.leadingCoeff, v]
  rw [← hlead]
  nth_rw 1 [Polynomial.as_sum_range P]
  rw [Polynomial.eval₂_finsetSum]
  apply Valuation.map_sum_eq_of_lt v (by simp)
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_range, Nat.lt_add_one_iff,
    Finset.mem_singleton, ← lt_iff_le_and_ne] at hi
  simp only [← C_mul_X_pow_eq_monomial, eval₂_mul, eval₂_C, eval₂_pow,
    eval₂_X, map_mul, map_pow]
  calc
    v (algebraMap B K (P.coeff i)) * v z ^ i
        ≤ 1 * v z ^ i := by
          gcongr
          exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
    _ < 1 * v z ^ P.natDegree := by
      simpa using pow_lt_pow_right₀ hz hi
    _ = v (algebraMap B K (P.leadingCoeff)) * v z ^ P.natDegree := by
      simp [hP.leadingCoeff, v]

private lemma monic_of_shapeProp
    {B : Type uB} [CommRing B] [Nontrivial B] {p : ℕ} [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : B[X]) (hP : shapeProp f P) :
    P.Monic := by
  obtain ⟨a, ha, rfl⟩ := hP
  rw [show X ^ p - X + ∑ i ∈ Finset.Ioo 0 p, C (a i) * X ^ i =
      X ^ p + (-X + ∑ i ∈ Finset.Ioo 0 p, C (a i) * X ^ i) by ring]
  apply (Polynomial.monic_X_pow p).add_of_left
  refine (degree_add_le _ _).trans_lt (max_lt_iff.2 ⟨?_, ?_⟩)
  · rw [degree_neg, degree_X, degree_X_pow]
    exact_mod_cast (Fact.out : p.Prime).one_lt
  · refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 ?_)
    · rw [degree_X_pow]
      exact WithBot.bot_lt_coe p
    · intro i hi
      exact (degree_C_mul_X_pow_le _ _).trans_lt (by
        simpa using (Finset.mem_Ioo.mp hi).2)

private lemma natDegree_of_shapeProp
    {B : Type uB} [CommRing B] [Nontrivial B] {p : ℕ} [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : B[X]) (hP : shapeProp f P) :
    P.natDegree = p := by
  obtain ⟨a, -, hshape⟩ := hP
  have hcp : P.coeff p = 1 := by
    rw [hshape]
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_X,
      Polynomial.finsetSum_coeff]
    simp only [↓reduceIte, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_Ioo, lt_self_iff_false, and_false, add_zero,
      sub_eq_self, ite_eq_right_iff, one_ne_zero, imp_false]
    exact ne_of_lt (Fact.out : p.Prime).one_lt
  have hle : P.natDegree ≤ p := by
    rw [hshape]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_sub_le _ _).trans
        (max_le (natDegree_X_pow_le p) (natDegree_X_le.trans (Fact.out : p.Prime).one_lt.le))
    · refine natDegree_sum_le_of_forall_le (n := p) _ _ fun i hi ↦ ?_
      exact (natDegree_C_mul_X_pow_le _ _).trans (Finset.mem_Ioo.mp hi).2.le
  exact le_antisymm hle (le_natDegree_of_ne_zero (by simp [hcp]))

private lemma scaled_power_lift
    {B : Type uB} {K : Type uK} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Field K] [Algebra B K] [IsFractionRing B K]
    (P : B[X]) (hP : P.Monic) (π : B) (n p i : ℕ) (hi : i ≤ p)
    (hdeg : P.natDegree = p) (z : K)
    (hz : ∃ b : B, (algebraMap B K π) ^ n * P.eval₂ (algebraMap B K) z =
      algebraMap B K b) :
    ∃ b : B, (algebraMap B K π) ^ n * z ^ i = algebraMap B K b := by
  let v := (IsDiscreteValuationRing.maximalIdeal B).valuation K
  have hπle : v (algebraMap B K π) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  have hbound : v ((algebraMap B K π) ^ n) *
      v (P.eval₂ (algebraMap B K) z) ≤ 1 := by
    obtain ⟨b, hb⟩ := hz
    have hb' : v (algebraMap B K b) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
    rwa [← hb, map_mul] at hb'
  have hzi : v ((algebraMap B K π) ^ n * z ^ i) ≤ 1 := by
    rw [map_mul, map_pow, map_pow]
    by_cases hzone : v z ≤ 1
    · calc
        v (algebraMap B K π) ^ n * v z ^ i ≤ 1 ^ n * 1 ^ i := by
          gcongr
        _ = 1 := by simp
    · have hzgt : 1 < v z := lt_of_not_ge hzone
      rw [valuation_eval₂_eq_pow_of_monic_of_one_lt P hP z hzgt, hdeg, map_pow] at hbound
      calc
        v (algebraMap B K π) ^ n * v z ^ i ≤
            v (algebraMap B K π) ^ n * v z ^ p := by
          gcongr
          exact hzgt.le
        _ ≤ 1 := hbound
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hzi
  exact ⟨b, hb.symm⟩

/-- For the Kummer polynomial `P` associated to a primitive `p`-th root of unity,
if `w = 1 - ζ` has order `e₁` and `π ^ n P(z)` is integral, then
`P(z) ≡ z ^ p - z` modulo `π ^ (e₁ - n) B`. -/
@[stacks 09F6]
theorem eval_sub_pow_sub_mem_uniformizer_zpow
    (B : Type uB) (K : Type uK)
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (p : ℕ) [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : shapeProp f P)
    (π : B) (hπ : Irreducible π) (e₁ n : ℕ)
    (hw : Associated (wElt f) (π ^ e₁)) (z : K)
    (hz : ∃ b : B,
      (algebraMap B K π) ^ n * P.eval₂ (algebraMap B K) z = algebraMap B K b) :
    ∃ b : B,
      P.eval₂ (algebraMap B K) z - (z ^ p - z) =
        (algebraMap B K π) ^ ((e₁ : ℤ) - n) * algebraMap B K b := by
  classical
  have hmon : P.Monic := monic_of_shapeProp f P hP
  obtain ⟨a, ha, hshape⟩ := hP
  have hdeg : P.natDegree = p := natDegree_of_shapeProp f P ⟨a, ha, hshape⟩
  have herr : P.eval₂ (algebraMap B K) z - (z ^ p - z) =
      ∑ i ∈ Finset.Ioo 0 p, algebraMap B K (a i) * z ^ i := by
    rw [hshape]
    simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_finsetSum,
      eval₂_mul, eval₂_C]
    ring
  have hterm : ∀ i ∈ Finset.Ioo 0 p, ∃ b : B,
      algebraMap B K (a i) * z ^ i =
        (algebraMap B K π) ^ ((e₁ : ℤ) - n) * algebraMap B K b := by
    intro i hi
    obtain ⟨hi0, hip⟩ := Finset.mem_Ioo.mp hi
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (ha i hi0 hip)
    obtain ⟨d, hd⟩ := scaled_power_lift P hmon π n p i hip.le hdeg z hz
    obtain ⟨u, hu⟩ := hw
    refine ⟨c * d * (↑u⁻¹ : B), ?_⟩
    rw [← hc, map_mul, map_mul, map_units_inv]
    have hπ0 : algebraMap B K π ≠ 0 :=
      fun h ↦ hπ.ne_zero ((IsFractionRing.injective B K) (by simpa using h))
    have huK : algebraMap B K (u : B) ≠ 0 := fun h ↦
      u.ne_zero ((IsFractionRing.injective B K) (by simp at h))
    rw [zpow_sub₀ hπ0, zpow_natCast, zpow_natCast]
    field_simp
    rw [show algebraMap B K c * algebraMap B K (wElt f) * z ^ i *
        algebraMap B K π ^ n * algebraMap B K (u : B) =
        algebraMap B K (wElt f) * algebraMap B K (u : B) *
          algebraMap B K c * (algebraMap B K π ^ n * z ^ i) by ring,
      hd, map_mul]
    rw [← map_mul _ (wElt f) (u : B), hu, map_pow]
    ring
  choose! b hb using hterm
  refine ⟨∑ i ∈ Finset.Ioo 0 p, b i, ?_⟩
  rw [herr, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl hb

open scoped nonZeroDivisors in
/-- **Stacks 09F7.** The correction term in the finite-level group law vanishes modulo
`π ^ (-2n + p e₁) B`. -/
@[stacks 09F7]
theorem add_mul_correction_sModEq
    {B K : Type*} [CommRing B] [IsDomain B] [Field K]
    [Algebra B K] [IsFractionRing B K]
    {p n e₁ : ℕ} {π w : B} {ξ₁ ξ₂ : K}
    (hw : Associated w (π ^ e₁))
    (hξ₁ : ξ₁ ∈ FractionalIdeal.spanSingleton B⁰
      ((algebraMap B K π) ^ (-(n : ℤ))))
    (hξ₂ : ξ₂ ∈ FractionalIdeal.spanSingleton B⁰
      ((algebraMap B K π) ^ (-(n : ℤ)))) :
    SModEq (FractionalIdeal.spanSingleton B⁰
        ((algebraMap B K π) ^ (-(2 : ℤ) * n + p * e₁ : ℤ)) : Submodule B K)
      (ξ₁ + ξ₂ + (algebraMap B K w) ^ p * ξ₁ * ξ₂) (ξ₁ + ξ₂) := by
  rw [SModEq.sub_mem, add_sub_cancel_left]
  rcases (FractionalIdeal.mem_spanSingleton B⁰).mp hξ₁ with ⟨a, rfl⟩
  rcases (FractionalIdeal.mem_spanSingleton B⁰).mp hξ₂ with ⟨b, rfl⟩
  rcases hw with ⟨u, hu⟩
  have hw' : w = π ^ e₁ * (u⁻¹ : Bˣ) := by
    apply (mul_right_cancel₀ (Units.ne_zero u))
    simpa [mul_assoc] using hu
  by_cases hπ : π = 0
  · subst π
    cases n with
    | zero =>
        apply (FractionalIdeal.mem_spanSingleton B⁰).mpr
        refine ⟨(u⁻¹ : Bˣ) ^ p * a * b, ?_⟩
        simp only [map_zero, Int.reduceNeg, CharP.cast_eq_zero, mul_zero, zero_add,
          Algebra.smul_def, map_mul, map_pow, map_units_inv, inv_pow, hw', neg_zero,
          zpow_ofNat, pow_zero, mul_one]
        rw [show (0 : K) ^ ((p : ℤ) * (e₁ : ℤ)) = 0 ^ (p * e₁) by
          norm_num [← zpow_natCast], mul_pow]
        ring_nf
    | succ n =>
        have hz : (0 : K) ^ (-(↑(n + 1) : ℤ)) = 0 := by
          rw [zero_zpow]
          omega
        simp only [map_zero, hz, smul_zero, mul_zero]
        exact Submodule.zero_mem _
  · apply (FractionalIdeal.mem_spanSingleton B⁰).mpr
    refine ⟨(u⁻¹ : Bˣ) ^ p * a * b, ?_⟩
    have hπK : algebraMap B K π ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective B K).ne hπ
    rw [hw']
    simp only [Algebra.smul_def, map_mul, map_pow]
    rw [show (-(2 : ℤ) * (n : ℤ) + (p : ℤ) * e₁) =
        (p : ℤ) * e₁ + (-(n : ℤ) + -(n : ℤ)) by omega, zpow_add₀ hπK, zpow_add₀ hπK]
    simp only [mul_pow]
    norm_num
    rw [show (algebraMap B K π) ^ ((p : ℤ) * (e₁ : ℤ)) =
        (algebraMap B K π) ^ (p * e₁) by norm_num [← zpow_natCast]]
    ring_nf

end IsDiscreteValuationRing
