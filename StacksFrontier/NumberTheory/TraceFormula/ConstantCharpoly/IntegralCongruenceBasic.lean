module

public import Mathlib.Algebra.CharP.IntermediateField
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Congruences between integral elements over `𝔽_ℓ⟦X⟧`

Let `Λ` be a field which is an algebra over `R = 𝔽_ℓ⟦X⟧` with injective structure map. We write
`x ≡ y mod X^N` for elements of `Λ` when `x - y = X^N z` with `z` integral over `R`.

* If `a ∈ R` is congruent modulo `X^N` to an element `b` of `Λ` algebraic over the prime field,
  then the coefficients of `a` in degrees `1, …, N - 1` vanish. Indeed `b^q = b` for a power `q`
  of `ℓ`, so `a^q ≡ a mod X^N`, and `R` is integrally closed, so `X^N` divides `a^q - a` in `R`.
  Comparing the lowest nonconstant coefficients of `a^q` and `a` gives the claim.
* If `u` and `u⁻¹` are integral over `R`, then some power `u^m` with `m ≥ 1` is congruent to `1`
  modulo `X`: the powers of `u` in the finite `R`-module `R[u, u⁻¹]` repeat modulo `X`. Raising to
  the power `ℓ^N` then gives `u^n ≡ 1 mod X^N` for every multiple `n` of `m ℓ^N`.

## Main results

* `Stacks.TraceFormula.coeff_eq_zero_of_algebraMap_sub_eq_mul`: the vanishing of coefficients.
* `Stacks.TraceFormula.exists_forall_dvd_pow_sub_one_eq_mul`: the congruence `u^n ≡ 1 mod X^N`.
-/

@[expose] public noncomputable section

open PowerSeries

namespace Stacks.TraceFormula

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The power series ring `𝔽_ℓ⟦X⟧` has characteristic `ℓ`. -/
public theorem charP_powerSeries_zmod : CharP (ZMod ℓ)⟦X⟧ ℓ :=
  charP_of_injective_ringHom C_injective ℓ

attribute [local instance] charP_powerSeries_zmod

variable {Λ : Type*} [Field Λ] [Algebra (ZMod ℓ)⟦X⟧ Λ]

/-- A field containing `𝔽_ℓ⟦X⟧` has characteristic `ℓ`. -/
public theorem charP_of_injective_algebraMap_powerSeries
    (hι : Function.Injective (algebraMap (ZMod ℓ)⟦X⟧ Λ)) : CharP Λ ℓ :=
  charP_of_injective_algebraMap hι ℓ

omit [Algebra (ZMod ℓ)⟦X⟧ Λ] in
/-- The prime field of a field of characteristic `ℓ` is finite. -/
public theorem finite_bot_subfield [CharP Λ ℓ] : Finite (⊥ : Subfield Λ) := by
  let f : ZMod ℓ →+* Λ := ZMod.castHom (dvd_refl ℓ) Λ
  refine Set.Finite.to_subtype ((Set.finite_range f).subset fun x hx => ?_)
  exact RingHom.mem_fieldRange.1 ((bot_le : (⊥ : Subfield Λ) ≤ f.fieldRange) hx)

omit [Algebra (ZMod ℓ)⟦X⟧ Λ] in
/-- An element algebraic over the prime field of a field of characteristic `ℓ` is fixed by a
positive power of the Frobenius. -/
public theorem exists_pow_prime_pow_eq_self [CharP Λ ℓ] {b : Λ}
    (hb : IsAlgebraic (⊥ : Subfield Λ) b) : ∃ f : ℕ, 0 < f ∧ b ^ ℓ ^ f = b := by
  have := finite_bot_subfield (ℓ := ℓ) (Λ := Λ)
  let K := IntermediateField.adjoin (⊥ : Subfield Λ) {b}
  have : FiniteDimensional (⊥ : Subfield Λ) K :=
    IntermediateField.adjoin.finiteDimensional hb.isIntegral
  have : Finite K := Module.finite_of_finite (⊥ : Subfield Λ)
  let := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
  refine ⟨n, n.pos, ?_⟩
  have h := FiniteField.pow_card (⟨b, IntermediateField.mem_adjoin_simple_self _ b⟩ : K)
  rw [hn] at h
  simpa using congrArg Subtype.val h

/-- An element algebraic over the prime field is integral over `𝔽_ℓ⟦X⟧`. -/
public theorem isIntegral_of_isAlgebraic_bot
    (hι : Function.Injective (algebraMap (ZMod ℓ)⟦X⟧ Λ)) {b : Λ}
    (hb : IsAlgebraic (⊥ : Subfield Λ) b) : IsIntegral (ZMod ℓ)⟦X⟧ b := by
  have := charP_of_injective_algebraMap_powerSeries hι
  obtain ⟨f, hf, hbf⟩ := exists_pow_prime_pow_eq_self (ℓ := ℓ) hb
  have hq : 1 < ℓ ^ f := Nat.one_lt_pow hf.ne' (Fact.out : ℓ.Prime).one_lt
  refine ⟨Polynomial.X ^ ℓ ^ f - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
  · rw [Polynomial.degree_X]
    exact_mod_cast hq
  · simp [hbf]

/-- `𝔽_ℓ⟦X⟧` is integrally closed in any field containing it: if `r = s w` with `s ≠ 0` and `w`
integral, then `s` divides `r`. -/
public theorem dvd_of_algebraMap_eq_mul (hι : Function.Injective (algebraMap (ZMod ℓ)⟦X⟧ Λ))
    {r s : (ZMod ℓ)⟦X⟧} (hs : s ≠ 0) {w : Λ} (hw : IsIntegral (ZMod ℓ)⟦X⟧ w)
    (h : algebraMap _ Λ r = algebraMap _ Λ s * w) : s ∣ r := by
  let K := FractionRing (ZMod ℓ)⟦X⟧
  let g : K →ₐ[(ZMod ℓ)⟦X⟧] Λ :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId (ZMod ℓ)⟦X⟧ Λ) (by exact hι)
  have hs' : algebraMap _ Λ s ≠ 0 := (map_ne_zero_iff _ hι).2 hs
  have hk : g (algebraMap _ K r / algebraMap _ K s) = w := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes, h, mul_div_cancel_left₀ _ hs']
  have hint : IsIntegral (ZMod ℓ)⟦X⟧ (algebraMap _ K r / algebraMap _ K s) :=
    (isIntegral_algHom_iff g (by exact (g : K →+* Λ).injective)).1 (hk ▸ hw)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨y, hι ?_⟩
  rw [h, map_mul, ← hk, ← hy, AlgHom.commutes]

/-- If `a ∈ 𝔽_ℓ⟦X⟧` is congruent modulo `X^N` to an element `b` algebraic over the prime field,
`a - b = X^N z` with `z` integral, then the coefficients of `a` in degrees `1, …, N - 1`
vanish. -/
public theorem coeff_eq_zero_of_algebraMap_sub_eq_mul
    (hι : Function.Injective (algebraMap (ZMod ℓ)⟦X⟧ Λ)) {a : (ZMod ℓ)⟦X⟧} {b z : Λ}
    (hb : IsAlgebraic (⊥ : Subfield Λ) b) (hz : IsIntegral (ZMod ℓ)⟦X⟧ z) {N : ℕ}
    (h : algebraMap _ Λ a - b = algebraMap (ZMod ℓ)⟦X⟧ Λ (X ^ N) * z) {c : ℕ} (hc1 : 1 ≤ c)
    (hcN : c < N) : coeff c a = 0 := by
  have := charP_of_injective_algebraMap_powerSeries hι
  obtain ⟨f, hf, hbf⟩ := exists_pow_prime_pow_eq_self (ℓ := ℓ) hb
  have hq2 : 2 ≤ ℓ ^ f :=
    (Fact.out : ℓ.Prime).two_le.trans (Nat.le_self_pow hf.ne' ℓ)
  obtain ⟨k, hk⟩ : ∃ k, ℓ ^ f = k + 1 := ⟨ℓ ^ f - 1, by omega⟩
  set T := algebraMap (ZMod ℓ)⟦X⟧ Λ (X ^ N)
  have hr : X ^ N ∣ a ^ ℓ ^ f - a := by
    refine dvd_of_algebraMap_eq_mul hι (pow_ne_zero _ X_ne_zero)
      (w := T ^ k * z ^ (k + 1) - z)
      (((isIntegral_algebraMap.pow _).mul (hz.pow _)).sub hz) ?_
    have hA : algebraMap (ZMod ℓ)⟦X⟧ Λ a = b + T * z := by linear_combination h
    rw [map_sub, map_pow, hA, add_pow_char_pow, hbf, mul_pow, hk]
    ring
  obtain ⟨y, hy⟩ := hr
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  set a0 := constantCoeff a with ha0
  have hdvd : X ^ c ∣ a - C a0 := by
    rw [X_pow_dvd_iff]
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [coeff_zero_eq_constantCoeff_apply, ha0]
    · rw [map_sub, ih m hm hm0 (hm.trans hcN), coeff_C, ite_eq_right hm0.ne', sub_zero]
  obtain ⟨a', ha'⟩ := hdvd
  have hca : coeff c a = constantCoeff a' := by
    have := congrArg (coeff c) ha'
    rw [map_sub, coeff_C, ite_eq_right (by omega), sub_zero, coeff_X_pow_mul', ite_eq_left le_rfl,
      Nat.sub_self, coeff_zero_eq_constantCoeff_apply] at this
    exact this
  have ha : a = C a0 + X ^ c * a' := by rw [← ha']; ring
  have hpow : a ^ ℓ ^ f = C a0 + X ^ (c * ℓ ^ f) * a' ^ ℓ ^ f := by
    conv_lhs => rw [ha]
    rw [add_pow_char_pow, ← map_pow, ZMod.pow_card_pow, mul_pow, ← pow_mul]
  have e : X ^ N * y = X ^ (c * ℓ ^ f) * a' ^ ℓ ^ f - X ^ c * a' := by
    rw [← hy]
    linear_combination hpow - ha
  have hcq : ¬ c * ℓ ^ f ≤ c :=
    not_le.2 (lt_of_lt_of_le (by omega : c < c * 2) (Nat.mul_le_mul_left c hq2))
  have h2 := congrArg (coeff c) e
  simp only [map_sub, coeff_X_pow_mul'] at h2
  rw [ite_eq_right (by omega), ite_eq_right hcq, ite_eq_left le_rfl, Nat.sub_self,
    coeff_zero_eq_constantCoeff_apply] at h2
  rw [hca]
  linear_combination h2

/-- If `u ≠ 0` and `u⁻¹` are integral over `𝔽_ℓ⟦X⟧`, then `u^m - 1 = X z` with `z` integral
for some `m ≥ 1`. -/
public theorem exists_pow_sub_one_eq_mul {u : Λ} (hu0 : u ≠ 0)
    (hu : IsIntegral (ZMod ℓ)⟦X⟧ u) (hu' : IsIntegral (ZMod ℓ)⟦X⟧ u⁻¹) :
    ∃ m : ℕ, 0 < m ∧ ∃ z : Λ, IsIntegral (ZMod ℓ)⟦X⟧ z ∧
      u ^ m - 1 = algebraMap (ZMod ℓ)⟦X⟧ Λ X * z := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hint : ∀ x ∈ ({u, u⁻¹} : Set Λ), IsIntegral (ZMod ℓ)⟦X⟧ x := by
    rintro x (rfl | rfl)
    exacts [hu, hu']
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (fg_adjoin_of_finite ((Set.finite_singleton _).insert _) hint)
  have hle : Algebra.adjoin (ZMod ℓ)⟦X⟧ ({u, u⁻¹} : Set Λ) ≤ integralClosure (ZMod ℓ)⟦X⟧ Λ :=
    Algebra.adjoin_le fun x hx => hint x hx
  have hsI : ∀ i, IsIntegral (ZMod ℓ)⟦X⟧ (s i) := by
    intro i
    have : s i ∈ Subalgebra.toSubmodule (Algebra.adjoin (ZMod ℓ)⟦X⟧ ({u, u⁻¹} : Set Λ)) :=
      hs ▸ Submodule.subset_span ⟨i, rfl⟩
    exact hle this
  have hmem : ∀ k : ℕ, u ^ k ∈ Submodule.span (ZMod ℓ)⟦X⟧ (Set.range s) := by
    intro k
    rw [hs]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) k
  choose cf hcf using fun k => (Submodule.mem_span_range_iff_exists_fun (ZMod ℓ)⟦X⟧).1 (hmem k)
  obtain ⟨a, b, hne, hφ⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => fun i : Fin n => constantCoeff (cf k i))
  have key : ∀ a b : ℕ, a < b →
      (fun i => constantCoeff (cf a i)) = (fun i => constantCoeff (cf b i)) →
      ∃ m : ℕ, 0 < m ∧ ∃ z : Λ, IsIntegral (ZMod ℓ)⟦X⟧ z ∧
        u ^ m - 1 = algebraMap (ZMod ℓ)⟦X⟧ Λ X * z := by
    intro a b hab hφ
    choose g hg using fun i => X_dvd_iff.2
      (show constantCoeff (cf a i - cf b i) = 0 by rw [map_sub, sub_eq_zero]; exact congrFun hφ i)
    have hz : u ^ a - u ^ b = algebraMap (ZMod ℓ)⟦X⟧ Λ X *
        ∑ i, algebraMap (ZMod ℓ)⟦X⟧ Λ (g i) * s i := by
      rw [← hcf a, ← hcf b, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, hg i, Algebra.smul_def, map_mul]
      ring
    have hinv : (u⁻¹) ^ a * u ^ a = 1 := by rw [← mul_pow, inv_mul_cancel₀ hu0, one_pow]
    have hb' : u ^ b = u ^ a * u ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab.le]
    refine ⟨b - a, by omega, -((u⁻¹) ^ a * ∑ i, algebraMap (ZMod ℓ)⟦X⟧ Λ (g i) * s i),
      ((hu'.pow a).mul (IsIntegral.sum _ fun i _ => isIntegral_algebraMap.mul (hsI i))).neg, ?_⟩
    linear_combination (1 - u ^ (b - a)) * hinv - (u⁻¹) ^ a * hb' - (u⁻¹) ^ a * hz
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a b h hφ
  · exact key b a h hφ.symm

/-- If `u ≠ 0` and `u⁻¹` are integral over `𝔽_ℓ⟦X⟧`, then for every `N` there is `M ≥ 1` with
`u^n - 1 = X^N z`, `z` integral, for every multiple `n` of `M`. -/
public theorem exists_forall_dvd_pow_sub_one_eq_mul
    (hι : Function.Injective (algebraMap (ZMod ℓ)⟦X⟧ Λ)) {u : Λ} (hu0 : u ≠ 0)
    (hu : IsIntegral (ZMod ℓ)⟦X⟧ u) (hu' : IsIntegral (ZMod ℓ)⟦X⟧ u⁻¹) (N : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ n, M ∣ n → ∃ z : Λ, IsIntegral (ZMod ℓ)⟦X⟧ z ∧
      u ^ n - 1 = algebraMap (ZMod ℓ)⟦X⟧ Λ (X ^ N) * z := by
  have := charP_of_injective_algebraMap_powerSeries hι
  obtain ⟨m, hm, z, hz, h⟩ := exists_pow_sub_one_eq_mul hu0 hu hu'
  have hN : N ≤ ℓ ^ N := (Nat.lt_pow_self (Fact.out : ℓ.Prime).one_lt).le
  refine ⟨m * ℓ ^ N, Nat.mul_pos hm (pow_pos (Fact.out : ℓ.Prime).pos _), ?_⟩
  rintro _ ⟨k, rfl⟩
  set T := algebraMap (ZMod ℓ)⟦X⟧ Λ X
  refine ⟨T ^ (ℓ ^ N - N) * z ^ ℓ ^ N * ∑ i ∈ Finset.range k, (u ^ (m * ℓ ^ N)) ^ i,
    ((isIntegral_algebraMap.pow _).mul (hz.pow _)).mul
      (IsIntegral.sum _ fun i _ => (hu.pow _).pow _), ?_⟩
  have e1 : u ^ (m * ℓ ^ N) - 1 = (T * z) ^ ℓ ^ N := by
    rw [← h, sub_pow_char_pow, one_pow, pow_mul]
  have e2 : T ^ ℓ ^ N = algebraMap (ZMod ℓ)⟦X⟧ Λ (X ^ N) * T ^ (ℓ ^ N - N) := by
    rw [map_pow, ← pow_add, Nat.add_sub_cancel' hN]
  rw [pow_mul u (m * ℓ ^ N) k, ← geom_sum_mul, e1, mul_pow, e2]
  ring

end Stacks.TraceFormula
