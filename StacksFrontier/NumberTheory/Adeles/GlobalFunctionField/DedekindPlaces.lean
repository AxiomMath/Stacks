module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import StacksFrontier.NumberTheory.Adeles.UnramifiedCuspForm

/-!
# Discrete places and the places of a field over a Dedekind subring

A place `v` of a field `K` (a valuation subring of `K` other than `K`) is *discrete* when it is the
valuation subring of a surjective `ℤᵐ⁰`-valued valuation. Such a valuation is unique, and is called
the normalized valuation of `v`.

If `B ⊆ K` is a Dedekind domain with fraction field `K`, the places of `K` containing `B` are
exactly the valuation subrings of the adic valuations of `B` at its height-one primes. In
particular they are discrete.

## Main definitions

* `Stacks.Adeles.Place.IsDiscrete` — the place is the valuation subring of a surjective
  `ℤᵐ⁰`-valued valuation.
* `Stacks.Adeles.Place.normVal` — the normalized valuation of a discrete place.
* `Stacks.Adeles.Place.ofHeightOneSpectrum` — the place of `K` at a height-one prime of a Dedekind
  domain `B` with fraction field `K`.

## Main results

* `Valuation.eq_of_valuationSubring_eq_of_surjective` — two surjective `ℤᵐ⁰`-valued valuations
  with the same valuation subring are equal.
* `Stacks.Adeles.Place.exists_eq_ofHeightOneSpectrum` — a place containing `B` is the place at a
  height-one prime of `B`.
-/

@[expose] public noncomputable section

open IsDedekindDomain WithZero

universe u v

/-- An element of `ℤᵐ⁰` is less than `1` iff it is at most `exp (-1)`. -/
private theorem lt_one_iff_le_exp_neg_one (x : ℤᵐ⁰) : x < 1 ↔ x ≤ exp (-1) := by
  simpa [← exp_add] using lt_mul_exp_iff_le (x := x) (y := exp (-1)) (by simp)

/-- Two surjective `ℤᵐ⁰`-valued valuations of a field with the same valuation subring are
equal. -/
public theorem Valuation.eq_of_valuationSubring_eq_of_surjective {K : Type u} [Field K]
    {w₁ w₂ : Valuation K ℤᵐ⁰} (h : w₁.valuationSubring = w₂.valuationSubring)
    (h₁ : Function.Surjective w₁) (h₂ : Function.Surjective w₂) : w₁ = w₂ := by
  have he : w₁.IsEquiv w₂ := (Valuation.isEquiv_iff_valuationSubring w₁ w₂).2 h
  obtain ⟨ϖ, hϖ⟩ := h₁ (exp (-1))
  obtain ⟨ϖ', hϖ'⟩ := h₂ (exp (-1))
  have hϖ₂ : w₂ ϖ = exp (-1) := by
    refine le_antisymm ((lt_one_iff_le_exp_neg_one _).1 (he.lt_one_iff_lt_one.1 (by simp [hϖ]))) ?_
    rw [← hϖ']
    refine he.le_iff_le.1 ?_
    rw [hϖ]
    exact (lt_one_iff_le_exp_neg_one _).1 (he.lt_one_iff_lt_one.2 (by simp [hϖ']))
  ext z
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, w₁ z = exp n := ⟨_, (exp_log (by simpa using hz)).symm⟩
  have hpow : (exp (-1 : ℤ)) ^ n = exp (-n) := by
    rw [← exp_zsmul]
    simp
  have h1 : w₁ (z * ϖ ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, hpow, hn, ← exp_add]
    simp
  have h2 : w₂ (z * ϖ ^ n) = 1 := he.eq_one_iff_eq_one.1 h1
  rw [map_mul, map_zpow₀, hϖ₂, hpow] at h2
  rw [hn, eq_inv_of_mul_eq_one_left h2, exp_neg, inv_inv]

namespace Stacks.Adeles.Place

variable {K : Type u} [Field K]

/-- A place is *discrete* if its valuation subring is the valuation subring of a surjective
`ℤᵐ⁰`-valued valuation. -/
public def IsDiscrete (v : Place K) : Prop :=
  ∃ w : Valuation K ℤᵐ⁰, w.valuationSubring = v.1 ∧ Function.Surjective w

/-- The normalized valuation of a place: the surjective `ℤᵐ⁰`-valued valuation whose valuation
subring is the place, when the place is discrete (and the trivial valuation otherwise). -/
public def normVal (v : Place K) : Valuation K ℤᵐ⁰ := by
  classical
  exact if h : v.IsDiscrete then h.choose else 1

/-- The normalized valuation of a discrete place has the place as valuation subring and is
surjective. -/
public theorem normVal_spec {v : Place K} (hv : v.IsDiscrete) :
    v.normVal.valuationSubring = v.1 ∧ Function.Surjective v.normVal := by
  classical
  simp only [normVal, dite_eq_left hv]
  exact hv.choose_spec

/-- Any surjective `ℤᵐ⁰`-valued valuation with valuation subring `v` is the normalized valuation
of `v`. -/
public theorem normVal_eq {v : Place K} {w : Valuation K ℤᵐ⁰} (hw : w.valuationSubring = v.1)
    (hs : Function.Surjective w) : v.normVal = w :=
  Valuation.eq_of_valuationSubring_eq_of_surjective ((normVal_spec ⟨w, hw, hs⟩).1.trans hw.symm)
    (normVal_spec ⟨w, hw, hs⟩).2 hs

variable {B : Type v} [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]

/-- The place of `K` at a height-one prime `P` of a Dedekind domain `B` with fraction field `K`:
the valuation subring of the `P`-adic valuation. -/
public def ofHeightOneSpectrum (P : HeightOneSpectrum B) : Place K :=
  ⟨(P.valuation K).valuationSubring, fun h => by
    obtain ⟨y, hy⟩ := P.valuation_surjective K (exp 1)
    have : y ∈ (P.valuation K).valuationSubring := h ▸ ValuationSubring.mem_top y
    rw [Valuation.mem_valuationSubring_iff, hy] at this
    exact absurd this (by simp [← exp_zero])⟩

/-- The valuation subring of the place at a height-one prime `P` is that of the `P`-adic
valuation. -/
@[simp]
public theorem ofHeightOneSpectrum_val (P : HeightOneSpectrum B) :
    (ofHeightOneSpectrum (K := K) P).1 = (P.valuation K).valuationSubring := rfl

/-- The place at a height-one prime is discrete, with normalized valuation the adic valuation. -/
public theorem normVal_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    (ofHeightOneSpectrum (K := K) P).normVal = P.valuation K :=
  normVal_eq rfl (P.valuation_surjective K)

/-- The place at a height-one prime is discrete. -/
public theorem isDiscrete_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    (ofHeightOneSpectrum (K := K) P).IsDiscrete :=
  ⟨P.valuation K, rfl, P.valuation_surjective K⟩

/-- If `I` is the ideal of elements of `R` in the maximal ideal of a place `v` containing `R`, then
elements of `R` outside `I` have valuation `1`. -/
private theorem valuation_algebraMap_eq_one {R : Type v} [CommRing R] [Algebra R K] (v : Place K)
    (hR : ∀ r : R, algebraMap R K r ∈ v.1) (I : Ideal R)
    (hmem : ∀ r : R, r ∈ I ↔ v.1.valuation (algebraMap R K r) < 1) {r : R} (hr : r ∉ I) :
    v.1.valuation (algebraMap R K r) = 1 :=
  le_antisymm (v.1.valuation_le_one ⟨_, hR r⟩) (not_lt.1 fun hlt => hr ((hmem r).2 hlt))

/-- If a place `v` contains `B` and `P` is the prime of elements of `B` in the maximal ideal of `v`,
then the valuation subring of the `P`-adic valuation lies in `v`. -/
private theorem valuationSubring_valuation_le (v : Place K) (hB : ∀ b : B, algebraMap B K b ∈ v.1)
    (P : HeightOneSpectrum B)
    (hmem : ∀ b : B, b ∈ P.asIdeal ↔ v.1.valuation (algebraMap B K b) < 1) :
    (P.valuation K).valuationSubring ≤ v.1 := by
  intro y hy
  rw [Valuation.mem_valuationSubring_iff] at hy
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer y hy
  have hd : v.1.valuation (algebraMap B K d) = 1 :=
    valuation_algebraMap_eq_one v hB P.asIdeal hmem d.2
  rw [← ValuationSubring.valuation_le_one_iff]
  have := congrArg v.1.valuation hnd
  rw [map_mul, hd, mul_one] at this
  rw [this]
  exact v.1.valuation_le_one ⟨_, hB n⟩

/-- If `P` is the prime of elements of `B` in the maximal ideal of a place `v`, and the valuation
subring of the `P`-adic valuation lies in `v`, then `v` lies in it. -/
private theorem le_valuationSubring_valuation (v : Place K) (P : HeightOneSpectrum B)
    (hmem : ∀ b : B, b ∈ P.asIdeal ↔ v.1.valuation (algebraMap B K b) < 1)
    (hle : (P.valuation K).valuationSubring ≤ v.1) : v.1 ≤ (P.valuation K).valuationSubring := by
  intro z hz
  rw [Valuation.mem_valuationSubring_iff]
  by_contra hgt
  push Not at hgt
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hgt
  obtain ⟨ϖ, hϖ⟩ := P.intValuation_exists_uniformizer
  have hϖK : P.valuation K (algebraMap B K ϖ) = exp (-1) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hϖ]
  have hzinv : P.valuation K z⁻¹ ≤ exp (-1) := by
    rw [← lt_one_iff_le_exp_neg_one, map_inv₀]
    exact inv_lt_one_of_one_lt₀ hgt
  have hϖ0 : algebraMap B K ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖK
    exact exp_ne_zero hϖK.symm
  have hw : z⁻¹ * (algebraMap B K ϖ)⁻¹ ∈ v.1 := by
    apply hle
    rw [Valuation.mem_valuationSubring_iff, map_mul, map_inv₀ _ (algebraMap B K ϖ), hϖK]
    calc P.valuation K z⁻¹ * (exp (-1))⁻¹ ≤ exp (-1) * (exp (-1))⁻¹ :=
          mul_le_mul_left hzinv _
      _ = 1 := mul_inv_cancel₀ exp_ne_zero
  have hinv : (algebraMap B K ϖ)⁻¹ ∈ v.1 := by
    have := mul_mem hz hw
    rwa [← mul_assoc, mul_inv_cancel₀ hz0, one_mul] at this
  have hϖP : ϖ ∈ P.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, hϖ]
    simp [← exp_zero]
  have h3 : v.1.valuation (algebraMap B K ϖ * (algebraMap B K ϖ)⁻¹) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le ((hmem ϖ).1 hϖP) (v.1.valuation_le_one ⟨_, hinv⟩)
  rw [mul_inv_cancel₀ hϖ0, map_one] at h3
  exact lt_irrefl _ h3

/-- A place containing a Dedekind domain `B` with fraction field `K` is the place at a height-one
prime of `B`, namely the prime of elements of `B` in the maximal ideal of the place. -/
public theorem exists_eq_ofHeightOneSpectrum (v : Place K)
    (hB : ∀ b : B, algebraMap B K b ∈ v.1) :
    ∃ P : HeightOneSpectrum B, v = ofHeightOneSpectrum P ∧
      ∀ b : B, b ∈ P.asIdeal ↔ v.1.valuation (algebraMap B K b) < 1 := by
  let φ : B →+* v.1 := (algebraMap B K).codRestrict v.1.toSubring hB
  let 𝔓 : Ideal B := (IsLocalRing.maximalIdeal v.1).comap φ
  have hmem : ∀ b : B, b ∈ 𝔓 ↔ v.1.valuation (algebraMap B K b) < 1 := fun b => by
    simp only [𝔓, Ideal.mem_comap]
    exact ValuationSubring.valuation_lt_one_iff v.1 (φ b)
  have hne : 𝔓 ≠ ⊥ := by
    intro h0
    apply v.2
    rw [eq_top_iff]
    intro y _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hvb := valuation_algebraMap_eq_one v hB 𝔓 hmem
      (fun h => hb0 (by rwa [h0, Ideal.mem_bot] at h))
    rw [← ValuationSubring.valuation_le_one_iff]
    simpa [hvb] using v.1.valuation_le_one ⟨_, hB a⟩
  let P : HeightOneSpectrum B := ⟨𝔓, Ideal.comap_isPrime _ _, hne⟩
  have hle := valuationSubring_valuation_le v hB P hmem
  exact ⟨P, Subtype.ext (le_antisymm (le_valuationSubring_valuation v P hmem hle) hle), hmem⟩

/-- A place containing a Dedekind domain with fraction field `K` is discrete. -/
public theorem isDiscrete_of_forall_mem (v : Place K) (hB : ∀ b : B, algebraMap B K b ∈ v.1) :
    v.IsDiscrete := by
  obtain ⟨P, rfl, -⟩ := exists_eq_ofHeightOneSpectrum v hB
  exact isDiscrete_ofHeightOneSpectrum P

end Stacks.Adeles.Place

end
