module

public import Mathlib.RingTheory.KrullDimension.Regular
public import StacksCore.Tactic.StacksAttribute

/-!
# Cutting by one element of the maximal ideal of a Noetherian local ring

Let `R` be a Noetherian local ring, `M` a finite `R`-module and `x` an element of the maximal
ideal. Then `dim Supp(M/xM) ≤ dim Supp(M) ≤ dim Supp(M/xM) + 1`, with equality on the right when
`x` lies in no minimal prime of `Supp(M)`, which is the case when `x` is a nonzerodivisor on `M`.
For `M = R` this reads `dim R ≤ dim R/xR + 1`, with equality when `x` lies in no minimal prime
of `R`.

## Main results

* `Module.supportDim_quotSMulTop_le_and_le_succ_and_eq_of_notMem_minimal`: all claims of
  **Stacks Tag 0B52**, the two inequalities, the equality case and the parenthetical
  nonzerodivisor example.

* `ringKrullDim_le_quotient_span_singleton_add_one_and_eq_of_notMem_minimalPrimes`: both claims
  of **Stacks Tag 00KW**.

## Implementation notes

Dimensions are `ringKrullDim`, with values in `WithBot ℕ∞`. Both claims are the case `M = R` of
Mathlib's module statements `Module.supportDim_le_supportDim_quotSMulTop_succ` and
`Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal`
(Stacks Tag 0B52): the annihilator of `R` is `⊥`, whose minimal primes are those of `R`, and
`x • ⊤ = (x)`. The nonzerodivisor case is Mathlib's
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`.

For 0B52, `M/xM` is `QuotSMulTop x M` and `dim Supp` is `Module.supportDim`. The left inequality
is Mathlib's `Module.supportDim_le_of_surjective` applied to the quotient map, the right one is
Mathlib's `Module.supportDim_le_supportDim_quotSMulTop_succ`, and the equality case is Mathlib's
`Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal`, whose
hypothesis is phrased with the minimal primes of the annihilator of `M`; these are the minimal
elements of `Supp(M) = V(Ann(M))` (`Module.mem_support_iff_of_finite`). The parenthetical claim,
that a nonzerodivisor on `M` lies in no minimal prime of the support (Stacks Tag 00LD), is
Mathlib's `IsSMulRegular.notMem_of_mem_minimalPrimes`.

## References

* [Stacks Project, Tag 0B52](https://stacks.math.columbia.edu/tag/0B52)

* [Stacks Project, Tag 00KW](https://stacks.math.columbia.edu/tag/00KW)
-/

@[expose] public section

open IsLocalRing Ideal Pointwise

/-- **Stacks 00KW.** Let `R` be a Noetherian local ring and `x ∈ 𝔪`. Then
`dim R ≤ dim R/xR + 1`, and if `x` is contained in no minimal prime of `R` then
`dim R/xR + 1 = dim R`. -/
@[stacks 00KW "both the inequality and the equality when x avoids the minimal primes"]
theorem ringKrullDim_le_quotient_span_singleton_add_one_and_eq_of_notMem_minimalPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ span {x}) + 1 ∧
      ((∀ p ∈ minimalPrimes R, x ∉ p) → ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R) := by
  have hspan : x • (⊤ : Ideal R) = span {x} := by
    simp [← Submodule.ideal_span_singleton_smul]
  refine ⟨hspan ▸ ringKrullDim_le_ringKrullDim_quotSMulTop_succ hx, fun hmin ↦ ?_⟩
  have hann : Module.annihilator R R = ⊥ :=
    Module.annihilator_eq_bot.mpr
      ((faithfulSMul_iff_algebraMap_injective R R).mpr fun {_ _} h ↦ h)
  have h := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (M := R) (by rwa [hann]) hx
  rw [Module.supportDim_self_eq_ringKrullDim] at h
  rw [← hspan, ← Module.supportDim_quotient_eq_ringKrullDim]
  exact h

namespace Module

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- For a finite module, the minimal elements of the support are the minimal primes of the
annihilator. -/
theorem minimal_mem_support_iff_mem_minimalPrimes_annihilator {p : PrimeSpectrum R} :
    Minimal (· ∈ support R M) p ↔ p.asIdeal ∈ (annihilator R M).minimalPrimes := by
  refine ⟨fun hp ↦ ⟨⟨p.isPrime, mem_support_iff_of_finite.mp hp.1⟩, fun q hq hle ↦ ?_⟩,
    fun hp ↦ ⟨mem_support_iff_of_finite.mpr hp.1.2, fun q hq hle ↦ ?_⟩⟩
  · exact hp.2 (y := ⟨q, hq.1⟩) (mem_support_iff_of_finite.mpr hq.2) hle
  · exact hp.2 ⟨q.isPrime, mem_support_iff_of_finite.mp hq⟩ hle

/-- **Stacks 0B52.** Let `R` be a Noetherian local ring, `M` a finite `R`-module and `x ∈ 𝔪`.
Then `dim Supp(M/xM) ≤ dim Supp(M) ≤ dim Supp(M/xM) + 1`. If `x` is not in any of the minimal
primes of `Supp(M)`, then equality holds for the right inequality. This is the case if `x` is a
nonzerodivisor on `M`: then `x` lies in no minimal prime of `Supp(M)`. -/
@[stacks 0B52 "both inequalities, the equality case, and the nonzerodivisor example"]
theorem supportDim_quotSMulTop_le_and_le_succ_and_eq_of_notMem_minimal
    [IsNoetherianRing R] [IsLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) :
    supportDim R (QuotSMulTop x M) ≤ supportDim R M ∧
      supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 ∧
      ((∀ p : PrimeSpectrum R, Minimal (· ∈ support R M) p → x ∉ p.asIdeal) →
        supportDim R M = supportDim R (QuotSMulTop x M) + 1) ∧
      (IsSMulRegular M x →
        ∀ p : PrimeSpectrum R, Minimal (· ∈ support R M) p → x ∉ p.asIdeal) := by
  refine ⟨supportDim_le_of_surjective _ (Submodule.mkQ_surjective _),
    supportDim_le_supportDim_quotSMulTop_succ hx, fun hn ↦ ?_, fun reg p hp ↦
      reg.notMem_of_mem_minimalPrimes (minimal_mem_support_iff_mem_minimalPrimes_annihilator.mp hp)⟩
  refine (supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (fun q hq ↦ ?_) hx).symm
  exact hn ⟨q, hq.1.1⟩ (minimal_mem_support_iff_mem_minimalPrimes_annihilator.mpr hq)

end Module

end
