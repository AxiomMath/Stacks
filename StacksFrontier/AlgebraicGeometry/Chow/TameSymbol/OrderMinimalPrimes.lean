module

public import Mathlib.Data.ENat.BigOperators
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.RestrictedDivisors
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced

/-!
# The order of vanishing as a sum over the minimal primes

Let `C` be a Noetherian local ring of dimension one and `x ∈ C` a nonzerodivisor. Stacks 02QG,
applied to the ideal `I = 0`, computes the order of vanishing of `x` as

`ord_C(x) = ∑_{𝔮 minimal} ord_{C/𝔮}(x) · length_{C_𝔮}(C_𝔮)`.

If `C` is reduced, every localization `C_𝔮` at a minimal prime is a field, of length one over
itself, so that

`ord_C(x) = ∑_{𝔮 minimal} ord_{C/𝔮}(x)`.

## Main results

* `Stacks.Chow.ord_eq_finsum_minimalPrimes_mul_length` — the general formula.
* `Stacks.Chow.ord_eq_finsum_minimalPrimes` — the formula for a reduced ring.
* `Stacks.Chow.ord_toNat_eq_finsum_minimalPrimes` — the same, as an identity of integers.

## References

* [Stacks Project, Tag 02QF](https://stacks.math.columbia.edu/tag/02QF)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
-/

@[expose] public section

universe u

namespace Stacks.Chow

variable {C : Type u} [CommRing C]

/-- The localization of `C ⧸ ⊥` at a prime `𝔮`, as a module over `C_𝔮`, has the length of
`C_𝔮`. -/
theorem length_localizedModule_quotient_bot (q : Ideal C) [q.IsPrime] :
    Module.length (Localization.AtPrime q)
        (LocalizedModule q.primeCompl (C ⧸ (⊥ : Ideal C))) =
      Module.length (Localization.AtPrime q) (Localization.AtPrime q) := by
  let e : (C ⧸ (⊥ : Ideal C)) ≃ₗ[C] C := Submodule.quotEquivOfEqBot ⊥ rfl
  let E : LocalizedModule q.primeCompl (C ⧸ (⊥ : Ideal C)) ≃ₗ[Localization.AtPrime q]
      Localization.AtPrime q :=
    (LocalizedModule.equivTensorProduct q.primeCompl (C ⧸ (⊥ : Ideal C))).trans
      ((TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (Localization.AtPrime q) (Localization.AtPrime q)) e).trans
        (TensorProduct.AlgebraTensorModule.rid C (Localization.AtPrime q)
          (Localization.AtPrime q)))
  exact E.length_eq

/-- A field has length one over itself. -/
theorem length_self_eq_one_of_isField {K : Type u} [CommRing K] (h : IsField K) :
    Module.length K K = 1 := by
  refine Module.length_eq_one_iff.mpr (isSimpleModule_self_iff_isUnit.mpr ⟨⟨h.exists_pair_ne⟩, ?_⟩)
  intro x hx
  obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
  exact ⟨⟨x, y, hy, by rwa [mul_comm]⟩, rfl⟩

variable [IsNoetherianRing C] [IsLocalRing C]

/-- **Stacks 02QG for `I = 0`.** For a nonzerodivisor `x` of a one-dimensional Noetherian local
ring `C`, the order of vanishing of `x` is the sum over the minimal primes `𝔮` of `C` of the
order of vanishing of `x` on `C / 𝔮` times the length of `C_𝔮`. -/
theorem ord_eq_finsum_minimalPrimes_mul_length (hdim : ringKrullDim C = 1) {x : C}
    (hx : x ∈ nonZeroDivisors C) :
    Ring.ord C x =
      ∑ᶠ q ∈ {q : PrimeSpectrum C | q.asIdeal ∈ minimalPrimes C},
        Ring.ord (C ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal x) *
          Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) := by
  have hC : IsSMulRegular C x := (isRegular_iff_mem_nonZeroDivisors.mpr hx).isSMulRegular
  have hx' : IsSMulRegular (C ⧸ (⊥ : Ideal C)) x :=
    let e : (C ⧸ (⊥ : Ideal C)) ≃ₗ[C] C := Submodule.quotEquivOfEqBot ⊥ rfl
    hC.of_injective e e.injective
  have hI : ringKrullDim (C ⧸ (⊥ : Ideal C)) = 1 :=
    (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot C)).trans hdim
  have h := AlgebraicGeometry.length_quotient_span_sup_eq_sum_minimalPrimes x ⊥ hx' hI
  rw [sup_bot_eq] at h
  rw [Ring.ord, h]
  refine finsum_mem_congr rfl fun q _ ↦ ?_
  rw [AlgebraicGeometry.ord_quotient_eq_length, sup_comm, length_localizedModule_quotient_bot]

/-- **The order of vanishing over the minimal primes of a reduced ring.** For a nonzerodivisor
`x` of a reduced one-dimensional Noetherian local ring `C`,
`ord_C(x) = ∑_{𝔮 minimal} ord_{C/𝔮}(x)`: the localizations at the minimal primes are fields. -/
theorem ord_eq_finsum_minimalPrimes [IsReduced C] (hdim : ringKrullDim C = 1) {x : C}
    (hx : x ∈ nonZeroDivisors C) :
    Ring.ord C x = ∑ᶠ p ∈ minimalPrimes C, Ring.ord (C ⧸ p) (Ideal.Quotient.mk p x) := by
  rw [ord_eq_finsum_minimalPrimes_mul_length hdim hx]
  have hcongr : ∑ᶠ q ∈ {q : PrimeSpectrum C | q.asIdeal ∈ minimalPrimes C},
        Ring.ord (C ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal x) *
          Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) =
      ∑ᶠ q ∈ {q : PrimeSpectrum C | q.asIdeal ∈ minimalPrimes C},
        Ring.ord (C ⧸ q.asIdeal) (Ideal.Quotient.mk q.asIdeal x) := by
    refine finsum_mem_congr rfl fun q hq ↦ ?_
    rw [length_self_eq_one_of_isField (isField_localizationAtPrime_of_minimal C q.asIdeal hq),
      mul_one]
  have himage : minimalPrimes C =
      PrimeSpectrum.asIdeal '' {q : PrimeSpectrum C | q.asIdeal ∈ minimalPrimes C} := by
    ext p
    refine ⟨fun hp ↦ ⟨⟨p, hp.isPrime⟩, hp, rfl⟩, ?_⟩
    rintro ⟨q, hq, rfl⟩
    exact hq
  rw [hcongr]
  conv_rhs => rw [himage]
  rw [finsum_mem_image (fun q _ q' _ h ↦ PrimeSpectrum.ext h)]

/-- **The order of vanishing over the minimal primes of a reduced ring**, as an identity of
integers: `ord_C(x) = ∑_{𝔮 minimal} ord_{C/𝔮}(x)`. -/
theorem ord_toNat_eq_finsum_minimalPrimes [IsReduced C] (hdim : ringKrullDim C = 1) {x : C}
    (hx : x ∈ nonZeroDivisors C) :
    ((Ring.ord C x).toNat : ℤ) =
      ∑ᶠ p ∈ minimalPrimes C, ((Ring.ord (C ⧸ p) (Ideal.Quotient.mk p x)).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 C := Ring.krullDimLE_iff.mpr (by rw [hdim]; exact_mod_cast le_rfl)
  have hfin := minimalPrimes.finite_of_isNoetherianRing C
  have h := ord_eq_finsum_minimalPrimes hdim hx
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h ⊢
  have htop : ∀ p ∈ hfin.toFinset, Ring.ord (C ⧸ p) (Ideal.Quotient.mk p x) ≠ ⊤ := by
    refine ENat.sum_ne_top.mp ?_
    rw [← h]
    exact Ring.ord_ne_top hx
  rw [h, ENat.toNat_sum htop, Nat.cast_sum]

end Stacks.Chow

end
