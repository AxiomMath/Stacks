module

public import Mathlib.RingTheory.Localization.AsSubring
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# A principal ideal of a normal domain is cut out at the height-one primes

Let `R` be a Noetherian normal domain and `a ∈ R` nonzero. This file proves that an element of
`R` which lies in `a R_𝔭` for every prime `𝔭` of height one already lies in `a R`.

This is the step that the affine computation in the proof of
[Stacks, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7) quotes as Algebra, Lemma 031T
when it writes
`𝔭₁^(e₁ + e'₁) ∩ … ∩ 𝔭ₙ^(eₙ + e'ₙ) = (r r')`: the intersection of the symbolic powers of the
minimal primes over a principal ideal, with exponents the valuations, is that principal ideal
again. The content of that equality is exactly the statement proved here, since in the discrete
valuation ring `R_𝔭` the symbolic power `𝔭^(e)` extends to `a R_𝔭` when `e` is the valuation of
`a`; the statement is given in the elementary `∃ y s, s ∉ 𝔭 ∧ s x = a y` form so that no
discrete valuation ring structure has to be produced in order to use it.

## Main results

* `Ideal.mem_span_singleton_of_forall_height_one`: an element regular against `a` at every
  height-one prime lies in `a R`.
* `Ideal.mem_span_singleton_iff_forall_height_one`: the resulting characterization of `a R`.

## Implementation notes

The proof is item (2) of Tag 031T — in the development as the middle conjunct of
`associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot` — applied to the
element `x / a` of the fraction field: the hypothesis says precisely that `x / a` has, at each
height-one prime, a denominator outside that prime, which is membership in
`Localization.subalgebra.ofField`, and the conclusion of Tag 031T item (2) is that the
intersection of those subalgebras is `R` itself.

Only `IsIntegrallyClosed R` is assumed for normality, following the development's spelling of
Definition 0309 as `IsDomain` plus `IsIntegrallyClosed`.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
-/

@[expose] public section

universe u

namespace Ideal

/-- In a Noetherian normal domain, an element `x` which becomes divisible by a nonzero `a` in
every localization at a prime of height one is already divisible by `a`.

Divisibility in `R_𝔭` is written out as `∃ y s, s ∉ 𝔭 ∧ s * x = a * y`, which is what it comes
to in a domain. This is the content of item (1) of Stacks Tag 031T for the ideal `a R`, in the
form in which the affine step of Tag 0BD7 uses it. -/
theorem mem_span_singleton_of_forall_height_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {a x : R} (ha : a ≠ 0)
    (h : ∀ p : Ideal R, p.IsPrime → p.height = 1 → ∃ y s : R, s ∉ p ∧ s * x = a * y) :
    x ∈ Ideal.span {a} := by
  classical
  have hane : algebraMap R (FractionRing R) a ≠ 0 := by simpa using ha
  have hmem : algebraMap R (FractionRing R) x * (algebraMap R (FractionRing R) a)⁻¹ ∈
      (⨅ p : PrimeSpectrum R, ⨅ _ : p.asIdeal.height = 1,
        Localization.subalgebra.ofField (FractionRing R) _
          p.asIdeal.primeCompl_le_nonZeroDivisors) := by
    refine Algebra.mem_iInf.mpr fun p => Algebra.mem_iInf.mpr fun hp => ?_
    obtain ⟨y, s, hs, hsx⟩ := h p.asIdeal p.isPrime hp
    have hsne : algebraMap R (FractionRing R) s ≠ 0 := by
      simp [show s ≠ 0 from fun hc => hs (hc ▸ p.asIdeal.zero_mem)]
    refine ⟨y, s, hs, ?_⟩
    have hkey : algebraMap R (FractionRing R) s * algebraMap R (FractionRing R) x =
        algebraMap R (FractionRing R) a * algebraMap R (FractionRing R) y := by
      rw [← map_mul, ← map_mul, hsx]
    field_simp
    linear_combination hkey
  rw [(associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot
    (FractionRing R)).2.1] at hmem
  obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hmem
  refine Ideal.mem_span_singleton.mpr ⟨r, IsFractionRing.injective R (FractionRing R) ?_⟩
  rw [map_mul, hr]
  field_simp

/-- A nonzero principal ideal of a Noetherian normal domain is cut out by divisibility at the
primes of height one. -/
theorem mem_span_singleton_iff_forall_height_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {a x : R} (ha : a ≠ 0) :
    x ∈ Ideal.span {a} ↔
      ∀ p : Ideal R, p.IsPrime → p.height = 1 → ∃ y s : R, s ∉ p ∧ s * x = a * y :=
  ⟨fun hx p hp _ => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    exact ⟨y, 1, fun hc => hp.ne_top ((Ideal.eq_top_iff_one p).mpr hc), by ring⟩,
   mem_span_singleton_of_forall_height_one ha⟩

end Ideal

end
