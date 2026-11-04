module

public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.RestrictedDivisors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local multiplicity comparison at a fibre of a family over the projective line

Let `A` be a Noetherian local ring, `I ⊆ A` an ideal with `dim A/I = 1` and `t ∈ A` an element with
`dim A/(t, I) ≤ 0`. If the maximal ideal of `A` is not an associated prime of `A/I`, then `t` is a
nonzerodivisor on `A/I`, so Stacks Tag 02QG
(`AlgebraicGeometry.length_quotient_span_sup_eq_sum_minimalPrimes`) gives
`length_A A/(t, I) = ∑ length_A A/(t, qᵢ) · length_{A_{qᵢ}} (A/I)_{qᵢ}`, the sum running over the
minimal primes of `I`. This is the local form of the multiplicity comparison in Stacks Tag 02S5 for
a closed subscheme `Z ⊆ X ×_S 𝐏¹_S` cut out by `I`, at the local ring `A = 𝒪_{X ×_S 𝐏¹_S, ξ}` of a
point `ξ` of the zero section, with `t` the coordinate of `𝐏¹` at zero.

The hypothesis is on *associated* points rather than on *embedded* points. The source asks only
that embedded points of `Z` avoid the two fibres or have small delta-dimension, and read literally
that is not enough: nothing then prevents `ξ` from being the generic point of a component, and the
quotient `A/I` can fail to have depth one.

## Main results

* `Stacks.Chow.isSMulRegular_quotient_of_notMem_associatedPrimes` — if the maximal ideal is not
  an associated prime of `A/I` and `A/(t, I)` has Krull dimension at most zero, then `t` is a
  nonzerodivisor on `A/I`.
* `Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes` — the
  resulting length identity, the local form of the multiplicity comparison in Tag 02S5.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
-/

@[expose] public section

open IsLocalRing

namespace Stacks.Chow

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- If the maximal ideal of a Noetherian local ring `R` is not an associated prime of `R ⧸ I` and
the quotient `R ⧸ (x, I)` has Krull dimension at most zero, then `x` is a nonzerodivisor on
`R ⧸ I`. -/
theorem isSMulRegular_quotient_of_notMem_associatedPrimes (x : R) (I : Ideal R)
    (hI : maximalIdeal R ∉ associatedPrimes R (R ⧸ I))
    (hx : ringKrullDim (R ⧸ (Ideal.span {x} ⊔ I)) ≤ 0) :
    IsSMulRegular (R ⧸ I) x := by
  by_contra hreg
  have hmem : x ∈ ⋃ p ∈ associatedPrimes R (R ⧸ I), (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R (R ⧸ I)]
    exact hreg
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hmem
  have hIp : I ≤ p := by
    have h := hp.annihilator_le
    rwa [Submodule.annihilator_top, Ideal.annihilator_quotient] at h
  have hJp : Ideal.span {x} ⊔ I ≤ p :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hxp) hIp
  have hJ : Ideal.span {x} ⊔ I ≠ ⊤ := fun h ↦ hp.isPrime.ne_top (top_le_iff.mp (h ▸ hJp))
  have : Nontrivial (R ⧸ (Ideal.span {x} ⊔ I)) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have hdim : Module.supportDim R (R ⧸ (Ideal.span {x} ⊔ I)) = 0 := by
    rw [Module.supportDim_quotient_eq_ringKrullDim]
    exact le_antisymm hx ringKrullDim_nonneg_of_nontrivial
  have hsupp := support_of_supportDim_eq_zero (R := R) (N := R ⧸ (Ideal.span {x} ⊔ I)) hdim
  have hpsupp : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈
      Module.support R (R ⧸ (Ideal.span {x} ⊔ I)) := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    exact hJp
  rw [hsupp, PrimeSpectrum.zeroLocus_eq_singleton] at hpsupp
  have hpm : p = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hpsupp
  exact hI (hpm ▸ hp)

/-- The local multiplicity comparison underlying Stacks Tag 02S5: for a one-dimensional quotient
`R ⧸ I` of a Noetherian local ring whose maximal ideal is not an associated prime, and an element
`x` for which `R ⧸ (x, I)` has Krull dimension at most zero, the colength of `(x, I)` is the sum
over the minimal primes `q` above `I` of the colength of `(x, q)` times the length of `R ⧸ I`
localized at `q`. -/
@[ega "IV 21.10.17.7" "(x), special case"]
theorem length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes
    (x : R) (I : Ideal R) (hI : maximalIdeal R ∉ associatedPrimes R (R ⧸ I))
    (hdim : ringKrullDim (R ⧸ I) = 1)
    (hx : ringKrullDim (R ⧸ (Ideal.span {x} ⊔ I)) ≤ 0) :
    Module.length R (R ⧸ (Ideal.span {x} ⊔ I)) =
      ∑ᶠ q ∈ {q : PrimeSpectrum R | q.asIdeal ∈ I.minimalPrimes},
        Module.length R (R ⧸ (Ideal.span {x} ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl (R ⧸ I)) :=
  AlgebraicGeometry.length_quotient_span_sup_eq_sum_minimalPrimes x I
    (isSMulRegular_quotient_of_notMem_associatedPrimes x I hI hx) hdim

end Stacks.Chow

end
