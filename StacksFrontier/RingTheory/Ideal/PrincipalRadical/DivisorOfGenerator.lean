module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# A divisibility consequence of Krull's principal ideal theorem

Let `R` be a Noetherian local domain, `p` a nonzero prime ideal contained in the radical of a
principal ideal `(h)`, and `g` an element of the maximal ideal not lying in `p`. If an element `τ`
of `(h)` is divisible by `g`, then `τ` already lies in `𝔪 · (h)`: writing `τ = u h`, the factor `u`
cannot be a unit, for otherwise `g` would divide `h`, so `p ⊆ √(g)` and a minimal prime `Q` of
`(g)` would contain the chain `0 ⊊ p ⊊ Q`, against Krull's principal ideal theorem.

This is the commutative algebra behind the step "the section `s_i` has a zero at `x_i`" in the
proof of [Stacks, Tag 0AXA].

## Main results

* `IsLocalRing.mem_maximalIdeal_mul_span_of_dvd`: the statement above.

## References

* [Stacks Project, Tag 0AXA](https://stacks.math.columbia.edu/tag/0AXA)
* [Stacks Project, Tag 00KV](https://stacks.math.columbia.edu/tag/00KV)
-/

@[expose] public section

namespace IsLocalRing

/-- **A multiple of a generator by a factor from the maximal ideal.** In a Noetherian local domain
let `p ≠ 0` be a prime ideal with `p ⊆ √(h)`, and let `g ∈ 𝔪` with `g ∉ p`. Every `τ ∈ (h)`
divisible by `g` lies in `𝔪 · (h)`.

Write `τ = h u`. If `u` were a unit, then `g ∣ h`, so `p ⊆ √(h) ⊆ √(g)`; a minimal prime `Q` over
`(g)` (it exists as `g` is not a unit) then contains `p`, strictly since `g ∈ Q ∖ p`, and `0 ⊊ p`;
so `Q` has height at least two, contradicting Krull's principal ideal theorem
(`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`). Hence `u ∈ 𝔪`. -/
theorem mem_maximalIdeal_mul_span_of_dvd {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] {p : Ideal R} [p.IsPrime] (hp : p ≠ ⊥) {h g τ : R}
    (hpK : p ≤ (Ideal.span {h}).radical) (hg : g ∈ maximalIdeal R) (hgp : g ∉ p)
    (hτ : τ ∈ Ideal.span {h}) (hgτ : g ∣ τ) :
    τ ∈ maximalIdeal R * Ideal.span {h} := by
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hτ
  by_cases hu : u ∈ maximalIdeal R
  · exact Ideal.mul_mem_mul hu (Ideal.mem_span_singleton_self h)
  exfalso
  have hunit : IsUnit u := of_not_not fun hnu => hu ((mem_maximalIdeal u).mpr hnu)
  have hgh : g ∣ h := hunit.dvd_mul_left.mp hgτ
  have hspan : Ideal.span {g} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (mem_maximalIdeal g).mp hg
  obtain ⟨Q, hQ⟩ := Ideal.nonempty_minimalPrimes hspan
  have := hQ.isPrime
  have hgQ : g ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self g)
  have hpQ : p ≤ Q := hpK.trans <|
    (Ideal.radical_mono (Ideal.span_singleton_le_span_singleton.mpr hgh)).trans
      (this.radical_le_iff.mpr hQ.1.2)
  have h₁ := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hp)
  have h₂ := Ideal.height_add_one_le_of_lt_of_isPrime
    (lt_of_le_of_ne hpQ fun he => hgp (he ▸ hgQ))
  have h₃ := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {g}) Q hQ
  have h₄ : (2 : ℕ∞) ≤ Q.height :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal R).height + 1 + 1 := by
        gcongr
        exact zero_le
      _ ≤ p.height + 1 := by gcongr
      _ ≤ Q.height := h₂
  exact absurd (h₄.trans h₃) (by decide)

end IsLocalRing
