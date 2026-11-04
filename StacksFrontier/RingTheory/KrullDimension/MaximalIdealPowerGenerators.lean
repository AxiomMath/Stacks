module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# A power of the maximal ideal needs at least `dim(A)` generators

Let `(A, 𝔪, κ)` be a Noetherian local ring and let `n ≥ 1`. Then

`dim(A) ≤ dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹)`.

The right-hand side is the minimal number of generators of the ideal `𝔪ⁿ`, and the inequality is
Krull's height theorem applied to `𝔪ⁿ`: that ideal has the same minimal primes as `𝔪`, namely
`𝔪` alone, so its height is the dimension of `A`.

At `n = 1` this is the familiar bound `dim(A) ≤ dim_κ(𝔪/𝔪²)` relating the Krull dimension to the
embedding dimension, which Mathlib has as
`IsLocalRing.ringKrullDim_le_spanFinrank_maximalIdeal` together with
`IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`. For `n ≥ 2` the graded piece
`𝔪ⁿ/𝔪ⁿ⁺¹` is strictly larger than a line as soon as `dim(A) ≥ 2`, and that is what the
statement below supplies; no bound on the growth of the Hilbert function of the associated
graded ring is needed for it.

## Main results

* `Stacks.KrullDimension.ringKrullDim_le_finrank_maximalIdealPow_quotient` — the inequality
  `dim(A) ≤ dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹)` for `n ≥ 1`.
* `Stacks.KrullDimension.two_le_finrank_maximalIdealPow_quotient` — its value at a ring of
  dimension two: `dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) ≥ 2` for every `n ≥ 1`.

## Implementation notes

The graded piece is spelled `𝔪ⁿ ⧸ (𝔪 • ⊤)`, the quotient of the ideal `𝔪ⁿ` regarded as an
`A`-module by the submodule `𝔪 · 𝔪ⁿ`; this is the spelling of
`IsLocalRing.spanFinrank_eq_finrank_quotient`, which identifies its dimension over
`A ⧸ 𝔪` with the minimal number of generators of `𝔪ⁿ`.

That the height of `𝔪ⁿ` is the height of `𝔪` is read off the description of the height as the
infimum of the heights of the minimal primes, together with `Ideal.radical_minimalPrimes` and
`Ideal.radical_pow`: the radical of `𝔪ⁿ` is `𝔪`.

## References

* [Stacks Project, Tag 00KQ](https://stacks.math.columbia.edu/tag/00KQ)
-/

@[expose] public section

universe u

open IsLocalRing

namespace Stacks.KrullDimension

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- **A power of the maximal ideal of a Noetherian local ring needs at least `dim(A)`
generators**, in the form `dim(A) ≤ dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹)` for `n ≥ 1`.

The only prime of `A` containing `𝔪ⁿ` is `𝔪`, so `𝔪ⁿ` has height `dim(A)`; Krull's height
theorem bounds that height by the minimal number of generators of `𝔪ⁿ`, which over a local ring
is the dimension of `𝔪ⁿ/𝔪 · 𝔪ⁿ` over the residue field. -/
theorem ringKrullDim_le_finrank_maximalIdealPow_quotient {n : ℕ} (hn : n ≠ 0) :
    ringKrullDim A ≤
      (((Module.finrank (A ⧸ maximalIdeal A)
        ((maximalIdeal A ^ n : Ideal A) ⧸
          (maximalIdeal A • ⊤ :
            Submodule A (maximalIdeal A ^ n : Ideal A))) : ℕ∞) : WithBot ℕ∞)) := by
  have hne : (maximalIdeal A ^ n : Ideal A) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top (Ideal.pow_le_self hn)
  have hrad : (maximalIdeal A ^ n : Ideal A).radical = maximalIdeal A := by
    rw [Ideal.radical_pow _ hn, (maximalIdeal.isMaximal A).isPrime.radical]
  rw [← IsLocalRing.spanFinrank_eq_finrank_quotient _
    (Ideal.fg_of_isNoetherianRing (maximalIdeal A ^ n : Ideal A))]
  calc ringKrullDim A = (((maximalIdeal A).height : ℕ∞) : WithBot ℕ∞) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ = ((((maximalIdeal A ^ n : Ideal A).radical).height : ℕ∞) : WithBot ℕ∞) := by rw [hrad]
    _ = (((maximalIdeal A ^ n : Ideal A).height : ℕ∞) : WithBot ℕ∞) := by
        rw [Ideal.height_eq_inf_minimalPrimes, Ideal.height_eq_inf_minimalPrimes,
          Ideal.radical_minimalPrimes]
    _ ≤ (((maximalIdeal A ^ n : Ideal A).spanFinrank : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast Ideal.height_le_spanFinrank _ hne

/-- **Over a Noetherian local ring of dimension two every graded piece `𝔪ⁿ/𝔪ⁿ⁺¹` with `n ≥ 1`
has dimension at least two.** This is
`Stacks.KrullDimension.ringKrullDim_le_finrank_maximalIdealPow_quotient` at `dim(A) = 2`. -/
theorem two_le_finrank_maximalIdealPow_quotient (hdim : ringKrullDim A = 2) {n : ℕ}
    (hn : n ≠ 0) :
    2 ≤ Module.finrank (A ⧸ maximalIdeal A)
      ((maximalIdeal A ^ n : Ideal A) ⧸
        (maximalIdeal A • ⊤ : Submodule A (maximalIdeal A ^ n : Ideal A))) := by
  have key := ringKrullDim_le_finrank_maximalIdealPow_quotient (A := A) hn
  rw [hdim] at key
  exact_mod_cast WithBot.coe_le_coe.mp (show ((2 : ℕ∞) : WithBot ℕ∞) ≤ _ from key)

end Stacks.KrullDimension

end
