module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocityFraction
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.ReciprocityNonzerodivisors
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.KrullDimOne

/-!
# The Key Lemma for the canonical tame symbol

Stacks 0EAX, the Key Lemma, says that for a two-dimensional Noetherian local domain `A` with
fraction field `K` and `f, g ∈ K^*` the orders of vanishing of the tame symbols
`∂_{A_𝔮}(f, g)` along `A/𝔮`, summed over the height-one primes `𝔮` of `A`, give zero.

Three pieces of this were already in place and did not meet.

* `Stacks.Chow.fracTameSymbolOrderAt_finsum_eq_zero_of_forall_nonZeroDivisors` reduces
  Stacks 0EAX to Stacks 0EAW — the same sum for a pair of nonzerodivisors of `A` — for *any*
  family of tame symbols `∂_{A_𝔮}` in the sense of Stacks 0EAH, supplied as a family of terms
  of `Stacks.Chow.RegularTameSymbol`.
* `AlgebraicGeometry.sum_ord_heightOneSymbol_eq_zero` is Stacks 0EAW, proved unconditionally,
  but for *one specific* symbol: `AlgebraicGeometry.heightOneSymbol`, the symbol of Stacks 02PZ
  on the localization `A_𝔮`.
* `Stacks.Chow.regularTameSymbolOfKrullDimOne` exhibits that specific symbol as a term of
  `Stacks.Chow.RegularTameSymbol`, which is what the reduction consumes.

The module documentation of
`StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.TameSymbolReciprocityFraction` records that the
missing step was exactly this: for an arbitrary term of `Stacks.Chow.RegularTameSymbol` the sum
cannot vanish by any argument available here, since the source declines to claim uniqueness of
the datum. Specializing the family to the canonical symbol removes that obstacle, because
Stacks 0EAW is proved for it.

So this file joins the three and proves Stacks 0EAX. Nothing is assumed beyond the hypotheses of
the source, and no hypothesis stands in for a missing result.

## Main definitions

* `Stacks.Chow.canonicalHeightOneSymbol` — the tame symbol of Stacks 0EAH on `A_𝔮` given by
  Stacks 02PZ, for a height-one prime `𝔮` of a Noetherian ring.

## Main results

* `Stacks.Chow.ringKrullDim_localization_heightOnePrime` — the localization at a height-one prime
  is one-dimensional.
* `Stacks.Chow.finsum_tameSymbolOrderAt_canonical_eq_zero` — **Stacks 0EAW for the canonical
  symbol**, in the shape the reduction to Stacks 0EAX consumes.
* `Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero` — **Stacks 0EAX**, the Key Lemma.

## Implementation notes

`AlgebraicGeometry.sum_ord_heightOneSymbol_eq_zero` sums over `{q : Ideal A // q.IsPrime ∧
q.height = 1}` while the reduction sums over `Stacks.Chow.HeightOnePrime A`, which is
`{p : PrimeSpectrum A // p.asIdeal.height = 1}`; the two index types are equivalent by
`Stacks.Chow.heightOnePrimeEquivIdeal` and `finsum_comp_equiv` transports the sum. The summands
then agree by `rfl`: `Stacks.Chow.tameSymbolOrderAt` of the canonical symbol and the summand of
Stacks 0EAW are both `Ring.ordFrac` of the same `AlgebraicGeometry.moduleSymbol`, and the
`Ring.KrullDimLE` and `Ideal.IsPrime` witnesses that the two spellings carry are propositions.

## References

* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0EAW](https://stacks.math.columbia.edu/tag/0EAW)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public section

open IsLocalRing

universe u

namespace Stacks.Chow

section Canonical

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- **The localization at a height-one prime is one-dimensional.** Its Krull dimension is the
height of the prime. -/
theorem ringKrullDim_localization_heightOnePrime (p : HeightOnePrime A) :
    ringKrullDim (Localization.AtPrime p.1.asIdeal) = 1 :=
  (IsLocalization.AtPrime.ringKrullDim_eq_height p.1.asIdeal
      (Localization.AtPrime p.1.asIdeal)).trans
    (congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) p.2)

/-- **The tame symbol of Stacks 0EAH at a height-one prime of a Noetherian ring.** The
localization `A_𝔮` is a one-dimensional Noetherian local ring, so
`Stacks.Chow.regularTameSymbolOfKrullDimOne` gives it the tame symbol of Stacks 0EAH on pairs of
nonzerodivisors. Its value is the symbol of Stacks 02PZ, which is
`AlgebraicGeometry.heightOneSymbol`. -/
noncomputable def canonicalHeightOneSymbol (p : HeightOnePrime A) :
    RegularTameSymbol (Localization.AtPrime p.1.asIdeal) :=
  regularTameSymbolOfKrullDimOne (ringKrullDim_localization_heightOnePrime p)

/-- **Stacks 0EAW for the canonical tame symbol.** The reciprocity sum of Stacks 0EAW, indexed by
`Stacks.Chow.HeightOnePrime` and formed from `Stacks.Chow.canonicalHeightOneSymbol`, vanishes.
This is `AlgebraicGeometry.sum_ord_heightOneSymbol_eq_zero` reindexed: the summands agree because
`Stacks.Chow.canonicalHeightOneSymbol` evaluates to `AlgebraicGeometry.heightOneSymbol`. -/
theorem finsum_tameSymbolOrderAt_canonical_eq_zero [IsLocalRing A]
    (hdim : ringKrullDim A = 2) (x y : nonZeroDivisors A) :
    ∑ᶠ p : HeightOnePrime A, tameSymbolOrderAt hdim p (canonicalHeightOneSymbol p) x y = 0 := by
  obtain ⟨hquot, hsum⟩ := AlgebraicGeometry.sum_ord_heightOneSymbol_eq_zero hdim x.2 y.2
  rw [← finsum_comp_equiv (heightOnePrimeEquivIdeal (A := A))] at hsum
  exact (finsum_congr fun p => rfl).trans hsum

/-- **Stacks Project, Tag 0EAX: the Key Lemma.** Let `A` be a two-dimensional Noetherian local
domain with fraction field `K` and let `f, g ∈ K^*`. Then

`∑_{height(𝔮) = 1} ord_{A/𝔮}(∂_{A_𝔮}(f, g)) = 0`,

the sum being over the height-one primes of `A`, with `∂_{A_𝔮}` the tame symbol of Stacks 0EAH on
the one-dimensional Noetherian local ring `A_𝔮`
(`Stacks.Chow.canonicalHeightOneSymbol`). Only finitely many primes contribute, by
`Stacks.Chow.finite_fracTameSymbolOrderAt_support`, which is the first form the source gives the
statement in.

The proof is the source's:
`Stacks.Chow.fracTameSymbolOrderAt_finsum_eq_zero_of_forall_nonZeroDivisors` expands a pair of
fractions into four pairs of nonzerodivisors of `A`, and Stacks 0EAW
(`Stacks.Chow.finsum_tameSymbolOrderAt_canonical_eq_zero`) kills each of the four. -/
@[stacks 0EAX]
theorem finsum_fracTameSymbolOrderAt_canonical_eq_zero [IsDomain A] [IsLocalRing A]
    (hdim : ringKrullDim A = 2) (f g : (FractionRing A)ˣ) :
    ∑ᶠ p : HeightOnePrime A,
      fracTameSymbolOrderAt hdim p (canonicalHeightOneSymbol p) f g = 0 :=
  fracTameSymbolOrderAt_finsum_eq_zero_of_forall_nonZeroDivisors hdim canonicalHeightOneSymbol
    (fun x y => finsum_tameSymbolOrderAt_canonical_eq_zero hdim x y) f g

end Canonical

end Stacks.Chow

end
