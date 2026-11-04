module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Krull's height theorem in relative form: chains of primes between an ideal and a prime

Let `R` be a Noetherian ring, let `I` and `J` be ideals of `R`, and let `q` be a prime minimal
over `I + J`. Then the height of `q / I` in `R / I` is at most the minimal number of generators
of `J`; equivalently, every chain of primes between `I` and `q` has length at most that number.

The proof is a reduction to Krull's height theorem in `R / I`. Because `R → R / I` is surjective
with kernel `I`, the primes of `R / I` minimal over `J / I` are exactly the images of the primes
of `R` minimal over `I + J`; so `q / I` is minimal over `J / I`. Krull's height theorem in `R / I`
bounds the height of `q / I` by the minimal number of generators of `J / I`, and the image of a
generating set of `J` generates `J / I`, so that number is at most the minimal number of
generators of `J`.

## Main results

* `Stacks.IdealTheory.RelativeHeight.solution`: for `q` minimal over `I ⊔ J` in a Noetherian ring,
  `(q.map (Ideal.Quotient.mk I)).height ≤ J.spanRank.toENat`.

## Implementation notes

The reduction step is the converse of `Ideal.mem_minimalPrimes_sup`, which Mathlib has only in
the direction from `R ⧸ I` back to `R`. Both directions are instances of the same computation of
`(J.map f).minimalPrimes` for a surjective `f`, so the converse is proved here rather than the
correspondence being redone by hand; it needs no Noetherian hypothesis.

The source's proof localizes at `p` and applies [StackProject 00KQ] to `R_p`, using the
correspondence between the primes of `R_p` and the primes of `R` contained in `p`. Here the
quotient by `I` replaces the localization at `p`, since the conclusion is a statement about the
primes *above* `I`; the induction on the number of generators that 00KQ performs is available
upstream as Krull's height theorem itself, so it is used directly and 00KQ is not invoked.

## References

* [StackProject 0BBZ](https://stacks.math.columbia.edu/tag/0BBZ)
-/

namespace Stacks.IdealTheory.RelativeHeight

/-- If a prime `q` of `R` is minimal over `I ⊔ J`, then `q / I` is minimal over `J / I` in
`R ⧸ I`.

This is the converse of `Ideal.mem_minimalPrimes_sup`; both directions follow from
`Ideal.minimalPrimes_map_of_surjective`, which computes the minimal primes over `J.map f`, for
`f` surjective, as the images of the minimal primes over `J ⊔ RingHom.ker f`. -/
private theorem map_quotientMk_mem_minimalPrimes_map_of_mem_minimalPrimes_sup {R : Type*}
    [CommRing R] {I J q : Ideal R} (hq : q ∈ (I ⊔ J).minimalPrimes) :
    q.map (Ideal.Quotient.mk I) ∈ (J.map (Ideal.Quotient.mk I)).minimalPrimes := by
  rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective]
  exact Set.mem_image_of_mem _ (by rwa [Ideal.mk_ker, sup_comm])

/-- **Stacks 0BBZ (2), Krull's height theorem in relative form.** Let `R` be a Noetherian ring
and let `I`, `J` be ideals of `R`. If a prime `q` is minimal over `I + J`, then the height of
`q / I` in `R / I` is at most the minimal number of generators of `J`; equivalently, every chain
of primes between `I` and `q` has length at most that number. -/
@[ega "0 16.3.2" "more general"]
public theorem solution {R : Type*}
    [CommRing R] [IsNoetherianRing R] {I J q : Ideal R} (hq : q ∈ (I ⊔ J).minimalPrimes) :
    (q.map (Ideal.Quotient.mk I)).height ≤ J.spanRank.toENat :=
  (Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ _
      (map_quotientMk_mem_minimalPrimes_map_of_mem_minimalPrimes_sup hq)).trans
    (OrderHomClass.mono Cardinal.toENat (Ideal.spanRank_map_le _ J))

end Stacks.IdealTheory.RelativeHeight

/-!
# Krull's height theorem in relative form: chains of primes between an ideal and a prime

Let `R` be a Noetherian ring, let `I` and `J` be ideals of `R`, and let `q` be a prime minimal
over `I + J`. Then the height of `q / I` in `R / I` is at most the minimal number of generators
of `J`. Read with `I = p` prime and `J = (f₁, …, f_r)`, this says that every chain of primes
`p = p₀ ⊂ p₁ ⊂ ⋯ ⊂ p_n = q` has length `n ≤ r` whenever `q` is minimal over `(p, f₁, …, f_r)`:
adjoining `r` elements to a prime moves at most `r` steps up the poset of primes. It is the
relative form of Krull's height theorem, and the `r`-element generalization of Krull's principal
ideal theorem in the shape Mathlib gives it, `Ideal.map_height_le_one_of_mem_minimalPrimes`.

## Main results

* `Ideal.map_height_le_spanRank_toENat_of_mem_minimalPrimes_sup`: for `q` minimal over `I ⊔ J`
  in a Noetherian ring, `(q.map (Ideal.Quotient.mk I)).height ≤ J.spanRank.toENat`.

## Implementation notes

The source has two items, and only the second is stated here. Item (1), "a prime minimal over
`(f₁, …, f_r)` has height `≤ r`", is Krull's height theorem, which Mathlib has as
`Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes`, and in the form with a finite set of
generators as `Ideal.height_le_card_of_mem_minimalPrimes_span_finset`; restating it would
duplicate a Mathlib lemma, and it is the case `I = ⊥` of the statement below up to the
isomorphism `R ⧸ ⊥ ≅ R`.

Three departures from the source's form, none of them a weakening.

The source's `p` prime is here an arbitrary ideal `I`. Only `I ≤ q` is used, which minimality of
`q` over `I ⊔ J` already gives, so primality of `I` would be a dead hypothesis. This is the same
generality as the `r = 1` sibling `Ideal.map_height_le_one_of_mem_minimalPrimes`. (In the chain
phrasing of Stacks 00KV, "no prime strictly between `p` and `q`", primality of `p` cannot be
dropped: `(ab) < (a) < (a, c)` in `k[a, b, c]` with `(a, c)` minimal over `(ab) + (c)`. The height
phrasing used here is the one that generalizes, since it bounds chains of primes *containing* `I`,
of which `(a) < (a, c)` over `(ab)` is one of length `1`.)

The source's `r` elements `f₁, …, f_r` are here an arbitrary ideal `J`, and the bound is
`J.spanRank.toENat`, the minimal cardinality of a generating set of `J`, as in Mathlib's
`Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes`. Taking `J = Ideal.span s` recovers the
source's form, since `(Ideal.span s).spanRank ≤ #s` by `Submodule.spanRank_span_le_card`; the
generators themselves are never used, only their number, so the ideal is the right hypothesis.

"Every chain of primes between `I` and `q` has length at most `r`" is spelled as a bound on the
height of `q / I`, matching the `r = 1` sibling. The two agree: `Ideal.height` of a prime is
`Order.height` in the prime spectrum by `PrimeSpectrum.height_eq_orderHeight`, that is, the
supremum of the lengths of chains of primes descending from it, and the primes of `R / I` below
`q / I` are exactly the primes of `R` between `I` and `q`.

Faithfulness. (1) Every hypothesis is used by the conclusion. `IsNoetherianRing R` is live: in a
valuation domain with value group `ℤ ×ₗ ℤ` the maximal ideal `m` is generated by an element of
value `(0, 1)`, hence is minimal over a principal ideal, while `⊥ ⊂ p ⊂ m` for
`p = {x : v(x) ≥ (1, 0)}` gives it height `2`. Minimality of `q` over `I ⊔ J` is the content: for
`R = k[a, b]`, `I = ⊥`, `J = (a)` the prime `q = (a, b)` contains `I ⊔ J` without being minimal
over it and has height `2 > 1 = J.spanRank`. (2) The base is the source's: `I`, `J`
and `q` are ideals of `R` and `spanRank` is computed over `R`; the quotient `R ⧸ I` appears only
because the height measured is that of `q / I`, which is what "chains between `I` and `q`" means.
(3) The source names no canonical map beyond the quotient map, which is pinned as
`Ideal.Quotient.mk I`, and the ideal the source writes `(p, f₁, …, f_r)` is pinned as `I ⊔ J`.
(4) The instantiation is not degenerate and the bound is attained: for `R = k[a, b, c]`, `I = (a)`
and `J = (b)`, the prime `q = (a, b)` is minimal over `I ⊔ J` and `q / I = (b)` has height
`1 = J.spanRank.toENat` in `R ⧸ I ≅ k[b, c]`.

## References

* [StacksProject 0BBZ](https://stacks.math.columbia.edu/tag/0BBZ)
-/

@[expose] public section

/-- **Stacks 0BBZ (2), Krull's height theorem in relative form.** Let `R` be a Noetherian ring
and let `I`, `J` be ideals of `R`. If a prime `q` is minimal over `I + J`, then the height of
`q / I` in `R / I` is at most the minimal number of generators of `J`; equivalently, every chain
of primes between `I` and `q` has length at most that number. -/
@[stacks 0BBZ "Item (2), for an arbitrary ideal in place of the prime; item (1) is Mathlib's \
`Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes`.",
  ega "0 16.3.1" "b ⇒ a",
  ega "0 16.3.2" "more general"]
public theorem Ideal.map_height_le_spanRank_toENat_of_mem_minimalPrimes_sup {R : Type*}
    [CommRing R] [IsNoetherianRing R] {I J q : Ideal R} (hq : q ∈ (I ⊔ J).minimalPrimes) :
    (q.map (Ideal.Quotient.mk I)).height ≤ J.spanRank.toENat :=
    by exact Stacks.IdealTheory.RelativeHeight.solution (R := R) hq

end

/-!
# Primes minimal over `(p, x)`: the chain form of Krull's principal ideal theorem

Let `R` be a Noetherian ring, let `x ∈ R` and let `p ⊆ R` be a prime ideal. If a prime `q` is
minimal over `p + (x)`, then no prime lies strictly between `p` and `q`.

Passing to `R / p`, Krull's principal ideal theorem applied to the principal ideal generated by
the image of `x` bounds the height of `q / p` by `1`. A prime `r` with `p < r < q` would give a
prime `r / p` strictly below `q / p`, hence of height `0`; but `R / p` is a domain and
`r / p ≠ 0`, so `⊥ < r / p` forces the height of `r / p` to be at least `1`.

## Main results

* `Stacks.IdealTheory.NoIntermediatePrime.solution`: for `p` prime and `q` minimal over `p ⊔ (x)`,
  no prime `r` satisfies `p < r < q`.

## Implementation notes

Both strict inequalities in `R / p` — the one below `q / p` and the one below `r / p` — are the
same step, namely that `Ideal.map (Ideal.Quotient.mk p)` is an order embedding on the ideals
containing `p`. That step is factored out as
`Stacks.IdealTheory.NoIntermediatePrime.map_mk_lt_map_mk_iff`, whose second use takes `I = p` and
reads `⊥ < r / p` after `Ideal.map_quotient_self`.

The height of `r / p` is bounded below without any finiteness hypothesis by
`Ideal.height_add_one_le_of_lt_of_isPrime`, rather than by the strict monotonicity of
`Ideal.height`, which would require a `FiniteHeight` instance on `r / p`.

The source's proof localizes at `p` and applies [StackProject 00KK] to `R_p` (for item (1)) and to
`(R / p)_q` (for item (2)); the induction that argument performs is already available upstream as
`Ideal.map_height_le_one_of_mem_minimalPrimes`, so it is used directly here.

## References

* [StackProject 00KV](https://stacks.math.columbia.edu/tag/00KV)
-/

namespace Stacks.IdealTheory.NoIntermediatePrime

/-- For ideals containing `p`, taking images under `R → R ⧸ p` reflects and preserves strict
inclusions: it is an order embedding on the ideals above `p`. -/
private theorem map_mk_lt_map_mk_iff {R : Type*} [CommRing R] {p I J : Ideal R}
    (hI : p ≤ I) (hJ : p ≤ J) :
    I.map (Ideal.Quotient.mk p) < J.map (Ideal.Quotient.mk p) ↔ I < J := by
  have hle : ∀ {I J : Ideal R}, p ≤ I → p ≤ J →
      (I.map (Ideal.Quotient.mk p) ≤ J.map (Ideal.Quotient.mk p) ↔ I ≤ J) := fun hI hJ =>
    ⟨fun h => by
      rw [← Ideal.comap_map_mk hI, ← Ideal.comap_map_mk hJ]
      exact Ideal.comap_mono h, Ideal.map_mono⟩
  simp only [lt_iff_le_not_ge, hle hI hJ, hle hJ hI]

/-- **Krull's principal ideal theorem, chain form.** Let `R` be a Noetherian ring, `x : R`, and
let `p` be a prime ideal. If a prime `q` is minimal over `p + (x)`, then no prime `r` lies
strictly between `p` and `q`. -/
public theorem solution {R : Type*}
    [CommRing R] [IsNoetherianRing R] {x : R} {p q r : Ideal R} [p.IsPrime] [r.IsPrime]
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) (hpr : p < r) : ¬r < q := by
  intro hrq
  have := hq.1.1
  have hpq : p ≤ q := le_sup_left.trans hq.1.2
  have hrP : (r.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hpr.le)
  have hqP : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hpq)
  -- Krull's principal ideal theorem in `R ⧸ p`: the height of `q ⧸ p` is at most `1`.
  have h1 : (q.map (Ideal.Quotient.mk p)).height ≤ 1 :=
    Ideal.map_height_le_one_of_mem_minimalPrimes (I := p) (x := x) hq
  -- `r ⧸ p` is a prime strictly below `q ⧸ p`, hence of height `0`.
  have hlt : r.map (Ideal.Quotient.mk p) < q.map (Ideal.Quotient.mk p) :=
    (map_mk_lt_map_mk_iff hpr.le hpq).2 hrq
  have hlt1 := Ideal.height_le_iff.1 h1 _ hrP hlt
  -- `r ⧸ p` is nonzero in the domain `R ⧸ p`, so `⊥ < r ⧸ p` and its height is at least `1`.
  have hbot : (⊥ : Ideal (R ⧸ p)) < r.map (Ideal.Quotient.mk p) := by
    simpa [Ideal.map_quotient_self] using (map_mk_lt_map_mk_iff le_rfl hpr.le).2 hpr
  have h2 : (1 : ℕ∞) ≤ (r.map (Ideal.Quotient.mk p)).height :=
    le_trans le_add_self (Ideal.height_add_one_le_of_lt_of_isPrime hbot)
  exact hlt1.not_ge (by exact_mod_cast h2)

end Stacks.IdealTheory.NoIntermediatePrime

/-!
# Primes minimal over `(p, x)`: the chain form of Krull's principal ideal theorem

Let `R` be a Noetherian ring, let `x ∈ R`, and let `p` be a prime ideal of `R`. If a prime `q` is
minimal over `p + (x)`, then no prime lies strictly between `p` and `q`: adjoining a single
element to a prime moves at most one step up the poset of primes. Equivalently, `q / p` has
height at most `1` in `R / p`, which is Krull's principal ideal theorem applied to the principal
ideal generated by the image of `x`.

## Main results

* `Ideal.not_lt_of_lt_of_mem_minimalPrimes_sup_span_singleton`: for `p` prime and `q` minimal
  over `p ⊔ (x)`, no prime `r` satisfies `p < r < q`.

## Implementation notes

The source has two items, and only the second is stated here. Item (1), "a prime minimal over
`(x)` has height `0` or `1`", is Krull's principal ideal theorem, which Mathlib has as
`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`: specializing its principal ideal to
`Ideal.span {x}`, whose `Submodule.IsPrincipal` instance inference finds, gives item (1) as a
single application, so restating it would duplicate a Mathlib lemma. "Height `0` or `1`" is
`height ≤ 1` there, `Ideal.height` taking values in `ℕ∞`.

"There is no prime strictly between `p` and `q`" is spelled the way Mathlib spells that concept
in `Ideal.height_le_iff_covBy`: a prime `r` with `p < r` has `¬ r < q`. The alternative, `CovBy`
in `PrimeSpectrum R`, would need the extra hypothesis `p < q` and a proof of `q.IsPrime` inside
the statement.

The hypothesis that `p` is prime cannot be relaxed to an arbitrary ideal: in `R = k[a, b, c]`
the prime `q = (a, c)` is minimal over `(ab) + (c)`, while `(ab) < (a) < (a, c)`. What is true
for an arbitrary ideal `I` in place of `p` is that no *two* primes fit, `I ≤ r₁ < r₂ < q`; that
strengthening is Mathlib's `Ideal.map_height_le_one_of_mem_minimalPrimes`, phrased there as
`(q.map (Ideal.Quotient.mk I)).height ≤ 1`, and the form stated here is the one the source
cites.

Faithfulness. (1) Every hypothesis is used by the conclusion: `IsNoetherianRing R` is what makes
Krull's theorem available, `p.IsPrime` is needed by the counterexample above, `r.IsPrime` is
needed because `⊥ < (a ^ 2) < (a)` in `k[a]` with `q = (a)` minimal over `(a)`, and `p < r` and
the minimality of `q` are the content. (2) The base is the source's: `p`, `q`, `r` and `x` all
live in `R`, with no quotient or localization in the statement (the source's proof passes to
`R / p`; the statement does not). (3) The source names no canonical map here; the ideal it writes
`(p, x)` is pinned as `p ⊔ Ideal.span {x}`. (4) The instantiation is not degenerate: in
`R = k[a, b]` with `p = (a)` and `x = b`, the prime `q = (a, b)` is minimal over `p + (b)` and
`p < q`, so the conclusion excludes candidates rather than holding vacuously.

## References

* [StackProject 00KV](https://stacks.math.columbia.edu/tag/00KV)
-/

/-- **Krull's principal ideal theorem, chain form.** Let `R` be a Noetherian ring, `x : R`, and
let `p` be a prime ideal. If a prime `q` is minimal over `p + (x)`, then no prime `r` lies
strictly between `p` and `q`. -/
@[stacks 00KV "Item (2); item (1) is Mathlib's Krull principal ideal theorem."]
public theorem Ideal.not_lt_of_lt_of_mem_minimalPrimes_sup_span_singleton {R : Type*}
    [CommRing R] [IsNoetherianRing R] {x : R} {p q r : Ideal R} [p.IsPrime] [r.IsPrime]
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) (hpr : p < r) : ¬r < q :=
  Stacks.IdealTheory.NoIntermediatePrime.solution hq hpr
