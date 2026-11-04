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
import StacksFrontier.RingTheory.Ideal.FinitePrimeAvoidance

@[expose] public section

/-!
# A Noetherian ring with finitely many primes has dimension at most one

Proof of `Ring.krullDimLE_one_of_finite_primeSpectrum`: a Noetherian ring `R` whose prime
spectrum is finite has `dim R ≤ 1`.

The mechanism is prime avoidance followed by Krull's principal ideal theorem. Let `𝔭` be a prime
of `R`. Only finitely many primes lie strictly below `𝔭`, and `𝔭` is contained in none of them,
so prime avoidance produces `x ∈ 𝔭` lying outside every prime strictly below `𝔭`. Any prime
containing `x` and contained in `𝔭` is then `𝔭` itself, that is, `𝔭` is a minimal prime over the
principal ideal `(x)`, so `height 𝔭 ≤ 1` by Krull's principal ideal theorem. As `dim R` is the
supremum of the heights of the primes of `R`, this gives `dim R ≤ 1`.

## Main results

* `Stacks.KrullDimension.FiniteSpectrum.solution`: a Noetherian ring with finitely many primes has
  Krull dimension at most `1`.

## Implementation notes

The source argues by reduction: first a Noetherian *local domain* with finitely many primes has
dimension at most `1`, because a nonempty open subset of the spectrum of a Noetherian local
domain of dimension at least `2` is infinite [StackProject 02IG]; then a Noetherian domain, by
passing to the localizations at the maximal ideals [StackProject 00KG]; then a general Noetherian
ring, by passing to `R/𝔮` for a minimal prime `𝔮` below the given prime [StackProject 00E0].

That route is followed here only in its content, not in its steps, and the reason is that its
three reductions all serve to arrange one application of Krull's principal ideal theorem, which
`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` already provides over an arbitrary
Noetherian ring. Neither locality, nor a domain hypothesis, nor a quotient is needed to say that
a prime minimal over a principal ideal has height at most `1`, and finiteness of the spectrum
exhibits every prime of `R` as such a prime directly; the deduction of `dim R ≤ 1` from a bound
on all heights is `ringKrullDim_le_iff_height_le`, which replaces the source's two reduction
lemmas at once. The prime avoidance step is the source's own mechanism for 02IG, applied to `R`
itself rather than to a localization of a quotient of `R`.

The content is carried by two lemmas, neither of which needs the Noetherian hypothesis; that
hypothesis enters only in Krull's principal ideal theorem afterwards.

* `Stacks.KrullDimension.FiniteSpectrum.exists_mem_forall_notMem_of_forall_not_le` is prime
  avoidance in element form: an ideal contained in none of finitely many primes has an element
  outside all of them. It is the elementwise reading of `Ideal.subset_union_prime_finite`, and the
  avoiding ideal need not itself be prime.
* `Stacks.KrullDimension.FiniteSpectrum.exists_mem_minimalPrimes_span_singleton` is the geometric
  step: a prime with only finitely many primes strictly below it is a minimal prime over a principal
  ideal. Finiteness of the whole spectrum is more than is used, so the lemma asks only for
  finiteness of the set of primes strictly below `p`.

## References

* [StackProject 0ALV](https://stacks.math.columbia.edu/tag/0ALV)
* [StackProject 02IG](https://stacks.math.columbia.edu/tag/02IG)
-/

namespace Stacks.KrullDimension.FiniteSpectrum

/-- A prime ideal `p` with only finitely many primes strictly below it is a minimal prime over a
principal ideal: prime avoidance gives `x ∈ p` outside all of them, and a prime `q ≤ p` with
`x ∈ q` can then be neither strictly below `p` nor anything else, so `q = p`. -/
private theorem exists_mem_minimalPrimes_span_singleton {R : Type*} [CommRing R] (p : Ideal R)
    [hp : p.IsPrime] (hfin : {q : Ideal R | q.IsPrime ∧ q < p}.Finite) :
    ∃ x : R, p ∈ (Ideal.span {x}).minimalPrimes := by
  obtain ⟨x, hxp, hx⟩ := exists_mem_forall_notMem_of_forall_not_le hfin (fun _ hq => hq.1)
    fun q hq hle => absurd hle (not_le_of_gt hq.2)
  refine ⟨x, ⟨hp, by rwa [Ideal.span_le, Set.singleton_subset_iff]⟩, ?_⟩
  rintro q ⟨hq, hqle⟩ hqp
  rcases hqp.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact absurd (hqle (Ideal.mem_span_singleton_self x)) (hx q ⟨hq, hlt⟩)

public theorem solution (R : Type*) [CommRing R] [IsNoetherianRing R]
    [Finite (PrimeSpectrum R)] : Ring.KrullDimLE 1 R := by
  rw [Ring.krullDimLE_iff, ringKrullDim_le_iff_height_le]
  intro p hp
  have hfin : {q : Ideal R | q.IsPrime ∧ q < p}.Finite :=
    (Set.finite_range PrimeSpectrum.asIdeal).subset fun q hq => ⟨⟨q, hq.1⟩, rfl⟩
  obtain ⟨x, hx⟩ := exists_mem_minimalPrimes_span_singleton p hfin
  have : (Ideal.span {x}).IsPrincipal := ⟨x, rfl⟩
  exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hx

end Stacks.KrullDimension.FiniteSpectrum

/-!
# A Noetherian ring with finitely many primes has dimension at most one

Let `R` be a Noetherian ring whose prime spectrum is finite. Then `dim R ≤ 1`, that is, every
prime of `R` is either minimal or maximal. The rings `k[[t]]` for a field `k`, and the `p`-adic
integers, are Noetherian rings of dimension `1` with finitely many primes, so `1` is the largest
dimension for which a finite spectrum can occur.

The argument reduces to the local domain case. If `R` is a Noetherian local domain of dimension
at least `2`, then every nonempty open subset of `Spec R` is infinite, so a Noetherian local
domain with finitely many primes has dimension at most `1`. A Noetherian domain with finitely
many primes therefore has `dim R_𝔪 ≤ 1` for every maximal ideal `𝔪`, hence `dim R ≤ 1` since the
dimension of a ring is the supremum of the dimensions of its localizations at maximal ideals.
In general `dim R/𝔮 ≤ 1` for every minimal prime `𝔮` of `R`, and every prime contains a minimal
prime, so `dim R ≤ 1`.

## Main results

* `Ring.krullDimLE_one_of_finite_primeSpectrum`: a Noetherian ring with finitely many primes has
  Krull dimension at most `1`.

## Implementation notes

The source writes the conclusion as `dim(R) ≤ 1`. It is stated here as `Ring.KrullDimLE 1 R`,
which is `ringKrullDim R ≤ 1` (`Ring.krullDimLE_iff`) and is the form the surrounding API
consumes: `Ring.krullDimLE_one_iff` turns it into "every prime is minimal or maximal", and, for
a domain, `Ring.krullDimLE_one_iff_of_noZeroDivisors` turns it into "every nonzero prime is
maximal", the form in which a Dedekind domain is recognised. The hypothesis "finitely many
primes" is the instance `Finite (PrimeSpectrum R)`, again Mathlib's spelling (as in
`PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`), so that it is found by
inference wherever it is already known, for instance over an Artinian ring.

No hypothesis of the source is dropped and none is added: the statement is for a commutative
ring, not a commutative semiring, because the dimension theory the source uses (systems of
parameters, and `dim R/xR = dim R - 1`) is ring-theoretic. Weakening `Finite (PrimeSpectrum R)`
to "finitely many non-minimal primes" is *not* a generalization: in a Noetherian ring the set of
minimal primes is already finite (`minimalPrimes.finite_of_isNoetherianRing`), so the two
hypotheses are equivalent.

Faithfulness. (1) Both hypotheses are used: without `IsNoetherianRing R` a valuation ring with
value group `ℤ ×ₗ ℤ` has exactly three primes and dimension `2`, and without
`Finite (PrimeSpectrum R)` the Noetherian ring `k[x, y]` has dimension `2`. (2) The base is the
source's: the spectrum counted and the dimension bounded are both those of `R` itself, not of a
localization or of a quotient. (3) The source names no canonical map; what has to be pinned is
the dimension, and `Ring.KrullDimLE 1 R` pins it as the Krull dimension of the prime spectrum of
`R` with its order, rather than asserting that some bound exists. (4) The instantiation is not
degenerate: `R = ℤ_[p]` is Noetherian, its spectrum is the two-element set `{(0), (p)}`, and its
dimension is exactly `1`, so the bound is attained and the hypotheses are not confined to
dimension `0`.

## References

* [StackProject 0ALV](https://stacks.math.columbia.edu/tag/0ALV)
-/

namespace Ring

/-- A Noetherian ring with finitely many primes has dimension at most `1`: every prime ideal is
either minimal or maximal. -/
@[stacks 0ALV]
public theorem krullDimLE_one_of_finite_primeSpectrum (R : Type*) [CommRing R]
    [IsNoetherianRing R] [Finite (PrimeSpectrum R)] :
    KrullDimLE 1 R :=
      by apply Stacks.KrullDimension.FiniteSpectrum.solution

end Ring
