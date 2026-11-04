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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
# Krull dimension is unchanged by an injective integral extension

Let `R ⊆ S` be commutative rings with `S` integral over `R`. This file proves Stacks 00OK:
`dim(R) = dim(S)`, where `dim` is the Krull dimension, the supremum of the lengths of chains of
prime ideals. The inclusion is taken in the form of an `R`-algebra `S` whose structure map is
injective.

Both inequalities are read off the map `Spec(S) → Spec(R)`, `𝔮 ↦ 𝔮 ∩ R`. Contraction along an
integral ring map is *strictly* monotone on primes, so a chain in `S` contracts to a chain in `R`
of the same length and `dim(S) ≤ dim(R)`; injectivity plays no role here (Stacks 00OJ). For the
other inequality, an injective integral map has surjective `Spec` (Stacks 00GQ, in Mathlib
`Algebra.IsIntegral.comap_surjective`) and satisfies going up (Stacks 00GU, in Mathlib the instance
`Algebra.HasGoingUp.of_isIntegral`). Hence a chain `𝔭₀ < ⋯ < 𝔭ₑ` in `R` lifts: surjectivity gives a
prime over `𝔭₀`, and going up extends a prime over `𝔭ᵢ` to a larger prime over `𝔭ᵢ₊₁`, the
extension being strict because the two contractions differ. So `dim(R) ≤ dim(S)` (Stacks 00OH).

## Main results

* `Stacks.KrullDimension.IntegralExtension.solution`: the statement of Stacks 00OK,
  `Algebra.IsIntegral.ringKrullDim_eq`.

## Implementation notes

The two halves are the private lemmas
`Stacks.KrullDimension.IntegralExtension.ringKrullDim_le_of_comap_surjective` (Stacks 00OH) and
`Stacks.KrullDimension.IntegralExtension.ringKrullDim_le_of_isIntegral` (Stacks 00OJ). The first is
stated for `[Algebra.HasGoingUp R S]` together with surjectivity of `PrimeSpectrum.comap
(algebraMap R S)`, which is all its proof uses: neither integrality nor injectivity appears, and it
therefore also covers the going-up situations that are not integral.

Two lemmas that Mathlib does not have are proved here. The chain lift is
`Stacks.KrullDimension.IntegralExtension.exists_ltSeries_comap_last_eq_of_hasGoingUp`, phrased as
an `Order.LTSeries` of `PrimeSpectrum` whose last term contracts to the last term of the given
series; the "lies over" bookkeeping is the running invariant of the induction on the length, and
the going-up step is Mathlib's `Ideal.exists_ideal_gt_liesOver_of_lt`. The order-theoretic
reduction it feeds is
`Stacks.KrullDimension.IntegralExtension.krullDim_le_of_forall_exists_length_le`: a preorder whose
chains are matched in length by chains of another has Krull dimension at most that of the other.
That is the companion of `Order.krullDim_le_of_strictMono` for maps that go the wrong way, and
unlike `Order.krullDim_le_of_strictComono_and_surj` it does not ask the comparison map to reflect
`<`, which contraction along an integral map does not do.

## References

* [StacksProject 00OK](https://stacks.math.columbia.edu/tag/00OK)
-/

namespace Stacks.KrullDimension.IntegralExtension

open Order

/-- If every chain in `α` is matched in length by a chain in `β`, then `krullDim α ≤ krullDim β`.
This is the companion of `Order.krullDim_le_of_strictMono` for a comparison that is not given by a
strictly monotone map `α → β`. -/
private theorem krullDim_le_of_forall_exists_length_le {α β : Type*} [Preorder α] [Preorder β]
    (h : ∀ p : LTSeries α, ∃ q : LTSeries β, p.length ≤ q.length) :
    krullDim α ≤ krullDim β := by
  rw [Order.krullDim]
  refine iSup_le fun p ↦ ?_
  obtain ⟨q, hq⟩ := h p
  exact le_trans (by exact_mod_cast hq) q.length_le_krullDim

/-- **Chain lifting for going up.** If `S` is an `R`-algebra satisfying going up whose induced map
`Spec(S) → Spec(R)` is surjective, then every chain of primes of `R` is the contraction of a chain
of primes of `S` of the same length, ending over the end of the given chain. -/
private theorem exists_ltSeries_comap_last_eq_of_hasGoingUp {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingUp R S]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)))
    (p : LTSeries (PrimeSpectrum R)) :
    ∃ q : LTSeries (PrimeSpectrum S), q.length = p.length ∧
      PrimeSpectrum.comap (algebraMap R S) q.last = p.last := by
  induction hn : p.length generalizing p with
  | zero =>
    obtain ⟨x, hx⟩ := hsurj p.last
    exact ⟨RelSeries.singleton _ x, by simp, hx⟩
  | succ n ih =>
    obtain ⟨q, hq, hql⟩ := ih p.eraseLast (by simp [hn])
    have hlt : p.eraseLast.last < p.last := p.eraseLast_last_rel_last (by omega)
    have : q.last.asIdeal.LiesOver p.eraseLast.last.asIdeal := ⟨by rw [← hql]; rfl⟩
    have : p.last.asIdeal.IsPrime := p.last.isPrime
    obtain ⟨Q, hQlt, hQp, hQo⟩ := Ideal.exists_ideal_gt_liesOver_of_lt
      (q := p.last.asIdeal) q.last.asIdeal ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).2 hlt)
    refine ⟨q.snoc ⟨Q, hQp⟩ ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hQlt), ?_, ?_⟩
    · rw [RelSeries.snoc_length, hq]
    · rw [RelSeries.last_snoc]; exact PrimeSpectrum.ext hQo.over.symm

/-- **Stacks 00OH** for going up: if `S` is an `R`-algebra satisfying going up whose induced map
`Spec(S) → Spec(R)` is surjective, then `dim(R) ≤ dim(S)`. -/
@[ega "IV 5.4.3" "dim(A) ≤ dim(B)"]
private theorem ringKrullDim_le_of_comap_surjective (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingUp R S]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) :
    ringKrullDim R ≤ ringKrullDim S :=
  krullDim_le_of_forall_exists_length_le fun p ↦ by
    obtain ⟨q, hq, -⟩ := exists_ltSeries_comap_last_eq_of_hasGoingUp hsurj p
    exact ⟨q, hq.ge⟩

/-- **Stacks 00OJ.** If `S` is an integral `R`-algebra then `dim(S) ≤ dim(R)`: contraction along an
integral ring map is strictly monotone on primes. No injectivity is needed. -/
@[ega "0 16.1.5", ega "IV 5.4.3" "dim(B) ≤ dim(A)"]
private theorem ringKrullDim_le_of_isIntegral (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap h

/-- An injective integral extension preserves Krull dimension: `dim(R) = dim(S)`, by the two
inequalities `ringKrullDim_le_of_comap_surjective` and `ringKrullDim_le_of_isIntegral`. -/
public theorem solution (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm
    (ringKrullDim_le_of_comap_surjective R S (Algebra.IsIntegral.comap_surjective R S))
    (ringKrullDim_le_of_isIntegral R S)

end Stacks.KrullDimension.IntegralExtension

/-!
# Krull dimension is unchanged by an injective integral extension

Let `R ⊆ S` be commutative rings with `S` integral over `R`, that is, every element of `S` is a
root of a monic polynomial with coefficients in `R`. Then `dim(R) = dim(S)`, where `dim` denotes
the Krull dimension, the supremum of the lengths of chains of prime ideals (Stacks 00OK).

Both inequalities are geometric statements about `Spec(S) → Spec(R)`, `𝔮 ↦ 𝔮 ∩ R`. Contraction
along an integral ring map is strictly monotone on primes, so chains in `S` push down to chains of
the same length in `R` and `dim(S) ≤ dim(R)`, with no injectivity needed (Lemma 00OJ). For the
converse, an injective integral map has surjective `Spec` (Lemma 00GQ, in Mathlib
`Algebra.IsIntegral.comap_surjective`) and satisfies going up (Lemma 00GU), so a chain of primes
of `R` lifts to a chain of primes of `S` of the same length and `dim(R) ≤ dim(S)` (Lemma 00OH).

## Main results

* `Algebra.IsIntegral.ringKrullDim_eq`: if `S` is an integral `R`-algebra and the structure map
  `R → S` is injective, then `ringKrullDim R = ringKrullDim S`.

## Implementation notes

The source's inclusion of rings `R ⊆ S` is stated here as an arbitrary `R`-algebra `S` whose
structure map `algebraMap R S` is injective, which subsumes it (a subring inclusion is such an
algebra map). Injectivity is spelled by the class `FaithfulSMul R S`, as in the sibling
`Algebra.IsIntegral.comap_surjective`, so that it is found by instance search;
`FaithfulSMul.algebraMap_injective` converts it to `Function.Injective (algebraMap R S)`.

The equality is oriented as in the source, `dim(R) = dim(S)`. `ringKrullDim` takes values in
`WithBot ℕ∞`, with `⊥` for the zero ring and `⊤` for infinite dimension, so no finiteness or
Noetherian hypothesis is needed and the degenerate case is covered: `S = 0` forces `R = 0` here,
because `algebraMap R S` is injective.

Faithfulness. (1) Neither hypothesis is idle: integrality gives `dim(S) ≤ dim(R)` and injectivity
gives `dim(R) ≤ dim(S)` — without integrality take `R = k ⊆ S = k[X]`, and without injectivity
take `S = 0` over a field `R`, where `dim(R) = 0 ≠ ⊥ = dim(S)`. (2) The rings and the extension
are the source's: a single `Algebra R S` structure, `Algebra.IsIntegral R S` and `FaithfulSMul R S`
all refer to the same map `algebraMap R S`, and both dimensions are those of `R` and of `S`
themselves. (3) The map the source names, the inclusion `R → S`, is pinned as `algebraMap R S`
through the two class hypotheses; the conclusion is an equality of numbers, not an existence
statement. (4) The instantiation is not degenerate: `ℤ ⊆ ℤ[i]` is injective and integral with
`dim = 1` on both sides, and `k ⊆ k[X]` shows the conclusion fails without integrality, so the
statement is not vacuous nor a tautology.

## References

* [StacksProject 00OK](https://stacks.math.columbia.edu/tag/00OK)
-/

@[expose] public section

/-- **Stacks 00OK.** If `S` is an integral `R`-algebra whose structure map `R → S` is injective
(for instance an integral ring extension `R ⊆ S`), then `R` and `S` have the same Krull
dimension. -/
@[stacks 00OK "The source's ring inclusion `R ⊆ S` is stated as an `R`-algebra `S` with
`algebraMap R S` injective, spelled `FaithfulSMul R S`; see the module docstring.", ega "0 16.1.5"
  "ρ injective case", ega "0 16.1.5" "ρ injective case", ega "IV 5.4.3" "more general"]
public theorem Algebra.IsIntegral.ringKrullDim_eq (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim R = ringKrullDim S := by apply Stacks.KrullDimension.IntegralExtension.solution

end
