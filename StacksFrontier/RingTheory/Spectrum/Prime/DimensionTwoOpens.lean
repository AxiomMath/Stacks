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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Nonempty opens in the spectrum of a Noetherian local domain of dimension at least two

A nonempty open subset of the spectrum of a Noetherian local domain `R` with `dim R ≥ 2` is
infinite. A Noetherian domain with a prime of height at least two has infinitely many primes of
height one, while for `x ≠ 0` only the finitely many minimal primes of `(x)` among them contain
`x`; so every nonempty basic open `D(x)` is infinite.

## Main results

* `PrimeSpectrum.infinite_of_two_le_ringKrullDim`: a nonempty open subset of the prime spectrum
  of a Noetherian local domain of Krull dimension at least `2` is infinite.

## References

* [StackProject 02IG](https://stacks.math.columbia.edu/tag/02IG)
-/

@[expose] public section

namespace Stacks.Spectrum.InfiniteOpens

open IsLocalRing

/-- Krull's principal ideal theorem in a Noetherian domain: a prime `p` containing a nonzero
element `x` is minimal over `(x)` if and only if it has height one. -/
@[ega "IV 5.2.5" "more general"]
private theorem mem_minimalPrimes_span_singleton_iff_height_eq_one {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsDomain R] {x : R} (hx : x ≠ 0) {p : Ideal R} [p.IsPrime]
    (hxp : x ∈ p) : p ∈ (Ideal.span {x}).minimalPrimes ↔ p.height = 1 := by
  have : (Ideal.span {x}).IsPrincipal := ⟨x, rfl⟩
  have hle : Ideal.span {x} ≤ p := (Ideal.span_singleton_le_iff_mem _).mpr hxp
  have h1 : 1 ≤ (Ideal.span {x}).height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx)
  exact ⟨fun hp => le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp)
      (h1.trans (Ideal.height_mono hle)),
    fun hp1 => Ideal.mem_minimalPrimes_of_height_le hle (hp1 ▸ h1)⟩

/-- A Noetherian domain with a prime of height at least two has infinitely many primes of height
one: prime avoidance produces a nonzero `y` in the given prime lying outside any finite list of
them, and a minimal prime of `(y)` is one more. -/
@[ega "IV 10.5.1" "e)"]
private theorem infinite_setOf_height_eq_one {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsDomain R] {P : Ideal R} [P.IsPrime] (hP : 2 ≤ P.height) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1}.Infinite := by
  intro hfin
  obtain ⟨y, hyP, hy⟩ := exists_mem_forall_notMem_of_forall_not_le (hfin.insert ⊥) (I := P)
    (by rintro q (rfl | ⟨hq, -⟩); exacts [Ideal.isPrime_bot, hq])
    (by
      rintro q hq hle
      have h2 := hP.trans (Ideal.height_mono hle)
      rcases hq with rfl | ⟨-, hq1⟩
      · simp at h2
      · simp [hq1] at h2)
  have hy0 : y ≠ 0 := fun h => hy ⊥ (Set.mem_insert _ _) (h ▸ Ideal.zero_mem ⊥)
  obtain ⟨⟨q, hq⟩⟩ := Ideal.nonempty_minimalPrimes (I := Ideal.span {y}) fun h =>
    ‹P.IsPrime›.ne_top (top_le_iff.mp (h ▸ (Ideal.span_singleton_le_iff_mem _).mpr hyP))
  have hqp : q.IsPrime := hq.1.1
  have hyq : y ∈ q := hq.1.2 (Ideal.mem_span_singleton_self y)
  exact hy q (Set.mem_insert_of_mem _
    ⟨hqp, (mem_minimalPrimes_span_singleton_iff_height_eq_one hy0 hyq).mp hq⟩) hyq

/-- A nonempty open subset of the spectrum of a Noetherian local domain of dimension at least
two is infinite. -/
public theorem solution (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsDomain R] (hR : 2 ≤ ringKrullDim R) (U : Set (PrimeSpectrum R)) (hU : IsOpen U)
    (hU' : U.Nonempty) : U.Infinite := by
  obtain ⟨p₀, hp₀U⟩ := hU'
  obtain ⟨V, ⟨x, hx⟩, hp₀V, hVU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp₀U hU
  subst hx
  have hx0 : x ≠ 0 := fun h =>
    (PrimeSpectrum.mem_basicOpen _ _).mp hp₀V (h ▸ p₀.asIdeal.zero_mem)
  have h2 : 2 ≤ (maximalIdeal R).height := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)] at hR
    exact WithBot.coe_le_coe.mp hR
  refine Set.Infinite.mono hVU (Set.Infinite.of_image PrimeSpectrum.asIdeal
    (Set.Infinite.mono ?_ ((infinite_setOf_height_eq_one h2).sdiff
      (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {x})))))
  rintro p ⟨⟨hp, hp1⟩, hpm⟩
  exact ⟨⟨p, hp⟩, (PrimeSpectrum.mem_basicOpen _ _).mpr fun hxp =>
    hpm ((mem_minimalPrimes_span_singleton_iff_height_eq_one hx0 hxp).mpr hp1), rfl⟩

end Stacks.Spectrum.InfiniteOpens

namespace PrimeSpectrum

/-- A nonempty open subset of the spectrum of a Noetherian local domain of dimension at least
two is infinite. -/
@[stacks 02IG, ega "IV 10.5.1" "e) ⇒ f) for local B"]
public theorem infinite_of_two_le_ringKrullDim (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsDomain R] (hR : 2 ≤ ringKrullDim R) (U : Set (PrimeSpectrum R))
    (hU : IsOpen U) (hU' : U.Nonempty) : U.Infinite :=
  Stacks.Spectrum.InfiniteOpens.solution R hR U hU hU'

end PrimeSpectrum
