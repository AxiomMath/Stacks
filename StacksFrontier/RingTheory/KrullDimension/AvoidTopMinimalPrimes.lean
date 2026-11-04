module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Support
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cutting the dimension with an element avoiding the top-dimensional minimal primes

Let `A` be a Noetherian ring of Krull dimension `d` and let `f ∈ A` lie outside every minimal
prime `p` with `dim A/p = d`. Then the quotient `A / (f)` has dimension strictly less than `d`,
and so does the support of `M / fM` for every finite `A`-module `M`.

The dimension of `A / (f)` is the length of the longest chain of primes containing `f`. Such a
chain starts at a prime containing a minimal prime, and if the chain is as long as possible then
its bottom is itself minimal of full dimension, which `f` avoids; otherwise the chain can be
extended by that minimal prime and becomes too long. For the module statement the support of
`M / fM` is contained in the support of `A / (f)`, so its dimension is bounded by the dimension
of `A / (f)`.

## Main results

* `ringKrullDim_quotient_span_singleton_lt_of_avoidsTopMinimalPrimes` — the dimension of the
  quotient drops.
* `Module.supportDim_quotSMulTop_lt_of_avoidsTopMinimalPrimes` — the support dimension of
  `M / fM` drops.
-/

@[expose] public noncomputable section

open Order

universe u v

/-- An element outside every minimal prime of full dimension cuts the Krull dimension of a
Noetherian ring: a chain of primes containing it of length `d` would have a minimal prime of
full dimension at its bottom, or else could be extended below. -/
theorem ringKrullDim_quotient_span_singleton_lt_of_avoidsTopMinimalPrimes
    (A : Type u) [CommRing A] [IsNoetherianRing A] (d : ℕ)
    (hd : ringKrullDim A = d) (f : A)
    (hf : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      ringKrullDim (A ⧸ p.asIdeal) = d → f ∉ p.asIdeal) :
    ringKrullDim (A ⧸ Ideal.span {f}) < d := by
  rw [ringKrullDim_quotient]
  refine Order.krullDim_lt_coe_iff.2 fun p => ?_
  by_contra hlen
  let q : LTSeries (PrimeSpectrum A) := p.map Subtype.val fun _ _ h => h
  have qlen : q.length = p.length := LTSeries.map_length p Subtype.val fun _ _ h => h
  have hle : ∀ s : LTSeries (PrimeSpectrum A), s.length ≤ d := fun s => by
    have h : (s.length : WithBot ℕ∞) ≤ ringKrullDim A := Order.LTSeries.length_le_krullDim s
    rw [hd] at h
    exact_mod_cast h
  have hpEq : p.length = d := Nat.le_antisymm (qlen ▸ hle q) (Nat.not_lt.mp hlen)
  obtain ⟨r, hrmin, hrle⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal A)) (J := q.head.asIdeal) bot_le
  have hfmem : f ∈ q.head.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus _ _).mp p.head.2 (Ideal.subset_span (Set.mem_singleton f))
  rcases eq_or_ne r q.head.asIdeal with rfl | heq
  · let t : LTSeries (PrimeSpectrum.zeroLocus (q.head.asIdeal : Set A)) :=
      { length := q.length
        toFun := fun i => ⟨q i, (PrimeSpectrum.mem_zeroLocus _ _).2 fun _ ha =>
          (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (q.monotone (Fin.zero_le i)) ha⟩
        step := fun i => q.strictMono (by simp) }
    have hdimGe : (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q.head.asIdeal) := by
      rw [ringKrullDim_quotient]
      have h := Order.LTSeries.length_le_krullDim t
      rwa [show t.length = q.length from rfl, qlen, hpEq] at h
    exact hf q.head hrmin (le_antisymm ((ringKrullDim_quotient_le _).trans hd.le) hdimGe) hfmem
  · let r' : PrimeSpectrum A := ⟨r, hrmin.isPrime⟩
    have hlt : r' < q.head :=
      (PrimeSpectrum.asIdeal_lt_asIdeal r' q.head).mp (lt_of_le_of_ne hrle heq)
    have hlong := hle (q.cons r' hlt)
    simp [qlen, hpEq] at hlong

/-- An element outside every minimal prime of full dimension cuts the support dimension of every
finite module: the support of `M / fM` is contained in the zero locus of `f`. -/
@[ega "0 16.3.4" "sufficiency"]
theorem Module.supportDim_quotSMulTop_lt_of_avoidsTopMinimalPrimes
    (A : Type u) [CommRing A] [IsNoetherianRing A] (d : ℕ)
    (hd : ringKrullDim A = d) (f : A)
    (hf : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      ringKrullDim (A ⧸ p.asIdeal) = d → f ∉ p.asIdeal)
    (M : Type (max u v)) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.supportDim A (QuotSMulTop f M) < (d : WithBot ℕ∞) := by
  have hsupp : Module.support A (QuotSMulTop f M) ⊆ Module.support A (A ⧸ Ideal.span {f}) := by
    intro p hp
    have hfp : f ∈ p.asIdeal := by
      rw [Module.support_quotSMulTop] at hp
      exact (PrimeSpectrum.mem_zeroLocus p {f}).mp hp.2 (by simp)
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    exact (PrimeSpectrum.mem_zeroLocus p _).2
      (SetLike.coe_subset_coe.mpr ((Ideal.span_singleton_le_iff_mem p.asIdeal).2 hfp))
  rw [Module.supportDim]
  refine lt_of_le_of_lt ?_
    (ringKrullDim_quotient_span_singleton_lt_of_avoidsTopMinimalPrimes A d hd f hf)
  rw [← Module.supportDim_quotient_eq_ringKrullDim (Ideal.span {f})]
  exact Order.krullDim_le_of_strictMono (fun p : Module.support A (QuotSMulTop f M) =>
    (⟨p.1, hsupp p.2⟩ : Module.support A (A ⧸ Ideal.span {f}))) fun _ _ h => h

end
