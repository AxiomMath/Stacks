module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# The maximal ideals containing a nonzerodivisor of a one-dimensional ring are finite in number

In a Noetherian ring `A` of Krull dimension at most one, an element `d` that is a nonzerodivisor
lies in only finitely many maximal ideals: a prime containing `d` cannot be a minimal prime of
`A` — minimal primes consist of zerodivisors — so by the dimension bound it is maximal, and it is
then minimal among the primes containing `d`; and a Noetherian ring has only finitely many primes
minimal over an ideal.

The statement passes to a module-finite algebra `S` over `A`: a maximal ideal of `S` containing
the image of `d` contracts to a maximal ideal of `A` containing `d`, and a quasi-finite algebra
has only finitely many primes over a given one. This is the shape in which the *zero locus* of an
element of a one-dimensional ring is finite on a finite cover of its spectrum — for instance on
the normalization of a curve.

## Main results

* `Stacks.RingTheory.finite_setOf_isMaximal_mem_of_mem_nonZeroDivisors` — the maximal ideals of a
  Noetherian ring of dimension at most one containing a fixed nonzerodivisor are finite in
  number.
* `Stacks.RingTheory.finite_setOf_isMaximal_mem_algebraMap_of_moduleFinite` — the same upstairs,
  for a module-finite algebra.

## Implementation notes

Neither statement needs the quotient `A / dA`, which is the usual route (it is Artinian, hence
semilocal). Working with `(Ideal.span {d}).minimalPrimes` directly avoids transporting ideals
across `Ideal.Quotient.mk` in both directions.

The hypothesis shape is `[IsNoetherianRing A] [Ring.KrullDimLE 1 A]` together with
`d ∈ nonZeroDivisors A`, which is the form taken by Mathlib's
`isFiniteLength_quotient_span_singleton` and by this development's
`Stacks.Length.length_ne_top_of_isTorsionBy_nonZeroDivisor`: no domain and no reducedness
hypothesis.
-/

@[expose] public section

namespace Stacks.RingTheory

/-- **In a reduced ring, an element outside every minimal prime is a nonzerodivisor.** If `y d = 0`
with `y ≠ 0` then, the intersection of the minimal primes being the nilradical and hence zero,
some minimal prime misses `y`; that prime then contains `d`. -/
public theorem mem_nonZeroDivisors_of_forall_notMem_minimalPrimes {A : Type*} [CommRing A]
    [IsReduced A] {d : A} (h : ∀ p ∈ minimalPrimes A, d ∉ p) : d ∈ nonZeroDivisors A := by
  refine mem_nonZeroDivisors_iff_right.mpr fun y hy => ?_
  by_contra hy0
  have hsInf : sInf (minimalPrimes A) = ⊥ :=
    (Ideal.sInf_minimalPrimes (I := (⊥ : Ideal A))).trans (nilradical_eq_zero A)
  obtain ⟨p, hp, hyp⟩ : ∃ p ∈ minimalPrimes A, y ∉ p := by
    by_contra hall
    simp only [not_exists, not_and, Classical.not_not] at hall
    exact hy0 (by
      simpa only [hsInf, Ideal.mem_bot] using Ideal.mem_sInf.mpr fun p hp => hall p hp)
  have hyd : y * d ∈ p := by rw [hy]; exact p.zero_mem
  exact h p hp ((hp.isPrime.mem_or_mem hyd).resolve_left hyp)

/-- **The maximal ideals containing a nonzerodivisor are finite in number**, in a Noetherian ring
of Krull dimension at most one. Such a maximal ideal is minimal over the principal ideal `d A`,
because a prime strictly inside it would be a minimal prime of the ring and so would consist of
zerodivisors; and a Noetherian ring has finitely many primes minimal over an ideal. -/
public theorem finite_setOf_isMaximal_mem_of_mem_nonZeroDivisors {A : Type*} [CommRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {d : A} (hd : d ∈ nonZeroDivisors A) :
    {m : Ideal A | m.IsMaximal ∧ d ∈ m}.Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {d})).subset ?_
  rintro m ⟨hm, hdm⟩
  have := hm
  refine ⟨⟨hm.isPrime, m.span_singleton_le_iff_mem.mpr hdm⟩, fun q hq hqm => ?_⟩
  rcases Ring.krullDimLE_one_iff.mp ‹Ring.KrullDimLE 1 A› q hq.1 with hmin | hmax
  · exact absurd hd (notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
      (q.span_singleton_le_iff_mem.mp hq.2) hmin)
  · exact le_of_eq (hmax.eq_of_le hm.ne_top hqm).symm

/-- **The maximal ideals containing the image of a nonzerodivisor are finite in number upstairs
too.** If `S` is a module-finite `A`-algebra and only finitely many maximal ideals of `A` contain
`d`, then only finitely many maximal ideals of `S` contain the image of `d`: each contracts to one
of the former, and a quasi-finite algebra has finitely many primes over a given prime. -/
public theorem finite_setOf_isMaximal_mem_algebraMap_of_moduleFinite {A S : Type*} [CommRing A]
    [CommRing S] [Algebra A S] [Algebra.IsIntegral A S] [Module.Finite A S] (d : A)
    (hA : {m : Ideal A | m.IsMaximal ∧ d ∈ m}.Finite) :
    {n : Ideal S | n.IsMaximal ∧ algebraMap A S d ∈ n}.Finite := by
  refine (hA.biUnion fun m _ => Algebra.QuasiFinite.finite_primesOver (S := S) m).subset ?_
  rintro n ⟨hn, hdn⟩
  have := hn
  exact Set.mem_biUnion
    (show Ideal.under A n ∈ {m : Ideal A | m.IsMaximal ∧ d ∈ m} from
      ⟨Ideal.IsMaximal.under A n, hdn⟩)
    ⟨hn.isPrime, ⟨rfl⟩⟩

end Stacks.RingTheory

end
