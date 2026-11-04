module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Proper closed subsets of a one-dimensional spectrum are finite

Let `A` be a Noetherian ring of Krull dimension at most one, in the sense that every nonzero
prime ideal of `A` is maximal. Then every proper closed subset of `PrimeSpectrum A` is finite,
and in particular the vanishing locus `V(I)` of a nonzero ideal is finite.

The mechanism is that over a nonzero ideal `I` there is no room for a chain of primes: a prime
`q ⊇ I` is itself nonzero, hence maximal, so no prime containing `I` sits strictly inside it.
Every point of `V(I)` is therefore a *minimal* prime over `I`, and a Noetherian ring has only
finitely many of those. A closed set is `V(I)` for some ideal `I`, and it is proper exactly when
some prime fails to contain `I`, which forces `I ≠ ⊥`.

Dedekind domains satisfy both hypotheses, so the statements are recorded for them as well.
-/

@[expose] public section

/-- In a ring of Krull dimension at most one, any prime containing a nonzero ideal `I` is already
minimal over `I`: a prime between `I` and it is nonzero, hence maximal, hence equal to it. -/
theorem Ideal.isMinimalPrime_of_ne_bot {A : Type*} [CommRing A] [Ring.DimensionLEOne A]
    {I p : Ideal A} (hI : I ≠ ⊥) (hp : p.IsPrime) (hle : I ≤ p) : I.IsMinimalPrime p := by
  refine ⟨⟨hp, hle⟩, fun q hq hqp ↦ ?_⟩
  have hqne : q ≠ ⊥ := fun h ↦ hI (le_bot_iff.mp (h ▸ hq.2))
  exact ((Ring.DimensionLEOne.maximalOfPrime hqne hq.1).eq_of_le hp.ne_top hqp).ge

/-- **The vanishing locus of a nonzero ideal is finite** in a Noetherian ring of Krull dimension
at most one: its points are exactly the minimal primes over the ideal, of which there are
finitely many. -/
theorem PrimeSpectrum.finite_zeroLocus {A : Type*} [CommRing A] [IsNoetherianRing A]
    [Ring.DimensionLEOne A] {I : Ideal A} (hI : I ≠ ⊥) :
    (PrimeSpectrum.zeroLocus (I : Set A)).Finite :=
  Set.Finite.subset (Set.Finite.preimage (fun _ _ _ _ h ↦ PrimeSpectrum.ext h)
      (Ideal.finite_minimalPrimes_of_isNoetherianRing A I))
    fun q hq ↦ Ideal.isMinimalPrime_of_ne_bot hI q.isPrime ((mem_zeroLocus _ _).mp hq)

/-- **Every proper closed subset of the prime spectrum of a Noetherian ring of Krull dimension at
most one is finite.** Properness is what rules out the vanishing locus of the zero ideal, which is
the whole space. -/
theorem PrimeSpectrum.finite_of_isClosed_of_ne_univ {A : Type*} [CommRing A] [IsNoetherianRing A]
    [Ring.DimensionLEOne A] {Z : Set (PrimeSpectrum A)} (hZ : IsClosed Z) (hZ' : Z ≠ Set.univ) :
    Z.Finite := by
  obtain ⟨I, rfl⟩ := (isClosed_iff_zeroLocus_ideal Z).mp hZ
  obtain ⟨p, hp⟩ := (Set.ne_univ_iff_exists_notMem _).mp hZ'
  refine finite_zeroLocus fun h ↦ hp ?_
  rw [h]
  simp

/-- The vanishing locus of a nonzero ideal of a Dedekind domain is finite. -/
theorem IsDedekindDomain.finite_zeroLocus {A : Type*} [CommRing A] [IsDedekindDomain A]
    {I : Ideal A} (hI : I ≠ ⊥) : (PrimeSpectrum.zeroLocus (I : Set A)).Finite :=
  PrimeSpectrum.finite_zeroLocus hI

/-- Every proper closed subset of the prime spectrum of a Dedekind domain is finite. -/
theorem IsDedekindDomain.finite_of_isClosed_of_ne_univ {A : Type*} [CommRing A]
    [IsDedekindDomain A] {Z : Set (PrimeSpectrum A)} (hZ : IsClosed Z) (hZ' : Z ≠ Set.univ) :
    Z.Finite :=
  PrimeSpectrum.finite_of_isClosed_of_ne_univ hZ hZ'

end
