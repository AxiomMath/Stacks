module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# The primes minimal over an ideal of dimension one are minimal primes of the ring

Let `A` be a local ring of Krull dimension one and `I` an ideal with `dim(A ⧸ I) = 1`. This file
proves

  `I.minimalPrimes = {𝔮 ∈ minimalPrimes A | I ≤ 𝔮}`,

that is: a prime minimal over `I` is already a minimal prime of `A`, and conversely a minimal
prime of `A` containing `I` is minimal over `I`.

The converse inclusion is a pure order argument and holds for any `I`. The forward inclusion is
where the dimensions are used, and it is false without them: in general a prime minimal over an
ideal is only minimal among the primes *containing that ideal*. Both hypotheses are needed. If
`dim(A ⧸ I) = 0` then `I.minimalPrimes` is the maximal ideal alone, which is not a minimal prime
of a one-dimensional ring; and if `dim A` were larger the primes minimal over a one-dimensional
`I` could sit anywhere above the minimal primes.

The argument for the forward inclusion is the one the geometric source performs with dimensions
of components: a prime `𝔮` minimal over `I` is not the maximal ideal, because a minimal prime
over `I` equal to the maximal ideal is the *only* prime over `I` and would make `dim(A ⧸ I)` zero;
so `𝔮` is strictly below the maximal ideal and `dim(A ⧸ 𝔮) ≥ 1`, hence `= 1` as `dim A = 1`. A
prime of a ring of dimension one whose quotient again has dimension one has height zero, by the
identity `dim A = ⨆_𝔭 (height 𝔭 + coheight 𝔭)` of `Order.krullDim`, and a prime of height zero is
a minimal prime.

## Main results

* `PrimeSpectrum.ringKrullDim_quotient_asIdeal_eq_krullDim_Ici`: the spectrum of `A ⧸ 𝔮` is the
  set of primes above `𝔮`, so `dim(A ⧸ 𝔮)` is the Krull dimension of that upper set — which is
  what makes it the coheight of `𝔮`.
* `Ideal.mem_minimalPrimes_of_ringKrullDim_quotient_eq_one`: a prime of a ring of Krull dimension
  one whose quotient has Krull dimension one is a minimal prime. No locality is needed here.
* `Ideal.ringKrullDim_quotient_eq_one_of_isMinimalPrime`: in a local ring of Krull dimension one,
  a prime minimal over an ideal `I` with `dim(A ⧸ I) = 1` has `dim(A ⧸ 𝔮) = 1`.
* `Ideal.minimalPrimes_eq_setOf_mem_minimalPrimes_of_ringKrullDim_eq_one`: the displayed
  identity.

## Implementation notes

This is the ring-theoretic content of the hypothesis `hc` of
`AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul`, which asks of a family of ideals
`I i` cutting out the irreducible components of a space through a point and of a map `c` sending
each branch — each minimal prime of the local ring — to the component it lies on, that

  `𝔮 ∈ (I i).minimalPrimes ↔ ∃ h : 𝔮 ∈ minimalPrimes A, c ⟨𝔮, h⟩ = i`.

With the identity below that hypothesis becomes

  `𝔮 ∈ minimalPrimes A → (I i ≤ 𝔮 ↔ c ⟨𝔮, _⟩ = i)`,

an incidence statement with no dimension theory left in it: that a branch lies on the `i`-th
component exactly when `c` sends it there. The dimension bookkeeping, which is where the
geometric source spends its argument, is discharged once and for all here.
-/

@[expose] public section

namespace PrimeSpectrum

variable {A : Type*} [CommRing A]

/-- **The Krull dimension of the quotient by a prime is the Krull dimension of the primes above
it.** `Mathlib`'s `ringKrullDim_quotient` presents the spectrum of `A ⧸ 𝔮` as the vanishing locus
of `𝔮`, which for a prime is the upper set `Set.Ici 𝔮` of the specialization order; together with
`Order.coheight_eq_krullDim_Ici` this identifies `dim(A ⧸ 𝔮)` with the coheight of `𝔮`. -/
theorem ringKrullDim_quotient_asIdeal_eq_krullDim_Ici (q : PrimeSpectrum A) :
    ringKrullDim (A ⧸ q.asIdeal) = Order.krullDim (Set.Ici q) := by
  rw [ringKrullDim_quotient,
    show PrimeSpectrum.zeroLocus (R := A) (q.asIdeal : Set A) = Set.Ici q from rfl]

end PrimeSpectrum

namespace Ideal

variable {A : Type*} [CommRing A]

/-- **A prime of a one-dimensional ring whose quotient is again one-dimensional is a minimal
prime.** The coheight of `𝔮` in the spectrum is the Krull dimension of the primes above `𝔮`, so
it is one; and `dim A` is the supremum over the primes of height plus coheight
(`Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`), so the height of `𝔮` plus one is at
most one. A prime of height zero is a minimal prime, by `Ideal.height_eq_zero_iff`.

Geometrically: an irreducible closed subset of a one-dimensional space which is itself
one-dimensional is an irreducible component. -/
theorem mem_minimalPrimes_of_ringKrullDim_quotient_eq_one (hdim : ringKrullDim A = 1)
    (q : Ideal A) [hq : q.IsPrime] (hqdim : ringKrullDim (A ⧸ q) = 1) :
    q ∈ minimalPrimes A := by
  have hco : Order.coheight (⟨q, hq⟩ : PrimeSpectrum A) = 1 := by
    have h := Order.coheight_eq_krullDim_Ici (⟨q, hq⟩ : PrimeSpectrum A)
    rw [← PrimeSpectrum.ringKrullDim_quotient_asIdeal_eq_krullDim_Ici, hqdim] at h
    exact_mod_cast h
  have hne : Nonempty (PrimeSpectrum A) := ⟨⟨q, hq⟩⟩
  have h := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := PrimeSpectrum A)
  rw [← ringKrullDim, hdim] at h
  have hsup : (⨆ a : PrimeSpectrum A, Order.height a + Order.coheight a) = 1 := by
    exact_mod_cast h.symm
  have hle : Order.height (⟨q, hq⟩ : PrimeSpectrum A) +
      Order.coheight (⟨q, hq⟩ : PrimeSpectrum A) ≤ 1 :=
    hsup ▸ le_iSup (fun a : PrimeSpectrum A => Order.height a + Order.coheight a) ⟨q, hq⟩
  rw [hco] at hle
  rw [← Ideal.height_eq_zero_iff, (⟨q, hq⟩ : PrimeSpectrum A).height_eq_orderHeight,
    Order.lt_one_iff.mp ((ENat.add_one_le_iff' (by simp)).mp hle)]

/-- **A prime minimal over a one-dimensional ideal of a local ring is not the maximal ideal.**
Were it the maximal ideal, every prime containing `I` would contain it — being below the maximal
ideal of a local ring and above a minimal prime over `I` — so the vanishing locus of `I` would be
a single point and `dim(A ⧸ I)` would be at most zero. -/
theorem ne_maximalIdeal_of_isMinimalPrime_of_ringKrullDim_quotient_eq_one [IsLocalRing A]
    {I q : Ideal A} (hI : ringKrullDim (A ⧸ I) = 1) (hq : I.IsMinimalPrime q) :
    q ≠ IsLocalRing.maximalIdeal A := by
  intro hqm
  have hsub : Subsingleton (PrimeSpectrum.zeroLocus (I : Set A)) := by
    have key : ∀ r : PrimeSpectrum.zeroLocus (I : Set A), (r : PrimeSpectrum A) = ⊤ := fun r =>
      PrimeSpectrum.ext <| le_antisymm (le_top (a := (r : PrimeSpectrum A))) <| by
        change IsLocalRing.maximalIdeal A ≤ _
        rw [← hqm]
        exact hq.2 ⟨r.1.2, SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp r.2)⟩
          (hqm ▸ le_top (a := (r : PrimeSpectrum A)))
    exact ⟨fun p p' => Subtype.ext ((key p).trans (key p').symm)⟩
  rw [ringKrullDim_quotient] at hI
  exact absurd (hI ▸ Order.krullDim_nonpos_of_subsingleton) (by simp)

/-- **A prime minimal over a one-dimensional ideal of a one-dimensional local ring has
one-dimensional quotient.** It is not the maximal ideal by
`Ideal.ne_maximalIdeal_of_isMinimalPrime_of_ringKrullDim_quotient_eq_one`, so the two primes
`𝔮 ⊊ 𝔪` give a strict chain among the primes above `𝔮` and `dim(A ⧸ 𝔮) ≥ 1`; and
`dim(A ⧸ 𝔮) ≤ dim A = 1`. -/
theorem ringKrullDim_quotient_eq_one_of_isMinimalPrime [IsLocalRing A]
    (hdim : ringKrullDim A = 1) {I q : Ideal A} (hI : ringKrullDim (A ⧸ I) = 1)
    (hq : I.IsMinimalPrime q) : ringKrullDim (A ⧸ q) = 1 := by
  have hqp : q.IsPrime := hq.isPrime
  have hqlt : (⟨q, hqp⟩ : PrimeSpectrum A) < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => ne_maximalIdeal_of_isMinimalPrime_of_ringKrullDim_quotient_eq_one
      hI hq (congrArg PrimeSpectrum.asIdeal h)
  refine le_antisymm (hdim ▸ ringKrullDim_quotient_le q) ?_
  rw [PrimeSpectrum.ringKrullDim_quotient_asIdeal_eq_krullDim_Ici (⟨q, hqp⟩ : PrimeSpectrum A)]
  exact Order.one_le_krullDim_iff.mpr ⟨⟨_, Set.mem_Ici.mpr le_rfl⟩, ⟨⊤, hqlt.le⟩, hqlt⟩

/-- **The primes minimal over a one-dimensional ideal of a one-dimensional local ring are exactly
the minimal primes of the ring containing it.**

The inclusion from right to left is a pure order argument: a prime above `I` and below a minimal
prime of `A` containing `I` is that minimal prime. The inclusion from left to right is
`Ideal.ringKrullDim_quotient_eq_one_of_isMinimalPrime` followed by
`Ideal.mem_minimalPrimes_of_ringKrullDim_quotient_eq_one`.

This is what the hypothesis `hc` of
`AlgebraicGeometry.natCast_ord_sub_eq_finsum_components_mul` needs in order to become a statement
about which branches lie on which component, with no dimension theory in it; see the
implementation notes of this file. -/
theorem minimalPrimes_eq_setOf_mem_minimalPrimes_of_ringKrullDim_eq_one [IsLocalRing A]
    (hdim : ringKrullDim A = 1) (I : Ideal A) (hI : ringKrullDim (A ⧸ I) = 1) :
    I.minimalPrimes = {q : Ideal A | q ∈ minimalPrimes A ∧ I ≤ q} := by
  ext q
  refine ⟨fun hq => ⟨?_, hq.le⟩, fun hq => ⟨⟨hq.1.isPrime, hq.2⟩, fun p hp hpq => ?_⟩⟩
  · have hqp : q.IsPrime := hq.isPrime
    exact mem_minimalPrimes_of_ringKrullDim_quotient_eq_one hdim q
      (ringKrullDim_quotient_eq_one_of_isMinimalPrime hdim hI hq)
  · exact hq.1.2 ⟨hp.1, bot_le⟩ hpq

end Ideal

end
