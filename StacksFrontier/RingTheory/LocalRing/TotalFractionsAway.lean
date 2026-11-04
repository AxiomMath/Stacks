module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# The total ring of fractions of a reduced one-dimensional local ring is a localization away

Let `R` be a reduced Noetherian local ring of dimension one. There is an element `d` of the
maximal ideal lying in no minimal prime; every prime containing such a `d` is the maximal ideal,
and the localization of `R` away from `d` is the total ring of fractions of `R`, the
localization at the nonzerodivisors.

## Main results

* `mem_nonZeroDivisors_of_forall_notMem_minimalPrimes`: in a reduced ring an element outside
  every minimal prime is a nonzerodivisor.
* `IsLocalRing.exists_mem_maximalIdeal_isLocalization_nonZeroDivisors`: the element `d`.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

/-- **In a reduced ring an element outside every minimal prime is a nonzerodivisor**: anything it
kills lies in every minimal prime, hence in the nilradical. -/
theorem mem_nonZeroDivisors_of_forall_notMem_minimalPrimes [IsReduced R] {d : R}
    (hd : ∀ p ∈ minimalPrimes R, d ∉ p) : d ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have hmem : x ∈ (⊥ : Ideal R).radical := by
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro p hp
    have hpr : Ideal.IsPrime p := hp.1.1
    have h0 : x * d ∈ p := hx ▸ p.zero_mem
    exact (hpr.mem_or_mem h0).resolve_right (hd p hp)
  obtain ⟨n, hn⟩ := hmem
  exact IsReduced.eq_zero x ⟨n, by simpa using hn⟩

namespace IsLocalRing

variable [IsLocalRing R]

/-- In a local ring of dimension one the maximal ideal has height one. -/
private theorem height_maximalIdeal_eq_one (hdim : ringKrullDim R = 1) :
    (maximalIdeal R).height = 1 := by
  have := maximalIdeal_height_eq_ringKrullDim (R := R)
  rw [hdim] at this
  exact_mod_cast this

/-- In a local ring of dimension one every prime other than the maximal ideal is minimal, and
the maximal ideal is not. -/
theorem mem_minimalPrimes_of_ne_maximalIdeal (hdim : ringKrullDim R = 1) {p : Ideal R}
    [p.IsPrime] (hp : p ≠ maximalIdeal R) : p ∈ minimalPrimes R := by
  rw [← Ideal.height_eq_zero_iff]
  have hlt : p < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hp
  have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [height_maximalIdeal_eq_one hdim] at h
  have h' : p.height + 1 ≤ 0 + 1 := by simpa using h
  exact nonpos_iff_eq_zero.mp ((ENat.add_le_add_iff_right ENat.one_ne_top).mp h')

/-- In a local ring of dimension one the maximal ideal is not a minimal prime, since its height
is one. -/
theorem maximalIdeal_notMem_minimalPrimes (hdim : ringKrullDim R = 1) :
    maximalIdeal R ∉ minimalPrimes R := by
  intro h
  have := height_maximalIdeal_eq_one hdim
  rw [Ideal.height_eq_zero_iff.mpr h] at this
  exact absurd this (by norm_num)

/-- **In a reduced Noetherian local ring of dimension one there is an element `d` of the maximal
ideal lying in no minimal prime.** Every prime containing it is the maximal ideal, and the
localization away from it is the localization at the nonzerodivisors, the total ring of
fractions: every nonzerodivisor lies in no minimal prime, so its radical is the maximal ideal
and it divides a power of `d`. -/
theorem exists_mem_maximalIdeal_isLocalization_nonZeroDivisors [IsNoetherianRing R] [IsReduced R]
    (hdim : ringKrullDim R = 1) :
    ∃ d ∈ maximalIdeal R, (∀ p : Ideal R, p.IsPrime → d ∈ p → p = maximalIdeal R) ∧
      ∀ (L : Type*) [CommRing L] [Algebra R L] [IsLocalization.Away d L],
        IsLocalization (nonZeroDivisors R) L := by
  classical
  let S : Finset (Ideal R) := (Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥).toFinset
  have hS : ∀ p ∈ S, p ∈ minimalPrimes R := fun p hp => by
    simpa [S, minimalPrimes] using hp
  have hnot : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ p ∈ (↑S : Set (Ideal R)), (p : Set R)) := by
    intro hsub
    obtain ⟨p, hpS, hle⟩ := (Ideal.subset_union_prime (f := fun p : Ideal R => p) ⊥ ⊥
      (fun p hp _ _ => (hS p hp).1.1)).mp hsub
    have hpm : p = maximalIdeal R :=
      le_antisymm (le_maximalIdeal (hS p hpS).1.1.ne_top) hle
    exact maximalIdeal_notMem_minimalPrimes hdim (hpm ▸ hS p hpS)
  obtain ⟨d, hdm, hdS⟩ := Set.not_subset.mp hnot
  have hdmin : ∀ p ∈ minimalPrimes R, d ∉ p := by
    intro p hp hdp
    exact hdS (Set.mem_biUnion (x := p) (by simpa [S, minimalPrimes] using hp) hdp)
  have hprime : ∀ p : Ideal R, p.IsPrime → d ∈ p → p = maximalIdeal R := by
    intro p hp hdp
    by_contra hne
    exact hdmin p (mem_minimalPrimes_of_ne_maximalIdeal hdim hne) hdp
  refine ⟨d, hdm, hprime, fun L _ _ _ => ?_⟩
  have hd0 : d ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_forall_notMem_minimalPrimes hdmin
  refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers d) (nonZeroDivisors R)
    (Submonoid.powers_le.mpr hd0) fun n hn => ?_
  have hrad : d ∈ (Ideal.span {n}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hnJ, hJ⟩
    have hJm : J = maximalIdeal R := by
      by_contra hne
      have hmin := mem_minimalPrimes_of_ne_maximalIdeal hdim hne
      exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hmin)
        (hnJ (Ideal.mem_span_singleton_self n)) hn
    exact hJm ▸ hdm
  obtain ⟨k, hk⟩ := hrad
  exact ⟨d ^ k, ⟨k, rfl⟩, Ideal.mem_span_singleton.mp hk⟩

end IsLocalRing
