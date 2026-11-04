module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# The Jacobson radical of a ring of dimension at most one

In a domain of Krull dimension at most one every nonzero prime is maximal, so the Jacobson
radical is contained in every nonzero prime. Consequently a nonzero element of the Jacobson
radical is divisible-into by every nonzero element: some power of it lies in any nonzero
principal ideal. This single fact drives the gluing arguments for one-dimensional rings,
where it is used to exhibit a localization as a fraction field and to clear denominators.

## Main results

* `Ring.exists_dvd_pow_of_mem_jacobson`: a power of an element of the Jacobson radical is
  divisible by any given nonzero element.
* `Ring.exists_ne_zero_mem_jacobson`: a semilocal domain of dimension one has a nonzero
  element in its Jacobson radical.
* `Ring.isLocalization_powers_of_ne_zero_of_mem_jacobson`: the fraction field of a domain of
  dimension at most one is its localization away from a nonzero element of the Jacobson
  radical.
* `Ring.exists_algebraMap_eq_pow_mul`: every element of the fraction field becomes integral
  after multiplication by a power of an element of the Jacobson radical.
* `Ring.isUnit_add_of_isUnit_of_mem_jacobson`: adding an element of the Jacobson radical to a
  unit gives a unit.
* `Ring.mem_jacobson_of_algebraMap_mem`: the Jacobson radical of the base is detected in an
  integral extension.

## Implementation notes

The divisibility statement is the common core of the arguments which each of the gluing
results would otherwise re-derive: the radical of a nonzero principal ideal contains the
Jacobson radical, because every prime containing a nonzero element is maximal in dimension at
most one. The dimension hypothesis is `Ring.DimensionLEOne`, which is what the proofs use;
the sources state dimension exactly one.

## References

* [Stacks Project, Section 33.41 (Tag 09MX)](https://stacks.math.columbia.edu/tag/09MX)
-/

@[expose] public section

namespace Ring

variable {A : Type*} [CommRing A]

/-- In a ring of dimension at most one, a power of an element of the Jacobson radical is
divisible by any given nonzero element. -/
public lemma exists_dvd_pow_of_mem_jacobson [Ring.DimensionLEOne A] {x : A}
    (hx : x ∈ Ring.jacobson A) {a : A} (ha : a ≠ 0) :
    ∃ n : ℕ, a ∣ x ^ n := by
  have hrad : x ∈ (Ideal.span ({a} : Set A)).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro P hP
    have hP0 : P ≠ ⊥ := fun h =>
      ha (Ideal.mem_bot.mp (h ▸ hP.1 (Ideal.mem_span_singleton_self a)))
    have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP0 hP.2
    exact Ring.jacobson_le_of_isMaximal P hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

/-- In a ring of dimension at most one, a power of an element of the Jacobson radical lies in
any given nonzero principal ideal. -/
public lemma exists_pow_mem_span_singleton [Ring.DimensionLEOne A] {x : A}
    (hx : x ∈ Ring.jacobson A) {a : A} (ha : a ≠ 0) :
    ∃ n : ℕ, x ^ n ∈ Ideal.span ({a} : Set A) := by
  obtain ⟨n, hn⟩ := exists_dvd_pow_of_mem_jacobson hx ha
  exact ⟨n, Ideal.mem_span_singleton.mpr hn⟩

/-- A semilocal domain of Krull dimension one has a nonzero element in its Jacobson radical:
take the product of a nonzero element of each of its finitely many maximal ideals. -/
public lemma exists_ne_zero_mem_jacobson [IsDomain A] [Finite (MaximalSpectrum A)]
    (hdim : ringKrullDim A = 1) :
    ∃ x : A, x ≠ 0 ∧ x ∈ Ring.jacobson A := by
  classical
  have hnf : ¬ IsField A := fun hF =>
    one_ne_zero (hdim.symm.trans (ringKrullDim_eq_zero_of_isField hF))
  let _ : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  choose f hfmem hfne using fun p : MaximalSpectrum A =>
    Submodule.exists_mem_ne_zero_of_ne_bot
      (Ring.ne_bot_of_isMaximal_of_not_isField p.isMaximal hnf)
  refine ⟨∏ p : MaximalSpectrum A, f p, Finset.prod_ne_zero_iff.mpr fun p _ => hfne p, ?_⟩
  rw [Ring.jacobson_eq_sInf_isMaximal]
  refine Ideal.mem_sInf.mpr fun I hI => ?_
  obtain ⟨z, hz⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ (⟨I, hI⟩ : MaximalSpectrum A))
  exact hz ▸ I.mul_mem_right z (hfmem ⟨I, hI⟩)

/-- The fraction field of a domain of dimension at most one is also its localization away from
any nonzero element of the Jacobson radical. -/
public lemma isLocalization_powers_of_ne_zero_of_mem_jacobson {K : Type*} [IsDomain A]
    [Ring.DimensionLEOne A] [Field K] [Algebra A K] [IsFractionRing A K]
    (x : A) (hx : x ≠ 0) (hxj : x ∈ Ring.jacobson A) :
    IsLocalization (Submonoid.powers x) K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (S := K) (M := Submonoid.powers x)
    (nonZeroDivisors A) ?_ ?_).mpr inferInstance
  · rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hx)
  · intro a ha
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_mem_jacobson hxj
      (mem_nonZeroDivisors_iff_ne_zero.mp ha)
    exact ⟨x ^ n, ⟨n, rfl⟩, hn⟩

/-- Multiplying an element of the fraction field by a large enough power of an element of the
Jacobson radical brings it into the ring. -/
public lemma exists_algebraMap_eq_pow_mul {K : Type*} [IsDomain A] [Ring.DimensionLEOne A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (x : A) (hx : x ∈ Ring.jacobson A) (z : K) :
    ∃ n : ℕ, ∃ y : A, algebraMap A K y = (algebraMap A K x) ^ n * z := by
  obtain ⟨a, b, hb, hdiv⟩ := IsFractionRing.div_surjective (A := A) z
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, c, hc⟩ := exists_dvd_pow_of_mem_jacobson hx hb0
  have hbK : algebraMap A K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hcK : (algebraMap A K x) ^ n = (algebraMap A K b) * (algebraMap A K c) := by
    simpa only [map_pow, map_mul] using congrArg (algebraMap A K) hc
  refine ⟨n, a * c, ?_⟩
  rw [map_mul, hcK, ← hdiv]
  field_simp

/-- Adding an element of the Jacobson radical to a unit gives a unit. -/
public lemma isUnit_add_of_isUnit_of_mem_jacobson {a b : A} (ha : IsUnit a)
    (hb : b ∈ Ring.jacobson A) : IsUnit (a + b) := by
  obtain ⟨u, rfl⟩ := ha
  have hb_bot : b ∈ Ideal.jacobson (⊥ : Ideal A) := by rwa [Ideal.jacobson_bot]
  have hfactor : (u : A) + b = (b * ((u⁻¹ : Aˣ) : A) + 1) * (u : A) := by
    rw [add_mul, mul_assoc, u.inv_mul]
    ring
  rw [hfactor]
  exact (Ideal.mem_jacobson_bot.mp hb_bot _).mul u.isUnit

/-- For an injective integral extension, an element of the base whose image lies in the
Jacobson radical already lies in the Jacobson radical. -/
public lemma mem_jacobson_of_algebraMap_mem {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) {x : R}
    (hx : algebraMap R S x ∈ Ideal.jacobson (⊥ : Ideal S)) :
    x ∈ Ideal.jacobson (⊥ : Ideal R) := by
  rw [Ideal.jacobson, Ideal.mem_sInf] at hx ⊢
  intro m hm
  have := hm.2
  obtain ⟨n, hn, he⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) m
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  rw [← he]
  exact hx ⟨bot_le, hn⟩

end Ring
