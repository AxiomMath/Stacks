module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Galois

/-!
# Galois extensions of degree prime to the residue characteristic are tame

Let `A` be a discrete valuation ring with fraction field `K` and residue field `κ`, and let `L/K`
be a finite Galois extension whose degree is invertible in `κ`. Then `L/K` is tamely ramified
with respect to `A`: all ramification indices and inertia degrees divide `[L : K]`
([Stacks, Tag 09EB]), so the ramification indices are prime to the characteristic of `κ` and the
residue field extensions, of degree prime to that characteristic, are separable.

## Main results

* `IsDiscreteValuationRing.isTamelyRamified_of_isGalois_of_isUnit_finrank`.

## References

* [Stacks Project, Tag 09EB](https://stacks.math.columbia.edu/tag/09EB)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public section

open IsLocalRing Module Field

namespace IsDiscreteValuationRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [Algebra A L] [IsScalarTower A K L]

/-- A divisor of a natural number invertible in a field is not divisible by the characteristic. -/
private lemma not_dvd_of_isUnit {k : Type*} [Field k] {n d : ℕ} (hn : IsUnit (n : k)) (hd : d ∣ n)
    (h : ringChar k ∣ d) : False :=
  hn.ne_zero ((CharP.cast_eq_zero_iff k (ringChar k) n).mpr (h.trans hd))

/-- **Galois extensions of degree invertible in the residue field are tame.** -/
theorem isTamelyRamified_of_isGalois_of_isUnit_finrank
    (h : IsUnit ((finrank K L : ℕ) : A ⧸ maximalIdeal A)) :
    Stacks.KummerExtension.IsTamelyRamified A K L := by
  classical
  obtain ⟨e, f, -, hf1, hef, hcard⟩ :=
    exists_uniform_ramificationIdx_inertiaDeg_and_finrank_eq A K L
  intro m hm hlies
  have := hm
  have : (maximalIdeal A).IsMaximal := maximalIdeal.isMaximal A
  let P : (maximalIdeal A).primesOver (integralClosure A L) := ⟨m, hm.isPrime, hlies⟩
  obtain ⟨he, hf⟩ := hef P
  have he_dvd : e ∣ finrank K L := by
    rw [← hcard]; exact (dvd_mul_left e _).trans (dvd_mul_right _ f)
  have hf_dvd : f ∣ finrank K L := by rw [← hcard]; exact dvd_mul_left f _
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  let : Field (integralClosure A L ⧸ m) := Ideal.Quotient.field _
  let : Algebra (A ⧸ maximalIdeal A) (integralClosure A L ⧸ m) :=
    Ideal.Quotient.algebraOfLiesOver m (maximalIdeal A)
  have hfin : finrank (A ⧸ maximalIdeal A) (integralClosure A L ⧸ m) = f := by
    rw [← hf, Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) m]
  have hchar := CharP.char_is_prime_or_zero (A ⧸ maximalIdeal A) (ringChar (A ⧸ maximalIdeal A))
  refine ⟨?_, ?_⟩
  · have hfpos : 0 < finrank (A ⧸ maximalIdeal A) (integralClosure A L ⧸ m) :=
      hfin ▸ hf1
    have : Module.Free (A ⧸ maximalIdeal A) (integralClosure A L ⧸ m) :=
      Module.Free.of_divisionRing _ _
    have : FiniteDimensional (A ⧸ maximalIdeal A) (integralClosure A L ⧸ m) :=
      Module.finite_of_finrank_pos hfpos
    rw [isSeparable_iff_finInsepDegree_eq_one]
    obtain ⟨k, hk⟩ := finInsepDegree_eq_pow (A ⧸ maximalIdeal A) (integralClosure A L ⧸ m)
      (ringExpChar (A ⧸ maximalIdeal A))
    have hdvd : finInsepDegree (A ⧸ maximalIdeal A) (integralClosure A L ⧸ m) ∣ f := by
      rw [← hfin, ← finSepDegree_mul_finInsepDegree]
      exact dvd_mul_left _ _
    rcases hchar with hp | hp
    · rcases k with _ | k
      · simpa using hk
      · exfalso
        refine not_dvd_of_isUnit h hf_dvd ?_
        have : ringExpChar (A ⧸ maximalIdeal A) = ringChar (A ⧸ maximalIdeal A) :=
          max_eq_left hp.one_lt.le
        rw [hk, this] at hdvd
        exact (dvd_pow_self _ (Nat.succ_ne_zero k)).trans hdvd
    · have : ringExpChar (A ⧸ maximalIdeal A) = 1 := by
        show max (ringChar (A ⧸ maximalIdeal A)) 1 = 1
        rw [hp]
        rfl
      rw [hk, this, one_pow]
  · have : IsDedekindDomain (integralClosure A L) :=
      (integralClosure_finite_dedekind_and_degree_eq_sum_ramification_inertia A K L).2.2.2.1
    have : Module.IsTorsionFree A (integralClosure A L) :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr (by
        intro x y hxy
        apply IsFractionRing.injective A K
        apply (algebraMap K L).injective
        simpa [IsScalarTower.algebraMap_apply A K L] using congrArg Subtype.val hxy)
    rcases hchar with hp | hp
    · right
      rw [Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal A) m
        (IsDiscreteValuationRing.not_a_field A), he]
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd ↦ not_dvd_of_isUnit h he_dvd hd
    · exact Or.inl hp

end IsDiscreteValuationRing
