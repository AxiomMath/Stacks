module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# An integral extension of a normal domain with trivial generic fibre

Let `A` be a normal domain with fraction field `K` and let `A ⟶ A'` be an integral ring map with
`A'` reduced, such that every minimal prime of `A'` lies over the zero ideal of `A`.  If the
generic fibre is trivial, in the sense that `K ⟶ K ⊗_A A'` is bijective, then `A ⟶ A'` is
bijective.

## Main results

* `injective_includeRight_of_comap_minimalPrimes_eq_bot`: `A' ⟶ K ⊗_A A'` is injective when `A'`
  is reduced and its minimal primes lie over `0`.
* `injective_includeRight_of_forall_mul_eq_zero`: `A' ⟶ K ⊗_A A'` is injective when `A'` is
  torsion free over `A`.
* `bijective_algebraMap_of_bijective_includeLeft`: `A ⟶ A'` is bijective.
* `RingHom.bijective_of_isIntegral_of_injective_comp_eq`: an integral map out of a normal domain
  which embeds compatibly into a ring isomorphic to the fraction field is bijective.

## References

* [Stacks Project, Tag 0AYI](https://stacks.math.columbia.edu/tag/0AYI)
-/

@[expose] public section

open TensorProduct

/-- An element of `A'` killed by `K ⊗_A A'` is killed by a nonzero element of `A`. -/
private theorem exists_mul_eq_zero_of_includeRight_eq_zero
    (A K A' : Type*) [CommRing A] [CommRing K] [Algebra A K] [IsFractionRing A K]
    [CommRing A'] [Algebra A A'] {a : A'}
    (ha : (Algebra.TensorProduct.includeRight : A' →ₐ[A] K ⊗[A] A') a = 0) :
    ∃ s : nonZeroDivisors A, algebraMap A A' s * a = 0 := by
  have := IsLocalization.tensorProduct_isLocalizedModule (M := A') (nonZeroDivisors A) K
  have ha' : TensorProduct.mk A K A' 1 a = 0 := ha
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A) _).1 ha'
  exact ⟨s, by rw [← Algebra.smul_def]; exact hs⟩

/-- Let `A` be a domain with fraction field `K` and `A'` a reduced `A`-algebra each of whose
minimal primes lies over `0`.  Then `A' ⟶ K ⊗_A A'` is injective. -/
theorem injective_includeRight_of_comap_minimalPrimes_eq_bot
    (A K A' : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing A'] [Algebra A A'] [IsReduced A']
    (hmin : ∀ p ∈ minimalPrimes A', p.comap (algebraMap A A') = ⊥) :
    Function.Injective (Algebra.TensorProduct.includeRight : A' →ₐ[A] K ⊗[A] A') := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨s, hs⟩ := exists_mul_eq_zero_of_includeRight_eq_zero A K A' ha
  have hmem : a ∈ sInf (minimalPrimes A') := by
    refine Ideal.mem_sInf.2 fun p hp => ?_
    rcases hp.1.1.mem_or_mem (hs ▸ p.zero_mem) with h | h
    · have : (s : A) ∈ p.comap (algebraMap A A') := h
      rw [hmin p hp, Ideal.mem_bot] at this
      exact absurd this (nonZeroDivisors.coe_ne_zero s)
    · exact h
  rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
  exact IsNilpotent.eq_zero <|
    (Ideal.mem_radical_iff (I := ⊥)).1 hmem |>.imp fun n h => by simpa using h

/-- Let `A` be a domain, `K` a fraction ring of `A` and `A'` an `A`-algebra which is torsion free:
a nonzero element of `A` kills no nonzero element of `A'`.  Then `A' ⟶ K ⊗_A A'` is injective. -/
theorem injective_includeRight_of_forall_mul_eq_zero
    (A K A' : Type*) [CommRing A] [IsDomain A] [CommRing K] [Algebra A K] [IsFractionRing A K]
    [CommRing A'] [Algebra A A']
    (htor : ∀ a : A, a ≠ 0 → ∀ s : A', algebraMap A A' a * s = 0 → s = 0) :
    Function.Injective (Algebra.TensorProduct.includeRight : A' →ₐ[A] K ⊗[A] A') := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨s, hs⟩ := exists_mul_eq_zero_of_includeRight_eq_zero A K A' ha
  exact htor s (nonZeroDivisors.coe_ne_zero s) a hs

/-- **An integral extension of a normal domain with trivial generic fibre is trivial.**  Let `A`
be a normal domain with fraction field `K` and `A'` a reduced `A`-algebra, integral over `A`,
each of whose minimal primes lies over `0`.  If `K ⟶ K ⊗_A A'` is bijective, then so is
`A ⟶ A'`. -/
theorem bijective_algebraMap_of_bijective_includeLeft
    (A K A' : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing A'] [Algebra A A'] [Algebra.IsIntegral A A'] [IsReduced A']
    (hmin : ∀ p ∈ minimalPrimes A', p.comap (algebraMap A A') = ⊥)
    (hgen : Function.Bijective (Algebra.TensorProduct.includeLeft : K →ₐ[A] K ⊗[A] A')) :
    Function.Bijective (algebraMap A A') := by
  have hinj := injective_includeRight_of_comap_minimalPrimes_eq_bot A K A' hmin
  have hcomm : ∀ a : A, (Algebra.TensorProduct.includeRight : A' →ₐ[A] K ⊗[A] A')
      (algebraMap A A' a) = Algebra.TensorProduct.includeLeft (algebraMap A K a) := fun a => by
    rw [AlgHom.commutes, AlgHom.commutes]
  refine ⟨fun a b hab => ?_, fun a' => ?_⟩
  · have := congrArg (Algebra.TensorProduct.includeRight : A' →ₐ[A] K ⊗[A] A') hab
    rw [hcomm, hcomm] at this
    exact IsFractionRing.injective A K (hgen.1 this)
  · obtain ⟨k, hk⟩ := hgen.2 (Algebra.TensorProduct.includeRight a')
    have hint : IsIntegral A k :=
      (isIntegral_algHom_iff _ hgen.1).1 (hk ▸ (Algebra.IsIntegral.isIntegral a').map _)
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    exact ⟨y, hinj (by rw [hcomm, hk])⟩

/-- **An integral extension of a normal domain which embeds into a ring equal to the fraction
field is trivial.**  Let `A` be a normal domain with fraction field `K`, let `ψ : A ⟶ A'` be
integral, and let `ρ : A' ⟶ R` and `κ : K ⟶ R` be ring maps agreeing on `A`, with `ρ` injective
and `κ` bijective.  Then `ψ` is bijective. -/
theorem RingHom.bijective_of_isIntegral_of_injective_comp_eq {A A' K R : Type*} [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing A'] [CommRing R] (ψ : A →+* A') (hψ : ψ.IsIntegral) (ρ : A' →+* R)
    (hρ : Function.Injective ρ) (κ : K →+* R) (hκ : Function.Bijective κ)
    (h : ρ.comp ψ = κ.comp (algebraMap A K)) :
    Function.Bijective ψ := by
  have h' : ∀ a, ρ (ψ a) = κ (algebraMap A K a) := fun a => congrArg (fun φ => φ a) h
  refine ⟨fun a b hab => IsFractionRing.injective A K (hκ.1 ?_), fun a' => ?_⟩
  · rw [← h', ← h', hab]
  · obtain ⟨k, hk⟩ := hκ.2 (ρ a')
    obtain ⟨p, hpm, hp⟩ := hψ a'
    have hint : _root_.IsIntegral A k := by
      refine ⟨p, hpm, hκ.1 ?_⟩
      rw [map_zero, Polynomial.hom_eval₂, ← h, hk, ← Polynomial.hom_eval₂, hp, map_zero]
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    exact ⟨y, hρ (by rw [h', hk])⟩

end
