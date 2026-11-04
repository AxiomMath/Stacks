module

public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# A rational function with the orders of a prime divisor generates a height-one prime

Let `R` be a Noetherian integrally closed domain with fraction field `K` and let `p ⊆ R` be a
prime ideal of height one. This file proves that `p` is principal as soon as there is a nonzero
`z ∈ K` whose order is `1` at `p` and `0` at every other height-one prime of `R`.

The argument is the one of [Stacks, Tag 0BE9]. Each localization `R_q` at a height-one prime is a
discrete valuation ring, so the order condition says that `z` generates `q R_q` when `q = p` and
is a unit of `R_q` otherwise. In particular `z` lies in every `R_q`, hence in `R` itself by the
description of an integrally closed Noetherian domain as the intersection of its localizations at
height-one primes (Tag 031T); writing `z = f` with `f ∈ R`, the same argument applied to `g / z`
for `g ∈ p` shows `g ∈ (f)`, and `f ∈ p` because `z` generates `p R_p`.

## Main results

* `Stacks.RingTheory.HeightOneOrders.ordFrac_ringEquiv`: the order of a fraction is computed by
  any subring of `K` isomorphic over `K` to the given one.
* `Stacks.RingTheory.HeightOneOrders.isDiscreteValuationRing_of_height_eq_one`: a localization of
  a Noetherian integrally closed domain at a height-one prime is a discrete valuation ring; its
  Noetherianness and Krull dimension are
  `Stacks.RingTheory.HeightOneOrders.isNoetherianRing_localizationAtPrime` and
  `Stacks.RingTheory.HeightOneOrders.krullDimLE_one_localizationAtPrime`.
* `Stacks.RingTheory.HeightOneOrders.isPrincipal_of_localized_generators`: a height-one prime is
  principal as soon as one element of `K` generates all of its localizations.
* `Stacks.RingTheory.HeightOneOrders.isPrincipal_of_ordFrac_eq_indicator`: the main result.

## Implementation notes

The localizations are taken as the subalgebras `Localization.subalgebra.ofField K _ _` of `K`, so
that elements of different localizations can be compared inside `K` without transporting along
isomorphisms; this is the shape in which Tag 031T is stated in this development.

## References

* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
* [Stacks Project, Tag 0AFT](https://stacks.math.columbia.edu/tag/0AFT)
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
-/

@[expose] public section

namespace Stacks.RingTheory.HeightOneOrders

/-! ### Transport of the order along an isomorphism over the fraction field -/

/-- The order of vanishing is invariant under a ring isomorphism. -/
theorem ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) : Ring.ord S (e a) = Ring.ord R a := by
  rw [Ring.ord, Module.length_quotient, Ring.ord, Module.length_quotient]
  simpa only [RingEquiv.idealComapOrderIso_symm_apply, Ideal.map_span, Set.image_singleton] using
    Order.coheight_orderIso e.idealComapOrderIso.symm (Ideal.span {a})

/-- The multiplicative order homomorphism is invariant under a ring isomorphism. -/
theorem ordMonoidWithZeroHom_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (e : R ≃+* S) (a : R) :
    Ring.ordMonoidWithZeroHom S (e a) = Ring.ordMonoidWithZeroHom R a := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_iff_ne_zero.mpr
      ((map_ne_zero_iff e e.injective).mpr ha)),
      Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_iff_ne_zero.mpr ha),
      ord_ringEquiv]

/-- Two subrings of a field which are isomorphic over it compute the same order of a fraction. -/
theorem ordFrac_ringEquiv
    {R S K : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    [Field K] [Algebra R K] [Algebra S K] [IsFractionRing R K] [IsFractionRing S K]
    (e : R ≃+* S) (he : ∀ r : R, algebraMap S K (e r) = algebraMap R K r)
    (z : K) : Ring.ordFrac S z = Ring.ordFrac R z := by
  have h (a : R) : Ring.ordFrac S (algebraMap R K a) =
      Ring.ordFrac R (algebraMap R K a) := by
    by_cases ha : a = 0
    · simp [ha]
    · rw [← he a, Ring.ordFrac_eq_ord S ((map_ne_zero_iff e e.injective).mpr ha),
        he a, Ring.ordFrac_eq_ord R ha, ordMonoidWithZeroHom_ringEquiv]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R z
  simp only [map_div₀, h]

/-! ### Descending a generator from the height-one localizations -/

/-- An element of the fraction field lying in every localization at a height-one prime lies in the
ring: this is the description of a Noetherian integrally closed domain as the intersection of
those localizations, [Stacks, Tag 031T]. -/
theorem mem_of_mem_heightOneLocalizations
    {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    {z : K}
    (hz : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      z ∈ Localization.subalgebra.ofField K _ p.asIdeal.primeCompl_le_nonZeroDivisors) :
    z ∈ (⊥ : Subalgebra R K) := by
  rw [← (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot
    (R := R) K).2.1]
  exact Algebra.mem_iInf.mpr fun p => Algebra.mem_iInf.mpr (hz p)

/-- A common generator of the localizations of a height-one prime descends to a generator. -/
theorem isPrincipal_of_localized_generators
    {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1)
    (z : K) (hz : z ≠ 0)
    (hloc : ∀ q : PrimeSpectrum R, q.asIdeal.height = 1 →
      let A := Localization.subalgebra.ofField K _ q.asIdeal.primeCompl_le_nonZeroDivisors
      ∃ f : A, (f : K) = z ∧ p.map (algebraMap R A) = Ideal.span {f}) :
    p.IsPrincipal := by
  have hzR : z ∈ (⊥ : Subalgebra R K) :=
    mem_of_mem_heightOneLocalizations fun q hq => by
      obtain ⟨f, rfl, _⟩ := hloc q hq
      exact f.property
  obtain ⟨f, hf⟩ := Algebra.mem_bot.mp hzR
  have hfmem : f ∈ p := by
    let A := Localization.subalgebra.ofField K _ p.primeCompl_le_nonZeroDivisors
    obtain ⟨f', hf', hspan⟩ := hloc ⟨p, inferInstance⟩ hp
    have heq : algebraMap R A f = f' := Subtype.ext (hf.trans hf'.symm)
    have hm : algebraMap R A f ∈ p.map (algebraMap R A) := by
      rw [hspan, heq]
      exact Ideal.mem_span_singleton_self f'
    have hc := Ideal.under_map_of_isLocalizationAtPrime p (S := A) (le_refl p)
    exact hc ▸ hm
  refine ⟨⟨f, le_antisymm ?_ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfmem))⟩⟩
  intro g hg
  have hgR : algebraMap R K g / z ∈ (⊥ : Subalgebra R K) := by
    apply mem_of_mem_heightOneLocalizations
    intro q hq
    let A := Localization.subalgebra.ofField K _ q.asIdeal.primeCompl_le_nonZeroDivisors
    obtain ⟨f', hf', hspan⟩ := hloc q hq
    have hm : algebraMap R A g ∈ Ideal.span {f'} := by
      rw [← hspan]
      exact Ideal.mem_map_of_mem _ hg
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hm
    have hval : algebraMap R K g = z * (a : K) := by
      have h := congrArg (fun b : A => (b : K)) ha
      change algebraMap R K g = (f' : K) * (a : K) at h
      exact h.trans (by rw [hf'])
    rw [hval, mul_div_cancel_left₀ _ hz]
    exact a.property
  obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hgR
  refine Ideal.mem_span_singleton.mpr ⟨a, IsFractionRing.injective R K ?_⟩
  rw [map_mul, hf, ha, mul_div_cancel₀ _ hz]

/-! ### Generators in a discrete valuation ring from the order -/

/-- In a discrete valuation ring an element of the fraction field with the order of a ring element
is a unit multiple of it, in particular comes from the ring and spans the same ideal. -/
theorem exists_generator_of_ordFrac_eq
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (z : K) (a : A)
    (h : Ring.ordFrac A z = Ring.ordFrac A (algebraMap A K a)) :
    ∃ f : A, algebraMap A K f = z ∧ Ideal.span {f} = Ideal.span {a} := by
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := A) z (algebraMap A K a) h
  refine ⟨↑u⁻¹ * a, ?_, ?_⟩
  · have hmul : u⁻¹ • (algebraMap A K a) = z := by rw [← hu, inv_smul_smul]
    simpa only [map_mul, Units.smul_def, Algebra.smul_def] using hmul
  · exact Ideal.span_singleton_mul_left_unit u⁻¹.isUnit a

/-- An element of the fraction field of a discrete valuation ring of order `1` is a unit of the
ring. -/
theorem exists_generator_of_ordFrac_eq_one
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (z : K)
    (h : Ring.ordFrac A z = 1) :
    ∃ f : A, algebraMap A K f = z ∧ Ideal.span {f} = ⊤ := by
  obtain ⟨f, hf, hspan⟩ := exists_generator_of_ordFrac_eq z (1 : A) (by simpa using h)
  exact ⟨f, hf, hspan.trans (by simp)⟩

/-- An element of the fraction field of a discrete valuation ring whose order is the valuation of
a uniformizer generates the maximal ideal. -/
theorem exists_generator_of_ordFrac_eq_exp_one
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (z : K)
    (h : Ring.ordFrac A z = WithZero.exp 1) :
    ∃ f : A, algebraMap A K f = z ∧ Ideal.span {f} = IsLocalRing.maximalIdeal A := by
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨f, hf, hspan⟩ := exists_generator_of_ordFrac_eq z a
    (h.trans (Ring.ordFrac_irreducible ha).symm)
  exact ⟨f, hf, hspan.trans ha.maximalIdeal_eq.symm⟩

/-- A localization at a height-one prime of a Noetherian ring has Krull dimension one. -/
private theorem ringKrullDim_localizationAtPrime_eq_one {R : Type*} [CommRing R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] (hp : p.height = 1)
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A p] :
    ringKrullDim A = 1 := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p A, hp]
  rfl

/-- A localization at a height-one prime of a Noetherian ring has Krull dimension at most one. -/
theorem krullDimLE_one_localizationAtPrime {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1)
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A p] :
    Ring.KrullDimLE 1 A :=
  Ring.krullDimLE_iff.mpr (ringKrullDim_localizationAtPrime_eq_one p hp A).le

/-- **A localization at a height-one prime of a Noetherian integrally closed domain is a discrete
valuation ring.** -/
theorem isDiscreteValuationRing_of_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1)
    (A : Type*) [CommRing A] [IsDomain A] [Algebra R A] [IsLocalization.AtPrime A p] :
    IsDiscreteValuationRing A := by
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A p
  have : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hdim := ringKrullDim_localizationAtPrime_eq_one p hp A
  have : Ring.KrullDimLE 1 A := krullDimLE_one_localizationAtPrime p hp A
  have : Ring.DimensionLEOne A := ⟨fun hne hprime => hprime.isMaximal_of_ne_bot hne⟩
  have : IsDedekindDomain A := { }
  have hfield : ¬ IsField A := fun h =>
    one_ne_zero (hdim.symm.trans (ringKrullDim_eq_zero_of_isField h))
  exact ((IsDiscreteValuationRing.TFAE A hfield).out 1 3).mpr
    (show IsDedekindDomain A from inferInstance)

/-- **A rational function with the orders of a prime divisor generates its height-one ideal.**
Let `R` be a Noetherian integrally closed domain with fraction field `K` and `p` a prime of
height one. If a nonzero `z ∈ K` has order `1` at `p` and order `0` at every other height-one
prime, then `p` is principal. -/
theorem isPrincipal_of_ordFrac_eq_indicator
    {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1)
    (z : K) (hz : z ≠ 0)
    (hord : ∀ (q : PrimeSpectrum R) (hq : q.asIdeal.height = 1),
      letI : IsDiscreteValuationRing
          (Localization.subalgebra.ofField K _ q.asIdeal.primeCompl_le_nonZeroDivisors) :=
        isDiscreteValuationRing_of_height_eq_one q.asIdeal hq _
      Ring.ordFrac
          (Localization.subalgebra.ofField K _ q.asIdeal.primeCompl_le_nonZeroDivisors) z =
        if q.asIdeal = p then WithZero.exp 1 else 1) :
    p.IsPrincipal := by
  classical
  apply isPrincipal_of_localized_generators p hp z hz
  intro q hq
  let A := Localization.subalgebra.ofField K _ q.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsDiscreteValuationRing A :=
    isDiscreteValuationRing_of_height_eq_one q.asIdeal hq A
  by_cases heq : q.asIdeal = p
  · have ho : Ring.ordFrac A z = WithZero.exp 1 := by simpa [heq] using hord q hq
    obtain ⟨f, hf, hspan⟩ := exists_generator_of_ordFrac_eq_exp_one z ho
    refine ⟨f, hf, ?_⟩
    rw [hspan, ← heq]
    exact IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal A
  · have ho : Ring.ordFrac A z = 1 := by simpa [heq] using hord q hq
    obtain ⟨f, hf, hspan⟩ := exists_generator_of_ordFrac_eq_one z ho
    refine ⟨f, hf, ?_⟩
    rw [hspan]
    exact IsLocalization.AtPrime.map_eq_top_of_not_le (S := A) (p := q.asIdeal)
      fun hle => heq (Ideal.eq_of_le_of_height_le p hle (by rw [hp, hq])).symm

end Stacks.RingTheory.HeightOneOrders

end
