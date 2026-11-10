module

public import StacksFrontier.AlgebraicGeometry.Properties.UnibranchReducedNormal
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.PullbackCriteria
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.LocalProperty
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GeometricBranches
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.HochsterHuneke.Local
public import StacksFrontier.RingTheory.Nagata.N1
public import StacksFrontier.RingTheory.NormalLocus.Open
import all StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GeometricBranches
import all StacksFrontier.RingTheory.NormalLocus.Open

/-!
# Geometric unibranchness near a generic point

A Nagata scheme is geometrically unibranch on an open neighbourhood of the generic point of each
irreducible component. The geometric unibranch condition ignores nilpotents
(`IsGeometricallyUnibranchRing` is a condition on the reduction), so the statement is about the
normal locus of the reduction.

## Main results

* `Stacks.EtaleCohomology.exists_notMem_forall_isGeometricallyUnibranchRing_localization`: for a
  minimal prime `𝔭` of a Nagata ring `A` there is `s ∉ 𝔭` with `A_𝔮` geometrically unibranch for
  every prime `𝔮` not containing `s`.
* `Stacks.EtaleCohomology.exists_mem_forall_isGeometricallyUnibranchAt`: a Nagata scheme is
  geometrically unibranch on an open neighbourhood of the generic point of each irreducible
  component.

## References

* [Stacks Project, Tag 0333](https://stacks.math.columbia.edu/tag/0333)
* [Stacks Project, Tag 0BQ3](https://stacks.math.columbia.edu/tag/0BQ3)
* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
-/

/-- If the localization of a domain `R` away from `f` is integrally closed, then so is its
localization at every prime `q` not containing `f`. -/
private theorem isIntegrallyClosed_atPrime_of_isIntegrallyClosed_away {R : Type*} [CommRing R]
    [IsDomain R] {f : R} (hf : IsIntegrallyClosed (Localization.Away f)) {q : Ideal R}
    [q.IsPrime] (hfq : f ∉ q) : IsIntegrallyClosed (Localization.AtPrime q) :=
  Stacks.NormalLocus.OpenInSpectrum.isIntegrallyClosed_atPrime_of_notMem hf hfq

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.EtaleCohomology

section Ring

variable {A : Type u} [CommRing A]

/-- In a Noetherian ring, a minimal prime `𝔭` misses an element lying in all the other minimal
primes. -/
theorem exists_notMem_forall_mem_minimalPrimes [IsNoetherianRing A] {𝔭 : Ideal A}
    (h𝔭 : 𝔭 ∈ minimalPrimes A) :
    ∃ g ∉ 𝔭, ∀ 𝔭' ∈ minimalPrimes A, 𝔭' ≠ 𝔭 → g ∈ 𝔭' := by
  classical
  have := h𝔭.isPrime
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hne : ∀ 𝔭' ∈ minimalPrimes A, 𝔭' ≠ 𝔭 → ∃ a ∈ 𝔭', a ∉ 𝔭 := by
    intro 𝔭' h𝔭' hne
    by_contra hall
    push Not at hall
    exact hne (le_antisymm hall (h𝔭.2 ⟨h𝔭'.isPrime, bot_le⟩ hall))
  choose! a ha ha' using hne
  let S := hfin.toFinset.filter (· ≠ 𝔭)
  refine ⟨∏ 𝔭' ∈ S, a 𝔭', ?_, fun 𝔭' h𝔭' hne => ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨𝔭', h𝔭', hmem⟩
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset] at h𝔭'
    exact ha' 𝔭' h𝔭'.1 h𝔭'.2 hmem
  · exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (by simp [S, h𝔭', hne]))
      (ha 𝔭' h𝔭' hne)

/-- If `g` lies in every minimal prime but `𝔭`, then at a prime `𝔮 ⊇ 𝔭` not containing `g` the
nilradical of the local ring `A_𝔮` is the extension of `𝔭`. -/
theorem nilradical_localization_atPrime_eq_map {𝔭 𝔮 : Ideal A} [𝔭.IsPrime] [𝔮.IsPrime]
    (h𝔭 : 𝔭 ∈ minimalPrimes A) {g : A} (hg : ∀ 𝔭' ∈ minimalPrimes A, 𝔭' ≠ 𝔭 → g ∈ 𝔭')
    (hle : 𝔭 ≤ 𝔮) (hg𝔮 : g ∉ 𝔮) :
    nilradical (Localization.AtPrime 𝔮) = 𝔭.map (algebraMap A (Localization.AtPrime 𝔮)) := by
  have hd : Disjoint (𝔮.primeCompl : Set A) (𝔭 : Set A) :=
    Set.disjoint_left.2 fun x hx hx' => hx (hle hx')
  have : (𝔭.map (algebraMap A (Localization.AtPrime 𝔮))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔮.primeCompl _ 𝔭 inferInstance hd
  refine le_antisymm (nilradical_le_prime _) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
  have hag : a * g ∈ nilradical A := by
    rw [nilradical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro 𝔭' h𝔭'
    by_cases h : 𝔭' = 𝔭
    · subst h; exact Ideal.mul_mem_right _ _ ha
    · exact Ideal.mul_mem_left _ _ (hg 𝔭' h𝔭' h)
  obtain ⟨m, hm⟩ := (mem_nilradical.1 hag)
  have hu : IsUnit (algebraMap A (Localization.AtPrime 𝔮) g) :=
    IsLocalization.map_units (Localization.AtPrime 𝔮) (⟨g, hg𝔮⟩ : 𝔮.primeCompl)
  refine Ideal.mem_comap.2 (mem_nilradical.2 ⟨m, ?_⟩)
  have h0 := congrArg (algebraMap A (Localization.AtPrime 𝔮)) hm
  rw [map_zero, mul_pow, map_mul, map_pow, map_pow] at h0
  exact (hu.pow m).mul_left_eq_zero.1 h0

/-- **Near a generic point, a Nagata ring is geometrically unibranch.** Let `A` be a Nagata ring
and `𝔭` a minimal prime of `A`. There is `s ∉ 𝔭` such that the local ring `A_𝔮` is
geometrically unibranch at every prime `𝔮` not containing `s`. -/
theorem exists_notMem_forall_isGeometricallyUnibranchRing_localization (hA : IsNagataRing A)
    {𝔭 : Ideal A} (h𝔭 : 𝔭 ∈ minimalPrimes A) :
    ∃ s ∉ 𝔭, ∀ (𝔮 : Ideal A) [𝔮.IsPrime], s ∉ 𝔮 →
      IsGeometricallyUnibranchRing (Localization.AtPrime 𝔮) := by
  have := h𝔭.isPrime
  obtain ⟨g, hg𝔭, hg⟩ := exists_notMem_forall_mem_minimalPrimes h𝔭
  obtain ⟨⟨h, hh0, hhic⟩, -⟩ :=
    (isN1_iff_exists_isIntegrallyClosed_away_and_forall_isN1_atPrime (A ⧸ 𝔭)).1
      ((hA.isJapaneseRing_quotient 𝔭).finite (FractionRing (A ⧸ 𝔭)))
  obtain ⟨h', rfl⟩ := Ideal.Quotient.mk_surjective h
  have hh'𝔭 : h' ∉ 𝔭 := fun hm => hh0 (Ideal.Quotient.eq_zero_iff_mem.2 hm)
  refine ⟨g * h', fun hm => (h𝔭.isPrime.mem_or_mem hm).elim hg𝔭 hh'𝔭, fun 𝔮 _ hs => ?_⟩
  have hg𝔮 : g ∉ 𝔮 := fun hm => hs (Ideal.mul_mem_right _ _ hm)
  have hh'𝔮 : h' ∉ 𝔮 := fun hm => hs (Ideal.mul_mem_left _ _ hm)
  have hle : 𝔭 ≤ 𝔮 := by
    obtain ⟨𝔭', h𝔭', hle'⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal A) ≤ 𝔮)
    by_cases h : 𝔭' = 𝔭
    · exact h ▸ hle'
    · exact absurd (hle' (hg 𝔭' h𝔭' h)) hg𝔮
  let e : Localization.AtPrime 𝔮 ⧸ nilradical (Localization.AtPrime 𝔮) ≃+*
      Localization.AtPrime (AlgebraicGeometry.quotientPrime 𝔭 𝔮 hle).asIdeal :=
    (Ideal.quotEquivOfEq (nilradical_localization_atPrime_eq_map h𝔭 hg hle hg𝔮)).trans
      (AlgebraicGeometry.localizationQuotientAtPrimeEquiv 𝔭 𝔮 hle)
  have hic : IsIntegrallyClosed
      (Localization.AtPrime (AlgebraicGeometry.quotientPrime 𝔭 𝔮 hle).asIdeal) :=
    isIntegrallyClosed_atPrime_of_isIntegrallyClosed_away hhic
      fun hm => hh'𝔮 ((Ideal.mem_quotient_iff_mem hle).1 hm)
  have : IsDomain (Localization.AtPrime 𝔮 ⧸ nilradical (Localization.AtPrime 𝔮)) :=
    e.symm.isDomain_iff.mp inferInstance
  exact AlgebraicGeometry.isGeometricallyUnibranchRing_of_isIntegrallyClosed_quotient_nilradical
    (IsIntegrallyClosed.of_equiv e.symm)

end Ring

section Scheme

open _root_.AlgebraicGeometry

/-- **A Nagata scheme is geometrically unibranch on an open neighbourhood of each generic
point.** If `x` is the generic point of an irreducible component of a Nagata scheme `X`, there
is an open `V ∋ x` such that `X` is geometrically unibranch at every point of `V`. -/
theorem exists_mem_forall_isGeometricallyUnibranchAt {X : Scheme.{u}} (hX : IsNagataScheme X)
    (x : X) (hx : closure {x} ∈ irreducibleComponents X) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ y ∈ V, IsGeometricallyUnibranchAt X y := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hA : IsNagataRing Γ(X, U) := hX.isNagataRing_sections ⟨U, hU⟩
  obtain ⟨s, hs, hsu⟩ := exists_notMem_forall_isGeometricallyUnibranchRing_localization hA
    (primeIdealOf_mem_minimalPrimes_of_mem_genericPoints U hU x hxU hx)
  have hmem : ∀ (y : X) (hy : y ∈ U), y ∈ X.basicOpen s ↔
      s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
    intro y hy
    rw [← PrimeSpectrum.mem_basicOpen, ← hU.fromSpec_preimage_basicOpen]
    change y ∈ X.basicOpen s ↔ hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) ∈ X.basicOpen s
    rw [hU.fromSpec_primeIdealOf]
  refine ⟨X.basicOpen s, (hmem x hxU).2 hs, fun y hy => ?_⟩
  have hyU : y ∈ U := X.basicOpen_le s hy
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyU⟩
  have := hU.isLocalization_stalk ⟨y, hyU⟩
  exact isGeometricallyUnibranchRing_of_ringEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨y, hyU⟩).asIdeal)
      (X.presheaf.stalk y)).toRingEquiv (hsu _ ((hmem y hyU).1 hy))

end Scheme

end Stacks.EtaleCohomology

end
