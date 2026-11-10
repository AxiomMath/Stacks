module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient
public import StacksFrontier.RingTheory.Nagata.N1
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Shrinking to a normal neighbourhood in a Nagata ring

Let `R` be a Nagata ring all of whose localizations at primes are reduced, and let `𝔭` be a prime
at which the local ring `R_𝔭` is a normal domain. Then the same holds at every prime in a
basic open neighbourhood of `𝔭`: there is `t ∉ 𝔭` such that `R_𝔮` is a normal domain for every
prime `𝔮` with `t ∉ 𝔮`. This is the shrinking step used when producing a chart on which a scheme
is normal.

## Main results

* `exists_notMem_forall_isDomain_and_isIntegrallyClosed_of_isNagataRing_away`: the shrinking
  step, with reducedness assumed only away from an element `u ∉ 𝔭` and the returned `t`
  divisible by `u`. Normality is spelled `IsDomain` together with `IsIntegrallyClosed`, Mathlib
  having no predicate for a normal ring.
* `exists_notMem_forall_isDomain_and_isIntegrallyClosed_of_isNagataRing`: its case `u = 1`, with
  reducedness assumed at every prime.

Along the way, in the namespace `Stacks.NagataNormalShrink`:

* `minimalPrimes_eq_preimage`: the minimal primes of a localization are exactly the primes
  contracting to a minimal prime.
* `eq_under_bot_of_mem_minimalPrimes`: at a prime with a domain local ring there is only one
  minimal prime below, namely the kernel of the localization map.
* `map_eq_bot_of_unique_minimalPrime`: if `p₀` is the only minimal prime below `𝔮` and `R_𝔮` is
  reduced, then `p₀` extends to `0` in `R_𝔮`.
* `nonempty_ringEquiv_atPrime_quotient`: consequently `R_𝔮` is the localization of `R ⧸ p₀` at
  `𝔮 / p₀`.

## Implementation notes

The whole argument is a transfer to the domain `R ⧸ p₀`, where `p₀` is the unique minimal prime
of `R` below `𝔭`. Uniqueness of `p₀` below `𝔭` is what `IsDomain (Localization.AtPrime 𝔭)` says,
via `IsLocalization.minimalPrimes_map`; a single element `t₁ ∉ 𝔭` lying in all the *other*
minimal primes — these are finite in number, `R` being Noetherian — propagates that uniqueness
to every prime `𝔮` with `t₁ ∉ 𝔮`. Reducedness then forces `p₀ R_𝔮 = 0`, so `R_𝔮` is the
localization of `R ⧸ p₀` at `𝔮 / p₀` and the question becomes one about the domain `R ⧸ p₀`.

There the Nagata hypothesis gives that `R ⧸ p₀` is N-1 (Tag 0333 applies to it), so its normal
locus is open (Tag 0332) and contains `𝔭 / p₀`; a basic open neighbourhood supplies the second
factor `t₂`, and `t = t₁ * t₂` works.

Both halves of the conclusion travel along the ring isomorphism `R_𝔮 ≅ (R ⧸ p₀)_{𝔮 / p₀}`:
`IsDomain` by `Function.Injective.isDomain` and `IsIntegrallyClosed` by
`IsIntegrallyClosed.of_equiv`.

## References

* [Stacks Project, Tag 0332](https://stacks.math.columbia.edu/tag/0332)
* [Stacks Project, Tag 0333](https://stacks.math.columbia.edu/tag/0333)
* [Stacks Project, Tag 033G](https://stacks.math.columbia.edu/tag/033G)
-/

@[expose] public section

universe u

namespace Stacks.NagataNormalShrink

variable {R : Type u} [CommRing R]

/-- The minimal primes of a localization of `R` are exactly the primes of the localization whose
contraction to `R` is a minimal prime of `R`. -/
public theorem minimalPrimes_eq_preimage (M : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization M A] :
    minimalPrimes A = Ideal.under R ⁻¹' minimalPrimes R := by
  have h := IsLocalization.minimalPrimes_map M A (⊥ : Ideal R)
  rwa [Ideal.map_bot] at h

/-- A proper ideal of a localization at the prime `𝔮` contracts into `𝔮`. -/
public theorem under_le_of_ne_top (𝔮 : Ideal R) [𝔮.IsPrime] (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization.AtPrime A 𝔮] {P : Ideal A} (hP : P ≠ ⊤) : P.under R ≤ 𝔮 := by
  have hd : Disjoint (𝔮.primeCompl : Set R) (P.under R : Set R) :=
    (IsLocalization.disjoint_under_iff 𝔮.primeCompl A P).mpr hP
  intro x hx
  by_contra hx𝔮
  exact Set.disjoint_left.mp hd hx𝔮 hx

/-- If the localization of `R` at the prime `𝔭` is a domain, every minimal prime of `R` below `𝔭`
is the kernel of the localization map. In particular there is only one of them. -/
@[ega "IV 5.13.5" "partial"]
public theorem eq_under_bot_of_mem_minimalPrimes {𝔭 : Ideal R} [𝔭.IsPrime]
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A 𝔭] [IsDomain A]
    {p : Ideal R} (hp : p ∈ minimalPrimes R) (hple : p ≤ 𝔭) :
    p = (⊥ : Ideal A).under R := by
  have hd : Disjoint (𝔭.primeCompl : Set R) (p : Set R) := by
    rw [Set.disjoint_left]
    exact fun x hx hxp => hx (hple hxp)
  have hP : (p.map (algebraMap R A)).under R = p :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔭.primeCompl A hp.isPrime hd
  have hmem : p.map (algebraMap R A) ∈ minimalPrimes A := by
    rw [minimalPrimes_eq_preimage 𝔭.primeCompl A, Set.mem_preimage, hP]
    exact hp
  rw [IsDomain.minimalPrimes_eq_singleton_bot A, Set.mem_singleton_iff] at hmem
  exact hP.symm.trans (congrArg (Ideal.under R) hmem)

/-- If `p₀` is the only minimal prime of `R` contained in the prime `𝔮`, and the localization
`A` of `R` at `𝔮` is reduced, then `p₀` extends to the zero ideal of `A`. -/
public theorem map_eq_bot_of_unique_minimalPrime {p₀ : Ideal R} (hp₀ : p₀ ∈ minimalPrimes R)
    {𝔮 : Ideal R} [𝔮.IsPrime] (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization.AtPrime A 𝔮] [IsReduced A]
    (huniq : ∀ p ∈ minimalPrimes R, p ≤ 𝔮 → p = p₀) :
    p₀.map (algebraMap R A) = ⊥ := by
  have : p₀.IsPrime := hp₀.isPrime
  have hset : (p₀.map (algebraMap R A)).minimalPrimes = minimalPrimes A := by
    rw [IsLocalization.minimalPrimes_map 𝔮.primeCompl A p₀,
      minimalPrimes_eq_preimage 𝔮.primeCompl A, Ideal.minimalPrimes_eq_subsingleton_self]
    ext P
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun h => h ▸ hp₀, fun h => huniq _ h (under_le_of_ne_top 𝔮 A ?_)⟩
    rintro rfl
    exact h.isPrime.ne_top Ideal.comap_top
  have hrad : (p₀.map (algebraMap R A)).radical = ⊥ := by
    rw [← Ideal.sInf_minimalPrimes, hset, Ideal.sInf_minimalPrimes]
    simp
  exact le_bot_iff.mp (Ideal.le_radical.trans hrad.le)

/-- The image of a prime `𝔮 ⊇ p₀` in `R ⧸ p₀` is prime. -/
public theorem isPrime_map_quotient {p₀ 𝔮 : Ideal R} [𝔮.IsPrime] (h : p₀ ≤ 𝔮) :
    (𝔮.map (Ideal.Quotient.mk p₀)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

/-- The image of a prime `𝔮 ⊇ p₀` in `R ⧸ p₀` contracts back to `𝔮`. -/
public theorem comap_map_quotient {p₀ 𝔮 : Ideal R} (h : p₀ ≤ 𝔮) :
    (𝔮.map (Ideal.Quotient.mk p₀)).comap (Ideal.Quotient.mk p₀) = 𝔮 := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr h]

/-- **The localization at `𝔮` is a localization of `R ⧸ p₀`.** If `p₀` is the only minimal prime
of `R` below the prime `𝔮` and `R_𝔮` is reduced, then `R_𝔮` is isomorphic, as a ring, to the
localization of `R ⧸ p₀` at the prime `𝔮'` lying over `𝔮`. -/
public theorem nonempty_ringEquiv_atPrime_quotient {p₀ : Ideal R} (hp₀ : p₀ ∈ minimalPrimes R)
    {𝔮 : Ideal R} [𝔮.IsPrime] (hred : IsReduced (Localization.AtPrime 𝔮))
    (huniq : ∀ p ∈ minimalPrimes R, p ≤ 𝔮 → p = p₀)
    (𝔮' : Ideal (R ⧸ p₀)) [𝔮'.IsPrime]
    (h𝔮' : 𝔮'.comap (Ideal.Quotient.mk p₀) = 𝔮) :
    Nonempty (Localization.AtPrime 𝔮 ≃+* Localization.AtPrime 𝔮') := by
  have := hred
  have : p₀.IsPrime := hp₀.isPrime
  have hbot : p₀.map (algebraMap R (Localization.AtPrime 𝔮)) = ⊥ :=
    map_eq_bot_of_unique_minimalPrime hp₀ (Localization.AtPrime 𝔮) huniq
  have := isLocalization_atPrime_quotient 𝔮 (Localization.AtPrime 𝔮) p₀ 𝔮' h𝔮'
  exact ⟨((RingEquiv.quotientBot (Localization.AtPrime 𝔮)).symm.trans
    (Ideal.quotEquivOfEq hbot.symm)).trans
      (IsLocalization.algEquiv 𝔮'.primeCompl
        (Localization.AtPrime 𝔮 ⧸ p₀.map (algebraMap R (Localization.AtPrime 𝔮)))
        (Localization.AtPrime 𝔮')).toRingEquiv⟩

/-- `IsDomain` travels backwards along a ring isomorphism. -/
public theorem isDomain_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    [IsDomain B] : IsDomain A :=
  Function.Injective.isDomain (e : A →+* B) e.injective

end Stacks.NagataNormalShrink

open Stacks.NagataNormalShrink in
/-- **The normal locus of a Nagata ring is open away from the non-reduced locus**, in the local
form in which the shrinking step uses it. Let `R` be a Nagata ring, `u ∉ 𝔭` an element such that
`R_𝔮` is reduced for every prime `𝔮` avoiding `u`, and suppose `R_𝔭` is a normal domain. Then
there is `t ∉ 𝔭`, divisible by `u`, such that `R_𝔮` is a normal domain for every prime `𝔮` with
`t ∉ 𝔮`.

Normality of a local ring is spelled as `IsDomain` together with `IsIntegrallyClosed`, Mathlib
having no predicate for a normal ring. -/
public theorem exists_notMem_forall_isDomain_and_isIntegrallyClosed_of_isNagataRing_away
    {R : Type u} [CommRing R] (hR : IsNagataRing R)
    {𝔭 : Ideal R} [𝔭.IsPrime] (u : R) (hu : u ∉ 𝔭)
    (hred : ∀ (𝔮 : Ideal R) [𝔮.IsPrime], u ∉ 𝔮 → IsReduced (Localization.AtPrime 𝔮))
    (hdom : IsDomain (Localization.AtPrime 𝔭))
    (hic : IsIntegrallyClosed (Localization.AtPrime 𝔭)) :
    ∃ t ∉ 𝔭, ∀ (𝔮 : Ideal R) [𝔮.IsPrime], t ∉ 𝔮 →
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮) := by
  classical
  have : IsNoetherianRing R := hR.isNoetherianRing
  have := hdom
  have := hic
  -- The unique minimal prime `p₀` of `R` below `𝔭`.
  obtain ⟨p₀, hp₀min, hp₀𝔭⟩ : ∃ p ∈ minimalPrimes R, p ≤ 𝔭 :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) bot_le
  have huniq𝔭 : ∀ p ∈ minimalPrimes R, p ≤ 𝔭 → p = p₀ := fun p hp hple =>
    (eq_under_bot_of_mem_minimalPrimes (Localization.AtPrime 𝔭) hp hple).trans
      (eq_under_bot_of_mem_minimalPrimes (Localization.AtPrime 𝔭) hp₀min hp₀𝔭).symm
  have : p₀.IsPrime := hp₀min.isPrime
  -- An element `t₁ ∉ 𝔭` lying in every other minimal prime.
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  have hnotle : ¬ ((hfin.toFinset.erase p₀).inf id ≤ 𝔭) := by
    intro hle
    obtain ⟨p, hpF, hple⟩ := (Ideal.IsPrime.inf_le' (P := 𝔭) inferInstance).mp hle
    exact (Finset.mem_erase.mp hpF).1
      (huniq𝔭 p (hfin.mem_toFinset.mp (Finset.mem_erase.mp hpF).2) hple)
  obtain ⟨t₁, ht₁mem, ht₁⟩ : ∃ t₁ ∈ (hfin.toFinset.erase p₀).inf id, t₁ ∉ 𝔭 := by
    rw [IsConcreteLE.le_iff] at hnotle
    push Not at hnotle
    exact hnotle
  -- `t₁` propagates the uniqueness of `p₀` to every prime avoiding it.
  have key : ∀ (𝔮 : Ideal R), 𝔮.IsPrime → t₁ ∉ 𝔮 →
      p₀ ≤ 𝔮 ∧ ∀ p ∈ minimalPrimes R, p ≤ 𝔮 → p = p₀ := by
    intro 𝔮 h𝔮 ht₁𝔮
    have := h𝔮
    have huniq : ∀ p ∈ minimalPrimes R, p ≤ 𝔮 → p = p₀ := by
      intro p hp hple
      by_contra hne
      have hpF : p ∈ hfin.toFinset.erase p₀ :=
        Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr hp⟩
      have hle : (hfin.toFinset.erase p₀).inf id ≤ p := Finset.inf_le (f := id) hpF
      exact ht₁𝔮 (hple (hle ht₁mem))
    obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := 𝔮) bot_le
    exact ⟨huniq p hp hple ▸ hple, huniq⟩
  -- The quotient `R ⧸ p₀` is a Noetherian Japanese domain, hence N-1.
  have : IsJapaneseRing (R ⧸ p₀) := hR.isJapaneseRing_quotient p₀
  have hN1 : IsN1 (R ⧸ p₀) := IsJapaneseRing.finite (FractionRing (R ⧸ p₀))
  obtain ⟨⟨f, hf0, hfic⟩, -⟩ :=
    (isN1_iff_exists_isIntegrallyClosed_away_and_forall_isN1_atPrime (R ⧸ p₀)).mp hN1
  have hopen := PrimeSpectrum.isOpen_setOf_isIntegrallyClosed_atPrime (R := R ⧸ p₀) hf0 hfic
  -- Every prime `𝔮 ⊇ p₀` with `p₀` the only minimal prime below it comes from a point of `R ⧸ p₀`.
  have hlift : ∀ (𝔮 : Ideal R) [𝔮.IsPrime], p₀ ≤ 𝔮 → IsReduced (Localization.AtPrime 𝔮) →
      (∀ p ∈ minimalPrimes R, p ≤ 𝔮 → p = p₀) → ∃ q : PrimeSpectrum (R ⧸ p₀),
        q.asIdeal.comap (Ideal.Quotient.mk p₀) = 𝔮 ∧
          Nonempty (Localization.AtPrime 𝔮 ≃+* Localization.AtPrime q.asIdeal) :=
    fun 𝔮 _ hle hr huniq =>
      have := isPrime_map_quotient hle
      ⟨⟨_, this⟩, comap_map_quotient hle,
        nonempty_ringEquiv_atPrime_quotient hp₀min hr huniq _ (comap_map_quotient hle)⟩
  -- `𝔭 / p₀` lies in the normal locus of `Spec (R ⧸ p₀)`.
  obtain ⟨q𝔭, hq𝔭, ⟨e𝔭⟩⟩ := hlift 𝔭 hp₀𝔭 (hred 𝔭 hu) huniq𝔭
  have hmem : q𝔭 ∈
      {q : PrimeSpectrum (R ⧸ p₀) | IsIntegrallyClosed (Localization.AtPrime q.asIdeal)} :=
    IsIntegrallyClosed.of_equiv e𝔭
  -- A basic open neighbourhood of `𝔭 / p₀` inside it supplies the second factor.
  obtain ⟨V, hVb, hVmem, hVsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem hopen
  obtain ⟨g, rfl⟩ := hVb
  obtain ⟨t₂, rfl⟩ := Ideal.Quotient.mk_surjective g
  have ht₂ : t₂ ∉ 𝔭 := fun h => hVmem (by rwa [← hq𝔭] at h)
  refine ⟨u * (t₁ * t₂), fun h => (Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› h).elim hu
    (fun h' => (Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› h').elim ht₁ ht₂), ?_⟩
  intro 𝔮 _ ht
  have hu𝔮 : u ∉ 𝔮 := fun h => ht (Ideal.mul_mem_right _ _ h)
  have ht₁𝔮 : t₁ ∉ 𝔮 := fun h => ht (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ h))
  have ht₂𝔮 : t₂ ∉ 𝔮 := fun h => ht (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ h))
  obtain ⟨hp₀𝔮, huniq𝔮⟩ := key 𝔮 inferInstance ht₁𝔮
  obtain ⟨q, hq, ⟨e⟩⟩ := hlift 𝔮 hp₀𝔮 (hred 𝔮 hu𝔮) huniq𝔮
  have hg𝔮 : q ∈ PrimeSpectrum.basicOpen (Ideal.Quotient.mk p₀ t₂) := fun hcon =>
    ht₂𝔮 (by rwa [← hq])
  have : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) := hVsub hg𝔮
  have : IsDomain (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  exact ⟨isDomain_of_ringEquiv e, IsIntegrallyClosed.of_equiv e.symm⟩

/-- **The normal locus of a Nagata ring with reduced local rings is open**, in the local form in
which the shrinking step uses it. Let `R` be a Nagata ring whose localization at every prime is
reduced, and let `𝔭` be a prime at which `R_𝔭` is a normal domain. Then there is `t ∉ 𝔭` such
that `R_𝔮` is a normal domain for every prime `𝔮` with `t ∉ 𝔮`.

This is the case `u = 1` of
`exists_notMem_forall_isDomain_and_isIntegrallyClosed_of_isNagataRing_away`. -/
public theorem exists_notMem_forall_isDomain_and_isIntegrallyClosed_of_isNagataRing
    {R : Type u} [CommRing R] (hR : IsNagataRing R)
    (hred : ∀ (𝔮 : Ideal R) [𝔮.IsPrime], IsReduced (Localization.AtPrime 𝔮))
    {𝔭 : Ideal R} [𝔭.IsPrime]
    (hdom : IsDomain (Localization.AtPrime 𝔭))
    (hic : IsIntegrallyClosed (Localization.AtPrime 𝔭)) :
    ∃ t ∉ 𝔭, ∀ (𝔮 : Ideal R) [𝔮.IsPrime], t ∉ 𝔮 →
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮) :=
  exists_notMem_forall_isDomain_and_isIntegrallyClosed_of_isNagataRing_away hR 1
    ((Ideal.ne_top_iff_one 𝔭).mp ‹𝔭.IsPrime›.ne_top) (fun 𝔮 _ _ => hred 𝔮) hdom hic

end
