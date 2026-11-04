module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Tactic.Ring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Minimal primes, localizations and reduced rings

If `R` is a reduced commutative ring, then the natural map `R → ∏_{p minimal} R_p` is an embedding
into a product of fields, and the union of the minimal primes of `R` is the set of zero divisors of
`R`.

A minimal prime outside a quasi-compact open of `Spec R` has a basic open neighbourhood disjoint
from that open. Every element of the maximal ideal of the localization at a minimal prime is
nilpotent; for a reduced ring, this localization is a field.

## Main definitions

* `localizationProdMap`: the natural map `R → ∏_{p minimal} R_p`.
* `zeroDivisorSet`: the set of zero divisors of `R`.

## Main results

* `localizationProdMap_injective`: for `R` reduced, `localizationProdMap R` is injective.
* `exists_injective_ringHom_pi_field`: a reduced commutative ring embeds into a product of fields.
* `iUnion_minimalPrimes_eq_zeroDivisors`: for `R` reduced, the union of the minimal primes is the
  set of zero divisors.
* `PrimeSpectrum.exists_disjoint_basicOpen_of_mem_minimalPrimes`: a minimal prime `𝔭` outside a
  quasi-compact open `W` has a basic open neighbourhood `D(f)` disjoint from `W`.
* `minimal_prime_maximalIdeal_isNilpotent`: every element of the maximal ideal of the localization
  at a minimal prime is nilpotent.
* `minimal_prime_reduced_localization_isField`: the localization of a reduced ring at a minimal
  prime is a field.

## References

* [Stacks Project, Tag 00EW](https://stacks.math.columbia.edu/tag/00EW)
* [Stacks Project, Tag 00EV](https://stacks.math.columbia.edu/tag/00EV)
* [Stacks Project, Tag 00EU](https://stacks.math.columbia.edu/tag/00EU)
-/

@[expose] public section

variable (R : Type*) [CommSemiring R]

/-- The natural ring map `R → ∏_{p ∈ minimalPrimes R} R_p` whose components are the localizations
at each minimal prime. -/
noncomputable def localizationProdMap :
    R →+* (∀ p : minimalPrimes R, @Localization.AtPrime R _ p.1 p.2.isPrime) :=
  RingHom.pi (fun p =>
    haveI : p.val.IsPrime := p.property.isPrime
    algebraMap R (Localization.AtPrime (p.val : Ideal R)))

/-- The `p`-component of `localizationProdMap R x` is the image of `x` in `R_p`. -/
@[simp]
theorem localizationProdMap_apply (x : R) (p : minimalPrimes R) :
    haveI := p.2.isPrime
    localizationProdMap R x p = algebraMap R (Localization.AtPrime p.1) x :=
  rfl

/-- The set of zero divisors of `R`: elements `x` with `x * y = 0` for some nonzero `y`. -/
def zeroDivisorSet : Set R := { x : R | ∃ y : R, y ≠ 0 ∧ x * y = 0 }

variable {R} in
/-- Membership in the set of zero divisors is witnessed by a nonzero annihilated element. -/
theorem mem_zeroDivisorSet {x : R} : x ∈ zeroDivisorSet R ↔ ∃ y, y ≠ 0 ∧ x * y = 0 := Iff.rfl

/-! ## Auxiliary facts about minimal primes -/

/-- The nilradical of a commutative semiring equals the infimum of its minimal prime ideals. -/
@[ega "0 1.1.1" "Case a = (0)"]
lemma nilradical_eq_sInf_minimalPrimes :
    nilradical R = sInf (minimalPrimes R) := by
  rw [nilradical_eq_sInf]
  refine le_antisymm (le_sInf fun p hp ↦ sInf_le hp.isPrime) (le_sInf fun p hp ↦ ?_)
  have : p.IsPrime := hp
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ p)
  exact (sInf_le hq).trans hqp

/-- In a reduced commutative semiring, the infimum of all minimal primes is `⊥`. -/
@[ega "0 1.1.1" "special case", ega "IV 20.1.3.1" "partial"]
lemma sInf_minimalPrimes_eq_bot [IsReduced R] :
    sInf (minimalPrimes R) = (⊥ : Ideal R) :=
  (nilradical_eq_sInf_minimalPrimes R).symm.trans (nilradical_eq_zero R)

/-- An element of a reduced commutative semiring is zero iff it lies in every minimal prime. -/
@[ega "IV 20.1.3.1" "affine zero detection"]
lemma eq_zero_iff_mem_all_minimalPrimes [IsReduced R] (x : R) :
    x = 0 ↔ ∀ p ∈ minimalPrimes R, x ∈ p := by
  refine ⟨fun hx p _ ↦ hx ▸ p.zero_mem, fun hx ↦ ?_⟩
  have hmem : x ∈ sInf (minimalPrimes R) := Submodule.mem_sInf.mpr hx
  rwa [sInf_minimalPrimes_eq_bot, Ideal.mem_bot] at hmem

/-! ## Localizing at a minimal prime gives a field -/

/-- For a minimal prime `p`, the localization `Localization.AtPrime p` has Krull dimension at most
`0`. -/
@[ega "0 1.5.8" "more general", ega "I 7.1.5" "special case"]
lemma krullDimLE_localization_atPrime_minimal
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    haveI : p.IsPrime := hp.isPrime
    Ring.KrullDimLE 0 (Localization.AtPrime p) :=
  have := hp.isPrime
  .of_isLocalization p hp _

/-- The localization of a reduced ring at a minimal prime is a field. -/
@[stacks 00EW "2, the factors are fields",
  ega "0 1.5.8" "reduced ring",
  ega "IV 20.1.3.1" "field-stalk clause"]
lemma isField_localizationAtPrime_of_minimal (R : Type*) [CommRing R] [IsReduced R]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    haveI : p.IsPrime := hp.isPrime
    IsField (Localization.AtPrime p) := by
  have := hp.isPrime
  have := krullDimLE_localization_atPrime_minimal R p hp
  exact Ring.KrullDimLE.isField_of_isReduced

/-! ## Computing the kernel of `R → R_p` -/

/-- The image of `x : R` in `Localization.AtPrime p` is zero iff some `s ∉ p` annihilates `x` in
`R`. -/
lemma algebraMap_eq_zero_iff_atPrime
    (p : Ideal R) [p.IsPrime] (x : R) :
    (algebraMap R (Localization.AtPrime p)) x = 0 ↔
      ∃ s : p.primeCompl, (s : R) * x = 0 :=
  IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) x

/-- For a reduced ring and a minimal prime `p`, every element of `p` maps to zero in
`Localization.AtPrime p`. -/
lemma algebraMap_eq_zero_of_mem_minimalPrime (R : Type*) [CommRing R] [IsReduced R]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) (x : R) (hx : x ∈ p) :
    haveI : p.IsPrime := hp.isPrime
    (algebraMap R (Localization.AtPrime p)) x = 0 := by
  have := hp.isPrime
  have hField := isField_localizationAtPrime_of_minimal R p hp
  by_contra hne
  obtain ⟨b, hb⟩ := hField.mul_inv_cancel hne
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p x).mp
    ⟨⟨_, b, hb, (hField.mul_comm _ _).trans hb⟩, rfl⟩ hx

/-- Conversely, if `s * x = 0` and `s ∉ p` with `p` prime, then `x ∈ p`. -/
lemma mem_prime_of_smul_eq_zero
    (p : Ideal R) [hp : p.IsPrime] (x s : R) (hs : s ∉ p) (h : s * x = 0) :
    x ∈ p :=
  (hp.mem_or_mem (h ▸ p.zero_mem : s * x ∈ p)).resolve_left hs

/-! ## Reduced rings embed into products of fields -/

/-- The map `R → ∏_{p minimal} R_p` from a reduced commutative ring to the product of localizations
at minimal primes is injective. -/
@[stacks 00EW "2, injectivity; the factors are fields by isField_localizationAtPrime_of_minimal"]
theorem localizationProdMap_injective (R : Type*) [CommRing R] [IsReduced R] :
    Function.Injective (localizationProdMap R) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine (eq_zero_iff_mem_all_minimalPrimes R x).mpr fun p hp ↦ ?_
  have := hp.isPrime
  obtain ⟨s, hs⟩ := (algebraMap_eq_zero_iff_atPrime R p x).mp (by simpa using congrFun hx ⟨p, hp⟩)
  exact mem_prime_of_smul_eq_zero R p x s s.property hs

/-- A reduced commutative ring embeds into a product of fields, indexed by a type in the universe
of `R`. -/
@[stacks 00EW "1"]
theorem exists_injective_ringHom_pi_field.{u} {R : Type u} [CommRing R]
    [IsReduced R] :
    ∃ (ι : Type u) (K : ι → Type u) (_ : ∀ i, Field (K i))
      (f : R →+* (∀ i, K i)), Function.Injective f :=
  ⟨(minimalPrimes R : Type u),
    fun p => @Localization.AtPrime R _ p.val p.property.isPrime,
    (fun p =>
      have : p.val.IsPrime := p.property.isPrime
      (isField_localizationAtPrime_of_minimal R p.val p.property).toField),
    localizationProdMap R, localizationProdMap_injective R⟩

/-! ## Zero divisors are the union of minimal primes -/

/-- For a reduced commutative ring, every element of every minimal prime is a zero divisor. -/
@[ega "IV 20.1.3.1" "converse direction"]
lemma mem_minimalPrime_imp_zeroDivisor (R : Type*) [CommRing R] [IsReduced R]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) (x : R) (hx : x ∈ p) :
    x ∈ zeroDivisorSet R := by
  have := hp.isPrime
  obtain ⟨s, hs⟩ := (algebraMap_eq_zero_iff_atPrime R p x).mp
    (algebraMap_eq_zero_of_mem_minimalPrime R p hp x hx)
  exact mem_zeroDivisorSet.mpr
    ⟨s, fun h0 ↦ s.property (h0 ▸ p.zero_mem), (mul_comm _ _).trans hs⟩

/-- For a reduced commutative semiring, every zero divisor lies in some minimal prime. -/
@[ega "IV 20.1.3.1" "partial, special case"]
lemma zeroDivisor_imp_mem_minimalPrime [IsReduced R]
    (x : R) (hx : x ∈ zeroDivisorSet R) :
    ∃ p ∈ minimalPrimes R, x ∈ p := by
  obtain ⟨y, hy, hxy⟩ := mem_zeroDivisorSet.mp hx
  obtain ⟨p, hp, hyp⟩ : ∃ p ∈ minimalPrimes R, y ∉ p := by
    by_contra! hall
    exact hy ((eq_zero_iff_mem_all_minimalPrimes R y).mpr hall)
  have := hp.isPrime
  exact ⟨p, hp, mem_prime_of_smul_eq_zero R p x y hyp ((mul_comm _ _).trans hxy)⟩

/-- The union of the minimal primes of a reduced commutative ring equals its set of zero
divisors. -/
@[stacks 00EW "3", ega "IV 20.1.3.1" "special case"]
theorem iUnion_minimalPrimes_eq_zeroDivisors (R : Type*) [CommRing R] [IsReduced R] :
    (⋃ p ∈ minimalPrimes R, (p : Set R)) = zeroDivisorSet R := by
  ext x
  simp only [Set.mem_iUnion₂, SetLike.mem_coe, exists_prop]
  exact ⟨fun ⟨p, hp, hxp⟩ ↦ mem_minimalPrime_imp_zeroDivisor R p hp x hxp,
    zeroDivisor_imp_mem_minimalPrime R x⟩

open PrimeSpectrum TopologicalSpace

/-- For each point of an open subset of `PrimeSpectrum R`, there exists a basic open neighbourhood
contained in that subset. -/
private lemma exists_basicOpen_subset_of_mem_open {R : Type*} [CommSemiring R]
    (W : Opens (PrimeSpectrum R)) (x : PrimeSpectrum R) (hx : x ∈ (W : Set (PrimeSpectrum R))) :
    ∃ r : R, x ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ∧
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆ (W : Set (PrimeSpectrum R)) := by
  obtain ⟨v, ⟨r, rfl⟩, hxv, hvW⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx W.isOpen
  exact ⟨r, hxv, hvW⟩

/-- A quasi-compact open set in `PrimeSpectrum R` is a finite union of basic opens. -/
private lemma compact_open_eq_finset_basicOpens {R : Type*} [CommSemiring R]
    (W : Opens (PrimeSpectrum R)) (hW : IsCompact (W : Set (PrimeSpectrum R))) :
    ∃ s : Finset R,
      (W : Set (PrimeSpectrum R)) =
        ⋃ g ∈ s, (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  classical
  let I : Type _ := {r : R // (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
                              (W : Set (PrimeSpectrum R))}
  let U : I → Set (PrimeSpectrum R) := fun r =>
    (PrimeSpectrum.basicOpen r.val : Set (PrimeSpectrum R))
  have hW_sub : (W : Set (PrimeSpectrum R)) ⊆ ⋃ i, U i := fun x hx => by
    obtain ⟨r, hxr, hrW⟩ := exists_basicOpen_subset_of_mem_open W x hx
    exact Set.mem_iUnion.mpr ⟨⟨r, hrW⟩, hxr⟩
  obtain ⟨t, ht⟩ :=
    hW.elim_finite_subcover U (fun _ => PrimeSpectrum.isOpen_basicOpen) hW_sub
  refine ⟨t.image (fun r : I => r.val), le_antisymm (fun x hx => ?_) (fun x hx => ?_)⟩
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion₂.mpr ⟨i.val, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hxi⟩
  · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    exact i.property hxg

/-- For any element `g` of a minimal prime `𝔭`, there exist `s ∉ 𝔭` and `k : ℕ` with
`s * g ^ k = 0`. -/
private lemma exists_mul_pow_eq_zero_of_mem_minimalPrimes
    {R : Type*} [CommSemiring R] {𝔭 : Ideal R} (h𝔭min : 𝔭 ∈ minimalPrimes R)
    {g : R} (hg : g ∈ 𝔭) :
    ∃ (s : R) (k : ℕ), s ∉ 𝔭 ∧ s * g ^ k = 0 := by
  have : 𝔭.IsPrime := h𝔭min.isPrime
  set S := Localization.AtPrime 𝔭
  have := krullDimLE_localization_atPrime_minimal R 𝔭 h𝔭min
  have hg_max : algebraMap R S g ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔭 g).mpr hg
  rw [(Ring.KrullDimLE.nilradical_eq_maximalIdeal S).symm, mem_nilradical] at hg_max
  obtain ⟨n, hn⟩ := hg_max
  rw [← map_pow, algebraMap_eq_zero_iff_atPrime] at hn
  obtain ⟨⟨s, hs⟩, hsg⟩ := hn
  exact ⟨s, n, hs, by simpa using hsg⟩

/-- Given a minimal prime `𝔭` and a finite set `gs ⊆ 𝔭`, there is a single `f ∉ 𝔭` such that
`basicOpen f` is disjoint from each `basicOpen g` for `g ∈ gs`. -/
private lemma exists_disjoint_basicOpen_finset
    {R : Type*} [CommSemiring R] {𝔭 : Ideal R} (h𝔭min : 𝔭 ∈ minimalPrimes R)
    (gs : Finset R) (hgs : ∀ g ∈ gs, g ∈ 𝔭) :
    ∃ f : R, f ∉ 𝔭 ∧
      ∀ g ∈ gs,
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) = ∅ := by
  classical
  have := h𝔭min.isPrime
  choose s k hs hsk using
    fun g (hg : g ∈ gs) => exists_mul_pow_eq_zero_of_mem_minimalPrimes h𝔭min (hgs g hg)
  refine ⟨∏ gh ∈ gs.attach, s gh.val gh.property, fun h => ?_, fun g hg => ?_⟩
  · obtain ⟨gh, -, hgh⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hs gh.val gh.property hgh
  rw [← Opens.coe_inf, ← basicOpen_mul, Opens.coe_eq_empty, basicOpen_eq_bot_iff]
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun gh : gs => s gh.val gh.property)
    (Finset.mem_attach gs ⟨g, hg⟩)
  exact .mk _ (k g hg + 1) <| by
    rw [hc, show (s g hg * c * g) ^ (k g hg + 1) =
      s g hg * g ^ k g hg * (s g hg ^ k g hg * c ^ (k g hg + 1) * g) by ring, hsk g hg, zero_mul]

/-- Let `𝔭` be a minimal prime of `R` and let `W ⊆ Spec R` be a quasi-compact open not containing
`𝔭`. Then some `f ∉ 𝔭` has `D(f)` disjoint from `W`. -/
@[stacks 00EV]
theorem PrimeSpectrum.exists_disjoint_basicOpen_of_mem_minimalPrimes
    {R : Type*} [CommSemiring R]
    {𝔭 : Ideal R} (h𝔭min : 𝔭 ∈ minimalPrimes R)
    {W : TopologicalSpace.Opens (PrimeSpectrum R)}
    (hW : IsCompact (W : Set (PrimeSpectrum R)))
    (h𝔭W : (⟨𝔭, h𝔭min.isPrime⟩ : PrimeSpectrum R) ∉ W) :
    ∃ f ∉ 𝔭,
      Disjoint (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))
        (W : Set (PrimeSpectrum R)) := by
  obtain ⟨gs, hgs⟩ := compact_open_eq_finset_basicOpens W hW
  have hg_in_𝔭 : ∀ g ∈ gs, g ∈ 𝔭 := fun g hg ↦ by
    by_contra hgp
    refine h𝔭W ?_
    rw [← SetLike.mem_coe, hgs]
    exact Set.mem_biUnion hg (by simpa [PrimeSpectrum.mem_basicOpen] using hgp)
  obtain ⟨f, hf𝔭, hfdisj⟩ := exists_disjoint_basicOpen_finset h𝔭min gs hg_in_𝔭
  refine ⟨f, hf𝔭, ?_⟩
  rw [Set.disjoint_iff_inter_eq_empty, hgs, Set.inter_iUnion₂]
  simpa using hfdisj

/-! ## Nilpotency in the localization at a minimal prime -/

open Ideal in
/-- Every element of the maximal ideal of the localization of a commutative semiring `R` at a
minimal prime `p` is nilpotent. -/
@[ega "0 1.5.8" "more general"]
theorem minimal_prime_maximalIdeal_isNilpotent
    (R : Type*) [CommSemiring R] (p : Ideal R) [p.IsPrime] (hp : p ∈ minimalPrimes R)
    (x : Localization.AtPrime p)
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p)) :
    IsNilpotent x := by
  have := krullDimLE_localization_atPrime_minimal R p hp
  exact Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hx

open Ideal in
/-- The localization of a reduced commutative ring at a minimal prime is a field. -/
@[ega "0 1.5.8" "reduced ring", ega "IV 20.1.3.1" "partial"]
theorem minimal_prime_reduced_localization_isField
    (R : Type*) [CommRing R] [IsReduced R] (p : Ideal R) [p.IsPrime]
    (hp : p ∈ minimalPrimes R) :
    IsField (Localization.AtPrime p) := by
  exact isField_localizationAtPrime_of_minimal R p hp
