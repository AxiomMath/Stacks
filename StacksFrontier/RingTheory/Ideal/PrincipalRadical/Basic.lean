module

public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.Ideal.PrincipalRadical.Length
public import StacksFrontier.RingTheory.Ideal.PrincipalRadical.SystemOfParameters
public import StacksFrontier.RingTheory.Serre.Defs
import StacksFrontier.RingTheory.Catenary.Saturated

/-!
# Existence of principal radical ideals

Let `R` be a Noetherian local normal domain. This file proves the existence statements of
Artin–Lipman: in dimension two, any finite family of height-one primes has a common nonzero
element `f` with `R / f R` reduced, and consequently every nonzero `a` in the maximal ideal
divides a power of such an element; in arbitrary dimension, assuming `R` catenary, every nonzero
radical ideal `J` contains a nonzero element `f` with `R / f R` reduced.

The proofs proceed by perturbing a first approximation `f` inside a high power of the maximal
ideal so as to maximize the number of minimal primes of `f R`, which is bounded uniformly by the
length estimates of `StacksFrontier.RingTheory.Ideal.PrincipalRadical.Length`, and then
correcting the perturbation to be a uniformizer at each of those primes.

## Main definitions

No new definitions are introduced. Normality is expressed by `IsDomain` together with
`IsIntegrallyClosed`, and reducedness of the quotient by `IsReduced (R ⧸ Ideal.span {f})`.

## Main results

* `exists_nonzero_mem_isReduced_quotient_of_height_one_primes`: in a two-dimensional Noetherian
  normal local domain, a finite family of height-one primes has a common nonzero element whose
  principal quotient is reduced.
* `exists_isReduced_quotient_and_dvd_pow`: in the same setting, every nonzero element of the
  maximal ideal divides a power of an element whose principal quotient is reduced.
* `exists_nonzero_mem_isReduced_quotient_of_isRadical`: in a catenary Noetherian normal local
  domain, every nonzero radical ideal contains a nonzero element whose principal quotient is
  reduced.

## Implementation notes

A pairwise distinct indexed family of primes is represented by a `Finset (Ideal R)`, which records
distinctness intrinsically. The second symbolic power of a height-one prime `p` is spelled as the
contraction along `algebraMap R (Localization.AtPrime p)` of the square of the maximal ideal of the
localization, which is a discrete valuation ring; "being a uniformizer at `p`" is then membership
in `p` together with non-membership in that contraction.

## References

* [Stacks, Tag 0AXH](https://stacks.math.columbia.edu/tag/0AXH)
* [Stacks, Tag 0AXI](https://stacks.math.columbia.edu/tag/0AXI)
* [Stacks, Tag 0BWZ](https://stacks.math.columbia.edu/tag/0BWZ)
-/

@[expose] public section

open IsLocalRing

section HeightOneLocalizations

/-- A height-one prime of a domain covers the zero prime. -/
private theorem covBy_bot_of_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    (⊥ : PrimeSpectrum R) ⋖ (⟨p, inferInstance⟩ : PrimeSpectrum R) := by
  have hpne : p ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hp
  have hb : (⊥ : PrimeSpectrum R) < (⟨p, inferInstance⟩ : PrimeSpectrum R) :=
    bot_lt_iff_ne_bot.mpr fun h => hpne (congrArg PrimeSpectrum.asIdeal h)
  refine ⟨hb, ?_⟩
  intro q hq hqp
  have hqne : q.asIdeal ≠ ⊥ := fun hz => ne_of_gt hq (PrimeSpectrum.ext hz)
  have hqpos : (1 : ℕ∞) ≤ q.asIdeal.height :=
    Order.one_le_iff_ne_zero.mpr fun hz => hqne (Ideal.height_eq_zero_iff_eq_bot.mp hz)
  have : q.asIdeal.IsPrime := q.isPrime
  have hstep : q.asIdeal.height + 1 ≤ p.height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hqp
  rw [hp] at hstep
  have : (2 : ℕ∞) ≤ 1 := by
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ q.asIdeal.height + 1 := by simpa [add_comm] using add_le_add_right hqpos 1
      _ ≤ 1 := hstep
  norm_num at this

/-- In a domain, a height-one prime containing a nonzero element is minimal over its
principal ideal. -/
private theorem mem_minimalPrimes_span_singleton_of_height_one
    {R : Type*} [CommRing R] [IsDomain R]
    {f : R} (hf : f ≠ 0) {p : Ideal R} [p.IsPrime]
    (hp : p.height = 1) (hfp : f ∈ p) :
    p ∈ (Ideal.span {f}).minimalPrimes := by
  refine ⟨⟨inferInstance, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfp)⟩, ?_⟩
  intro q hq hqp
  have : q.IsPrime := hq.1
  have hqne : q ≠ ⊥ := by
    intro hz
    have : f ∈ (⊥ : Ideal R) := hz ▸ hq.2 (Ideal.mem_span_singleton_self f)
    exact hf (by simpa using this)
  have hc := covBy_bot_of_height_eq_one p hp
  have hqspec : (⟨q, inferInstance⟩ : PrimeSpectrum R) ≤
      (⟨p, inferInstance⟩ : PrimeSpectrum R) := hqp
  rcases hc.eq_or_eq bot_le hqspec with hb | he
  · exact False.elim (hqne (congrArg PrimeSpectrum.asIdeal hb))
  · exact (congrArg PrimeSpectrum.asIdeal he).ge

/-- The minimal primes over a nonzero principal ideal in a Noetherian domain have height one. -/
@[ega "IV 5.2.5" "more general"]
private theorem height_eq_one_of_mem_minimalPrimes_span_singleton
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {f : R} (hf : f ≠ 0) {p : Ideal R}
    (hp : p ∈ (Ideal.span {f}).minimalPrimes) : p.height = 1 := by
  have : p.IsPrime := hp.isPrime
  have hne : p ≠ ⊥ := by
    intro he
    have : f ∈ (⊥ : Ideal R) := he ▸ hp.le (Ideal.mem_span_singleton_self f)
    exact hf (by simpa using this)
  have hlow : (1 : ℕ∞) ≤ p.height :=
    Order.one_le_iff_ne_zero.mpr fun hz => hne (Ideal.height_eq_zero_iff_eq_bot.mp hz)
  have hupp : p.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) p hp
  exact le_antisymm hupp hlow

/-- A one-dimensional Noetherian normal local domain is a discrete valuation ring. -/
private theorem isDiscreteValuationRing_of_ringKrullDim_eq_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hnf : ¬ IsField R := fun h =>
    one_ne_zero (hdim.symm.trans (ringKrullDim_eq_zero_of_isField h))
  have : Ring.DimensionLEOne R := ⟨by
    intro p hp0 hp
    exact (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
      (Ring.krullDimLE_iff.mpr hdim.le)) p hp0 hp⟩
  have : IsDedekindDomain R :=
    (isDedekindDomain_iff R (FractionRing R)).mpr
      ⟨inferInstance, inferInstance, inferInstance,
        (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance⟩
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 3 1).mp (inferInstance : IsDedekindDomain R)

/-- The localization of a Noetherian normal domain at a height-one prime is a discrete
valuation ring. -/
private theorem isDiscreteValuationRing_at_height_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (p : Ideal R) [p.IsPrime]
    (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  refine isDiscreteValuationRing_of_ringKrullDim_eq_one ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
  exact_mod_cast hp

end HeightOneLocalizations

section ReducedPrincipalQuotientDimensionTwo

private theorem exists_nonzero_mem_finset_ideals
    {R : Type*} [CommRing R] [IsDomain R] (s : Finset (Ideal R))
    (hs : ∀ I ∈ s, I ≠ ⊥) :
    ∃ x : R, x ≠ 0 ∧ ∀ I ∈ s, x ∈ I := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact ⟨1, one_ne_zero, by simp⟩
  | @insert I s hIs ih =>
      obtain ⟨a, hamem, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (hs I (Finset.mem_insert_self I s))
      obtain ⟨b, hb, hbmem⟩ := ih fun J hJ => hs J (Finset.mem_insert_of_mem hJ)
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      intro J hJ
      rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact J.mul_mem_right b hamem
      · exact J.mul_mem_left a (hbmem J hJ)

/-- In a domain, a prime is minimal over a nonzero principal ideal exactly when it contains the
generator and has height one. -/
@[ega "0 16.3.1" "special case", ega "IV 5.2.5" "more general"]
private theorem mem_minimalPrimes_span_iff_height_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {f : R} (hf : f ≠ 0) {p : Ideal R} (hp : p.IsPrime) :
    p ∈ (Ideal.span {f}).minimalPrimes ↔ f ∈ p ∧ p.height = 1 := by
  have : p.IsPrime := hp
  constructor
  · intro h
    exact ⟨h.1.2 (Ideal.subset_span (Set.mem_singleton f)),
      height_eq_one_of_mem_minimalPrimes_span_singleton hf h⟩
  · rintro ⟨hfp, hheight⟩
    exact mem_minimalPrimes_span_singleton_of_height_one hf hheight hfp

/-- An element in the maximal ideal but not its square is irreducible. -/
private theorem irreducible_of_mem_maximalIdeal_not_mem_sq
    {A : Type*} [CommRing A] [IsLocalRing A] {a : A}
    (ha : a ∈ IsLocalRing.maximalIdeal A)
    (ha2 : a ∉ IsLocalRing.maximalIdeal A ^ 2) : Irreducible a := by
  refine ⟨fun hunit => IsLocalRing.notMem_maximalIdeal.mpr hunit ha, fun b c hbc => ?_⟩
  by_contra h
  push Not at h
  have hb : b ∈ IsLocalRing.maximalIdeal A := by
    by_contra hbm
    exact h.1 (IsLocalRing.notMem_maximalIdeal.mp hbm)
  have hc : c ∈ IsLocalRing.maximalIdeal A := by
    by_contra hcm
    exact h.2 (IsLocalRing.notMem_maximalIdeal.mp hcm)
  apply ha2
  rw [pow_two]
  exact hbc ▸ Ideal.mul_mem_mul hb hc

/-- A height-one prime is not contained in its second symbolic power. -/
private theorem not_le_symbolic_sq_at_height_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [IsIntegrallyClosed R] {p : Ideal R} (hp : p.IsPrime) (hheight : p.height = 1) :
    ¬ p ≤ (p.map (algebraMap R (Localization.AtPrime p)) ^ 2).comap
      (algebraMap R (Localization.AtPrime p)) := by
  have : p.IsPrime := hp
  have : IsDiscreteValuationRing (Localization.AtPrime p) :=
    isDiscreteValuationRing_at_height_one p hheight
  let A := Localization.AtPrime p
  have hmap : p.map (algebraMap R A) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (IsLocalization.AtPrime.isMaximal_map p A)
  have hlt : IsLocalRing.maximalIdeal A ^ 2 < IsLocalRing.maximalIdeal A :=
    Ideal.pow_lt_self (IsLocalRing.maximalIdeal A)
      (IsDiscreteValuationRing.not_a_field' (R := A))
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      2 (by omega)
  intro hle
  have hmaple : p.map (algebraMap R A) ≤ p.map (algebraMap R A) ^ 2 :=
    (Ideal.map_le_iff_le_comap).mpr hle
  rw [hmap] at hmaple
  exact (not_le_of_gt hlt) hmaple

/-- Comparable height-one prime ideals in a Noetherian ring are equal. -/
private theorem eq_of_le_height_one_primes
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {p q : Ideal R} (hp : p.IsPrime) (_hq : q.IsPrime)
    (hpheight : p.height = 1) (hqheight : q.height = 1)
    (hpq : p ≤ q) : p = q := by
  have : p.IsPrime := hp
  exact Ideal.eq_of_le_of_height_le p hpq (by rw [hpheight, hqheight])

/-- A height-one prime has a local uniformizer avoiding a finite set of other height-one
primes. The second symbolic power is described by localization. -/
private theorem exists_mem_not_mem_symbolic_sq_and_other_primes
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [IsIntegrallyClosed R] (s : Finset (Ideal R))
    (hs : ∀ q ∈ s, q.IsPrime ∧ q.height = 1)
    {p : Ideal R} [p.IsPrime] (hp : p ∈ s) :
    ∃ a : R, a ∈ p ∧
      a ∉ (p.map (algebraMap R (Localization.AtPrime p)) ^ 2).comap
        (algebraMap R (Localization.AtPrime p)) ∧
      ∀ q ∈ s, q ≠ p → a ∉ q := by
  classical
  let T : Ideal R := (p.map (algebraMap R (Localization.AtPrime p)) ^ 2).comap
    (algebraMap R (Localization.AtPrime p))
  have hpnT : ¬ p ≤ T := not_le_symbolic_sq_at_height_one (hs p hp).1 (hs p hp).2
  have hsprime : ∀ q ∈ s.erase p, q.IsPrime := fun q hq => (hs q (Finset.mem_of_mem_erase hq)).1
  have hnotcover : ¬ (p : Set R) ⊆
      (T : Set R) ∪ (T : Set R) ∪ ⋃ q ∈ (↑(s.erase p) : Set (Ideal R)), (q : Set R) := by
    intro hcover
    rcases (Ideal.subset_union_prime' (s := s.erase p) (f := id)
      (a := T) (b := T) hsprime).mp hcover with hle | hle | ⟨q, hq, hpq⟩
    · exact hpnT hle
    · exact hpnT hle
    · have hqs : q ∈ s := Finset.mem_of_mem_erase hq
      have hpeq : p = q := eq_of_le_height_one_primes
        (hs p hp).1 (hs q hqs).1 (hs p hp).2 (hs q hqs).2 hpq
      exact (Finset.ne_of_mem_erase hq) hpeq.symm
  obtain ⟨a, ha, havoid⟩ := Set.not_subset.mp hnotcover
  exact ⟨a, ha, fun haT => havoid (Or.inl (Or.inl haT)), fun q hq hqp haq =>
    havoid (Or.inr (Set.mem_iUnion₂.mpr ⟨q, Finset.mem_erase.mpr ⟨hqp, hq⟩, haq⟩))⟩

/-- A quotient by an ideal of definition of a Noetherian local ring has finite length. -/
private theorem length_quotient_ne_top_of_radical_eq_maximalIdeal
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I.radical = IsLocalRing.maximalIdeal R) :
    Module.length R (R ⧸ I) ≠ ⊤ := by
  have hsupport : Module.support R (R ⧸ I) = {IsLocalRing.closedPoint R} := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    ext q
    constructor
    · intro hq
      have hmle : IsLocalRing.maximalIdeal R ≤ q.asIdeal := by
        rw [← hI]
        exact q.isPrime.radical_le_iff.mpr (SetLike.coe_subset_coe.mp hq)
      have heq : IsLocalRing.maximalIdeal R = q.asIdeal :=
        (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le q.isPrime.ne_top hmle
      exact (PrimeSpectrum.ext heq.symm : q = IsLocalRing.closedPoint R)
    · intro hq
      have heq : q = IsLocalRing.closedPoint R := by simpa using hq
      subst q
      exact SetLike.coe_subset_coe.mpr
        (le_trans Ideal.le_radical (le_of_eq hI))
  exact Module.length_ne_top_iff.mpr (isFiniteLength_of_support hsupport)

/-- An element of `WithBot ℕ∞` whose successor is a natural number `d` equals `d - 1`. -/
private theorem eq_natCast_sub_one_of_add_one_eq {x : WithBot ℕ∞} {d : ℕ}
    (hsum : x + 1 = d) : x = (d - 1 : ℕ) := by
  have hnotbot : x ≠ ⊥ := by
    intro hb
    rw [hb] at hsum
    simp at hsum
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hnotbot
  have heq : e + 1 = (d : ℕ∞) := WithBot.coe_injective (by
    simpa [← he] using hsum)
  have hfinite : e < ⊤ := (ENat.add_lt_top.mp (by rw [heq]; simp)).1
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite.ne
  have hnat : n + 1 = d := by
    exact_mod_cast (by simpa [← hn] using heq : (n : ℕ∞) + 1 = d)
  have hnd : n = d - 1 := by omega
  simpa [← he, ← hn] using congrArg (fun k : ℕ => (k : WithBot ℕ∞)) hnd

/-- A nonzero nonunit parameter in a finite-dimensional Noetherian local domain lowers Krull
dimension by one. -/
private theorem ringKrullDim_quotient_span_singleton_eq_sub_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    {d : ℕ} (hdim : ringKrullDim R = d) {f : R}
    (hf : f ≠ 0) (hfm : f ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ Ideal.span {f}) = (d - 1 : ℕ) := by
  have hsum :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (show f ∈ nonZeroDivisors R by simpa using hf) hfm
  rw [hdim] at hsum
  exact eq_natCast_sub_one_of_add_one_eq hsum

/-- In a local ring that is not of dimension one, a height-one prime is not maximal. -/
private theorem ne_maximalIdeal_of_height_eq_one
    {R : Type*} [CommRing R] [IsLocalRing R] (hne : ringKrullDim R ≠ 1)
    {p : Ideal R} (hp : p.height = 1) : p ≠ maximalIdeal R := by
  rintro rfl
  have h := maximalIdeal_height_eq_ringKrullDim (R := R)
  rw [hp] at h
  exact hne (by simpa using h.symm)

/-- The second member of a two-element system of parameters avoids every height-one prime
containing the first. -/
private theorem not_mem_height_one_prime_of_isSystemOfParameters_pair
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 2) {f g : R}
    (hsop : IsLocalRing.IsSystemOfParameters [f, g])
    {p : Ideal R} (hp : p.IsPrime) (hheight : p.height = 1)
    (hfp : f ∈ p) : g ∉ p := by
  intro hgp
  have hIle : Ideal.ofList [f, g] ≤ p := by
    rw [Ideal.ofList, Ideal.span_le]
    intro x hx
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hfp
    · exact hgp
  have hmle : IsLocalRing.maximalIdeal R ≤ p := by
    rw [← hsop.1]
    exact hp.radical_le_iff.mpr hIle
  exact ne_maximalIdeal_of_height_eq_one (by rw [hdim]; norm_num) hheight
    ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hp.ne_top hmle).symm

/-- Minimal primes of a quotient correspond bijectively to minimal primes over its defining
ideal. -/
private theorem natCard_minimalPrimes_quotient_eq
    {R : Type*} [CommRing R] (I : Ideal R) :
    Nat.card (minimalPrimes (R ⧸ I)) = Nat.card I.minimalPrimes := by
  rw [Ideal.minimalPrimes_eq_comap]
  exact (Nat.card_image_of_injective
    (Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective) _).symm

/-- The ideal generated by the first element of a list is contained in the ideal of the list. -/
private theorem span_singleton_le_ofList_cons {R : Type*} [CommRing R] (f : R) (gs : List R) :
    Ideal.span {f} ≤ Ideal.ofList (f :: gs) := by
  rw [Ideal.ofList_cons]
  exact le_sup_left

/-- Mapping to the quotient by the first element of a list kills it from the list. -/
private theorem map_mk_ofList_cons {R : Type*} [CommRing R] (f : R) (gs : List R) :
    Ideal.map (Ideal.Quotient.mk (Ideal.span {f})) (Ideal.ofList (f :: gs)) =
      Ideal.ofList (gs.map (Ideal.Quotient.mk (Ideal.span {f}))) := by
  rw [Ideal.map_ofList]
  simp [Ideal.ofList_cons]

/-- Quotienting by a parameter list after its first element preserves the module length of
the final quotient. -/
private theorem length_quotient_ofList_cons_eq_length_quotient_map
    {R : Type*} [CommRing R] (f : R) (gs : List R) :
    Module.length R (R ⧸ Ideal.ofList (f :: gs)) =
      Module.length (R ⧸ Ideal.span {f})
        ((R ⧸ Ideal.span {f}) ⧸
          Ideal.ofList (gs.map (Ideal.Quotient.mk (Ideal.span {f})))) := by
  have hlin : Module.length R ((R ⧸ Ideal.span {f}) ⧸
      Ideal.map (Ideal.Quotient.mk (Ideal.span {f})) (Ideal.ofList (f :: gs))) =
      Module.length R (R ⧸ Ideal.ofList (f :: gs)) :=
    (DoubleQuot.quotQuotEquivQuotOfLEₐ R
      (span_singleton_le_ofList_cons f gs)).toLinearEquiv.length_eq
  rw [← hlin, map_mk_ofList_cons]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

/-- The number of height-one components of a principal divisor is at most the length of a
two-parameter quotient. -/
private theorem natCard_minimalPrimes_span_le_length_pair
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hdim : ringKrullDim R = 2) {f g : R} (hf : f ≠ 0)
    (hfm : f ∈ IsLocalRing.maximalIdeal R)
    (hgm : g ∈ IsLocalRing.maximalIdeal R)
    (hsop : IsLocalRing.IsSystemOfParameters [f, g]) :
    (Nat.card (Ideal.span {f}).minimalPrimes : ℕ∞) ≤
      Module.length R (R ⧸ Ideal.ofList [f, g]) := by
  let I : Ideal R := Ideal.span {f}
  have hIle : I ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfm)
  have hIne : I ≠ ⊤ := fun htop =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top (eq_top_iff.mpr (htop ▸ hIle))
  let T := R ⧸ I
  have : Nontrivial T := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing T :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hdimT : ringKrullDim T = 1 := by
    simpa using
      ringKrullDim_quotient_span_singleton_eq_sub_one (d := 2) (by simpa using hdim) hf hfm
  have hgT : (Ideal.Quotient.mk I) g ∈ IsLocalRing.maximalIdeal T := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem _ hgm
  have hgmin : ∀ q ∈ minimalPrimes T, (Ideal.Quotient.mk I) g ∉ q := by
    intro q hq hqg
    let Q : Ideal R := q.comap (Ideal.Quotient.mk I)
    have hQmin : Q ∈ I.minimalPrimes := by
      simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using
        (Ideal.minimalPrimes_comap_of_surjective Ideal.Quotient.mk_surjective hq)
    have hQprime : Q.IsPrime := hQmin.1.1
    have hQheight : Q.height = 1 :=
      height_eq_one_of_mem_minimalPrimes_span_singleton hf hQmin
    have hfQ : f ∈ Q := hQmin.1.2 (Ideal.subset_span (Set.mem_singleton f))
    exact (not_mem_height_one_prime_of_isSystemOfParameters_pair hdim hsop
      hQprime hQheight hfQ) hqg
  have hbound := (natCard_minimalPrimes_le_length_quotient_span_singleton
    hdimT hgT hgmin).2
  have hlen := length_quotient_ofList_cons_eq_length_quotient_map f [g]
  rw [List.map_singleton, Ideal.ofList_singleton] at hlen
  rwa [natCard_minimalPrimes_quotient_eq I, ← hlen] at hbound

/-- A principal ideal in a Noetherian normal domain is radical if its localization at every
height-one prime is radical. -/
private theorem span_singleton_isRadical_of_height_one_localizations
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] {f : R} (hf : f ≠ 0)
    (hlocal : ∀ p : Ideal R, ∀ [p.IsPrime], p.height = 1 → f ∈ p →
      (Ideal.map (algebraMap R (Localization.AtPrime p)) (Ideal.span {f})).IsRadical) :
    (Ideal.span {f}).IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
  by_contra hnot
  have hxq : Ideal.Quotient.mk (Ideal.span {f}) x ≠ 0 := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hnot
  obtain ⟨p, hp, hcolon⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hxq
  have : p.IsPrime := hp.isPrime
  have hpheight : p.height = 1 :=
    (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot
      (FractionRing R)).1 f hf p hp |>.2
  have hfp : f ∈ p := (show Ideal.span {f} ≤ p by
    simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient]
      using hp.annihilator_le) (Ideal.mem_span_singleton_self f)
  let S := Localization.AtPrime p
  let q : R →+* S := algebraMap R S
  have hpow : (q x) ^ n ∈ Ideal.map q (Ideal.span {f}) := by
    rw [← map_pow]
    exact Ideal.mem_map_of_mem q hn
  have hxloc : q x ∈ Ideal.map q (Ideal.span {f}) :=
    hlocal p hpheight hfp (Ideal.mem_radical_iff.mpr ⟨n, hpow⟩)
  obtain ⟨s, hs, hxs⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S
      (Ideal.span {f}) x).mp hxloc
  have hzero : s • (Ideal.Quotient.mk (Ideal.span {f}) x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hxs
  exact hs (hcolon (by
    rw [Submodule.mem_colon_singleton]
    simpa only [Submodule.mem_bot] using hzero))

/-- Over a local ring that is a discrete valuation ring, a nonunit generator outside the square of
the maximal ideal has radical principal ideal. -/
private theorem isRadical_map_span_singleton_of_mem_not_mem_sq
    {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime p)] {f : R}
    (hfm : algebraMap R (Localization.AtPrime p) f ∈ maximalIdeal (Localization.AtPrime p))
    (hf2 : algebraMap R (Localization.AtPrime p) f ∉
      maximalIdeal (Localization.AtPrime p) ^ 2) :
    (Ideal.map (algebraMap R (Localization.AtPrime p)) (Ideal.span {f})).IsRadical := by
  rw [Ideal.map_span, Set.image_singleton,
    (irreducible_of_mem_maximalIdeal_not_mem_sq hfm hf2).maximalIdeal_eq.symm]
  exact (maximalIdeal.isMaximal _).isPrime.isRadical

/-- A principal ideal in a Noetherian normal domain is radical if its generator is a
uniformizer at every height-one prime containing it. -/
private theorem isRadical_span_of_not_mem_symbolic_sq
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [IsIntegrallyClosed R] {f : R} (hf : f ≠ 0)
    (hlocal : ∀ (p : Ideal R) (_hp : p.IsPrime), p.height = 1 → f ∈ p →
      algebraMap R (Localization.AtPrime p) f ∉
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ 2) :
    (Ideal.span {f}).IsRadical := by
  refine span_singleton_isRadical_of_height_one_localizations hf fun p hp hheight hfp => ?_
  have : IsDiscreteValuationRing (Localization.AtPrime p) :=
    isDiscreteValuationRing_at_height_one p hheight
  exact isRadical_map_span_singleton_of_mem_not_mem_sq p
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ p f).mpr hfp) (hlocal p hp hheight hfp)

/-- Finite prime avoidance supplies an element of any power of the maximal ideal that
is a unit at each of finitely many nonmaximal primes. -/
private theorem exists_mem_pow_notMem_finite_primes
    {R : Type*} [CommRing R] [IsLocalRing R]
    (S : Set (Ideal R)) (hS : S.Finite) (hprime : ∀ p ∈ S, p.IsPrime)
    (hne : ∀ p ∈ S, p ≠ maximalIdeal R) (N : ℕ) :
    ∃ y ∈ maximalIdeal R ^ N, ∀ p ∈ S, y ∉ p := by
  have hnot : ¬ (maximalIdeal R : Set R) ⊆ ⋃ p ∈ S, (p : Set R) := by
    intro hsub
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime_finite hS ⊥ ⊥
      (by intro p hp _ _; exact hprime p hp)).mp hsub
    exact hne p hp ((maximalIdeal.isMaximal R).eq_of_le (hprime p hp).ne_top hmp).symm
  obtain ⟨y, hym, hy⟩ := Set.not_subset.mp hnot
  refine ⟨y ^ N, Ideal.pow_mem_pow hym N, fun p hp hyp => hy (Set.mem_iUnion.mpr
    ⟨p, Set.mem_iUnion.mpr ⟨hp, (hprime p hp).isRadical (Ideal.mem_radical_iff.mpr ⟨N, hyp⟩)⟩⟩)⟩

/-- Prime avoidance permits a perturbation in any power of the maximal ideal which makes
all prescribed local multiplicities equal to one. -/
private theorem exists_perturbation_not_mem_symbolic_sq
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hdim : ringKrullDim R = 2) (s : Finset (Ideal R))
    (hs : ∀ p ∈ s, p.IsPrime ∧ p.height = 1) (f : R)
    (N : ℕ) :
    ∃ h ∈ IsLocalRing.maximalIdeal R ^ N, (∀ p ∈ s, h ∈ p) ∧
      ∀ (p : Ideal R) (_hp : p.IsPrime), p ∈ s →
        algebraMap R (Localization.AtPrime p) (f + h) ∉
          IsLocalRing.maximalIdeal (Localization.AtPrime p) ^ 2 := by
  classical
  let : ∀ p : s, p.val.IsPrime := fun p => (hs p p.property).1
  let T (p : s) : Ideal R :=
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.val) ^ 2).comap
      (algebraMap R (Localization.AtPrime p.val))
  have hex (p : s) : ∃ a : R, a ∈ p.val ∧ a ∉ T p ∧
      ∀ q ∈ s, q ≠ p.val → a ∉ q := by
    have hmap : p.val.map (algebraMap R (Localization.AtPrime p.val)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p.val) :=
      IsLocalRing.eq_maximalIdeal
        (IsLocalization.AtPrime.isMaximal_map p.val (Localization.AtPrime p.val))
    simpa only [hmap] using
      exists_mem_not_mem_symbolic_sq_and_other_primes s hs p.property
  choose a ha using hex
  let c (p : s) : R := if f ∈ T p then a p else (a p) ^ 2
  obtain ⟨b, hbm, hb⟩ := exists_mem_pow_notMem_finite_primes (↑s) s.finite_toSet
    (fun p hp => (hs p hp).1)
    (fun p hp => ne_maximalIdeal_of_height_eq_one (by rw [hdim]; norm_num) (hs p hp).2) N
  let h := b * ∏ p : s, c p
  have hc (p : s) : c p ∈ p.val := by
    dsimp only [c]
    split_ifs
    · exact (ha p).1
    · exact p.val.pow_mem_of_mem (ha p).1 2 (by decide)
  have hcnot (p q : s) (hpq : p ≠ q) : c q ∉ p.val := by
    have hnot : a q ∉ p.val := (ha q).2.2 p.val p.property
      (fun heq => hpq (Subtype.ext heq))
    dsimp only [c]
    split_ifs
    · exact hnot
    · exact fun hpow => hnot ((hs p p.property).1.mem_of_pow_mem 2 hpow)
  have hprod (p : s) : h =
      (b * ∏ q ∈ Finset.univ.erase p, c q) * c p := by
    rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ p)]
  have hmem : ∀ p ∈ s, h ∈ p := by
    intro p hp
    rw [hprod ⟨p, hp⟩]
    exact p.mul_mem_left _ (hc ⟨p, hp⟩)
  refine ⟨h, (IsLocalRing.maximalIdeal R ^ N).mul_mem_right _ hbm, hmem, ?_⟩
  intro p hp hps
  let q : s := ⟨p, hps⟩
  let A := Localization.AtPrime p
  let φ := algebraMap R A
  let u := φ (b * ∏ t ∈ Finset.univ.erase q, c t)
  have hu : IsUnit u := by
    dsimp only [u]
    rw [map_mul, map_prod]
    apply IsUnit.mul
    · exact (IsLocalization.AtPrime.isUnit_to_map_iff A p b).mpr (hb p hps)
    · apply IsUnit.prod_iff.mpr
      intro t ht
      apply (IsLocalization.AtPrime.isUnit_to_map_iff A p (c t)).mpr
      exact hcnot q t (Finset.ne_of_mem_erase ht).symm
  have hh : φ h = u * φ (c q) := by
    rw [hprod q, map_mul]
  show φ (f + h) ∉ IsLocalRing.maximalIdeal A ^ 2
  rw [map_add, hh]
  by_cases hft : f ∈ T q
  · have hfn : φ f ∈ IsLocalRing.maximalIdeal A ^ 2 := hft
    have hcq : c q = a q := ite_eq_left hft
    rw [hcq]
    intro hsum
    have hprodmem := (IsLocalRing.maximalIdeal A ^ 2).sub_mem hsum hfn
    rw [add_sub_cancel_left] at hprodmem
    exact (ha q).2.1 ((Ideal.unit_mul_mem_iff_mem _ hu).mp hprodmem)
  · have hfn : φ f ∉ IsLocalRing.maximalIdeal A ^ 2 := hft
    have hcq : c q = (a q) ^ 2 := ite_eq_right hft
    rw [hcq, map_pow]
    have ham : φ (a q) ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff A p (a q)).mpr (ha q).1
    have hprodmem : u * φ (a q) ^ 2 ∈ IsLocalRing.maximalIdeal A ^ 2 :=
      (IsLocalRing.maximalIdeal A ^ 2).mul_mem_left u (Ideal.pow_mem_pow ham 2)
    intro hsum
    exact hfn (by simpa only [add_sub_cancel_right] using
      (IsLocalRing.maximalIdeal A ^ 2).sub_mem hsum hprodmem)

/-- Neither member of a two-element system of parameters in dimension two can vanish. -/
private theorem ne_zero_of_isSystemOfParameters_pair
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 2) {f g : R}
    (hsop : IsLocalRing.IsSystemOfParameters [f, g]) : f ≠ 0 := by
  intro hf
  have hrad : (Ideal.span {g}).radical = IsLocalRing.maximalIdeal R := by
    simpa [hf, Ideal.ofList_cons, Ideal.ofList_nil] using hsop.1
  have hmin : IsLocalRing.maximalIdeal R ∈ (Ideal.span {g}).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · exact Ideal.le_radical.trans hrad.le
    · intro p hp _
      rw [← hrad]
      exact hp.1.radical_le_iff.mpr hp.2
  have hheight := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
    (Ideal.span {g}) (IsLocalRing.maximalIdeal R) hmin
  have hdimle : ringKrullDim R ≤ 1 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact WithBot.coe_le_coe.mpr hheight
  rw [hdim] at hdimle
  norm_num at hdimle

/-- Every entry of a system of parameters belongs to the maximal ideal. -/
private theorem mem_maximalIdeal_of_mem_isSystemOfParameters
    {R : Type*} [CommRing R] [IsLocalRing R] {rs : List R}
    (hsop : IsLocalRing.IsSystemOfParameters rs) {x : R} (hx : x ∈ rs) :
    x ∈ IsLocalRing.maximalIdeal R := by
  rw [← hsop.1]
  exact Ideal.le_radical (Ideal.subset_span hx)

/-- **Stacks 0AXH.** In a two-dimensional Noetherian normal local domain, finitely many
height-one prime ideals contain a common nonzero element whose principal quotient is reduced. -/
@[stacks 0AXH]
theorem exists_nonzero_mem_isReduced_quotient_of_height_one_primes
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hdim : ringKrullDim R = 2) (primes : Finset (Ideal R))
    (hprimes : ∀ p ∈ primes, p.IsPrime ∧ p.height = 1) :
    ∃ f : R, f ≠ 0 ∧ (∀ p ∈ primes, f ∈ p) ∧ IsReduced (R ⧸ Ideal.span {f}) := by
  classical
  obtain hempty | hnonempty := primes.eq_empty_or_nonempty
  · subst primes
    refine ⟨1, one_ne_zero, by simp, ?_⟩
    rw [Ideal.span_singleton_eq_top.mpr isUnit_one]
    infer_instance
  obtain ⟨f, hf, hfprimes⟩ := exists_nonzero_mem_finset_ideals primes
    (fun p hp => Ideal.ne_bot_of_height_eq_one (hprimes p hp).2)
  have hfm : f ∈ IsLocalRing.maximalIdeal R := by
    obtain ⟨p, hp⟩ := hnonempty
    exact IsLocalRing.le_maximalIdeal (hprimes p hp).1.ne_top (hfprimes p hp)
  have hfmin : ∀ p ∈ minimalPrimes R, f ∉ p := by
    simpa [IsDomain.minimalPrimes_eq_singleton_bot] using hf
  obtain ⟨g, hgm, N, hsop, hstable⟩ :=
    exists_isSystemOfParameters_pair_add_of_avoids_minimalPrimes hdim f hfm hfmin
  let L := Module.length R (R ⧸ Ideal.ofList [f, g])
  have hL : L ≠ ⊤ := length_quotient_ne_top_of_radical_eq_maximalIdeal hsop.1
  have hnonzero (h : R) (hh : h ∈ IsLocalRing.maximalIdeal R ^ N) : f + h ≠ 0 :=
    ne_zero_of_isSystemOfParameters_pair hdim (hstable h hh).1
  have hbound (h : R) (hh : h ∈ IsLocalRing.maximalIdeal R ^ N) :
      Nat.card (Ideal.span {f + h}).minimalPrimes ≤ L.toNat := by
    have hsh := (hstable h hh).1
    have hb := natCard_minimalPrimes_span_le_length_pair hdim (hnonzero h hh)
      (mem_maximalIdeal_of_mem_isSystemOfParameters hsh (by simp)) hgm hsh
    rw [← (hstable h hh).2] at hb
    exact_mod_cast ENat.toNat_le_toNat hb hL
  let S : Set R := {h | h ∈ IsLocalRing.maximalIdeal R ^ N ∧ ∀ p ∈ primes, h ∈ p}
  let t (x : R) : ℕ := Nat.card (Ideal.span {x}).minimalPrimes
  have hbounded : BddAbove ((fun h => t (f + h)) '' S) :=
    ⟨L.toNat, fun _ ⟨h, hh, heq⟩ => heq ▸ hbound h hh.1⟩
  have hSne : S.Nonempty := ⟨0, Ideal.zero_mem _, fun p _ => Ideal.zero_mem p⟩
  obtain ⟨n, hn, hnmax⟩ := hbounded.exists_isGreatest_of_nonempty (hSne.image _)
  obtain ⟨h₀, hh₀, rfl⟩ := hn
  let f' := f + h₀
  have hf' : f' ≠ 0 := hnonzero h₀ hh₀.1
  have hf'primes : ∀ p ∈ primes, f' ∈ p :=
    fun p hp => p.add_mem (hfprimes p hp) (hh₀.2 p hp)
  let s := (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f'})).toFinset
  have hs (p : Ideal R) : p ∈ s ↔ p ∈ (Ideal.span {f'}).minimalPrimes :=
    Set.Finite.mem_toFinset _
  have hsprime : ∀ p ∈ s, p.IsPrime ∧ p.height = 1 := fun p hp =>
    ⟨((hs p).mp hp).1.1, height_eq_one_of_mem_minimalPrimes_span_singleton hf' ((hs p).mp hp)⟩
  have hf's : ∀ p ∈ s, f' ∈ p := fun p hp => ((hs p).mp hp).1.2 (Ideal.subset_span (by simp))
  have hprimes_s : ∀ p ∈ primes, p ∈ s := fun p hp =>
    (hs p).mpr ((mem_minimalPrimes_span_iff_height_one hf' (hprimes p hp).1).mpr
      ⟨hf'primes p hp, (hprimes p hp).2⟩)
  obtain ⟨h, hhm, hhs, hlocal⟩ :=
    exists_perturbation_not_mem_symbolic_sq hdim s hsprime f' N
  have hsumS : h₀ + h ∈ S :=
    ⟨(IsLocalRing.maximalIdeal R ^ N).add_mem hh₀.1 hhm,
      fun p hp => p.add_mem (hh₀.2 p hp) (hhs p (hprimes_s p hp))⟩
  have hnew : f' + h ≠ 0 := by
    simpa only [f', add_assoc] using hnonzero (h₀ + h) hsumS.1
  have hcard : Nat.card (Ideal.span {f' + h}).minimalPrimes ≤
      Nat.card (Ideal.span {f'}).minimalPrimes :=
    hnmax ⟨h₀ + h, hsumS, by simp only [t, f', add_assoc]⟩
  have hsubset : (Ideal.span {f'}).minimalPrimes ⊆
      (Ideal.span {f' + h}).minimalPrimes := fun p hp =>
    (mem_minimalPrimes_span_iff_height_one hnew hp.1.1).mpr
      ⟨p.add_mem (hf's p ((hs p).mpr hp)) (hhs p ((hs p).mpr hp)),
        height_eq_one_of_mem_minimalPrimes_span_singleton hf' hp⟩
  have heq : (Ideal.span {f'}).minimalPrimes = (Ideal.span {f' + h}).minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R
      (Ideal.span {f' + h})).eq_of_subset_of_card_le hsubset hcard
  refine ⟨f' + h, hnew, fun p hp => p.add_mem (hf'primes p hp)
    (hhs p (hprimes_s p hp)), (Ideal.isRadical_iff_quotient_reduced _).mp ?_⟩
  apply isRadical_span_of_not_mem_symbolic_sq hnew
  intro p hp hheight hfp
  apply hlocal p hp
  apply (hs p).mpr
  rw [heq]
  exact (mem_minimalPrimes_span_iff_height_one hnew hp).mpr ⟨hfp, hheight⟩

/-- **Stacks 0AXI.** In a two-dimensional Noetherian normal local domain, every nonzero element of
the maximal ideal divides a power of an element whose principal quotient is reduced. -/
@[stacks 0AXI]
lemma exists_isReduced_quotient_and_dvd_pow
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hdim : ringKrullDim R = 2) {a : R}
    (_ha : a ∈ IsLocalRing.maximalIdeal R) (ha0 : a ≠ 0) :
    ∃ c : R, IsReduced (R ⧸ Ideal.span {c}) ∧ ∃ n : ℕ, a ∣ c ^ n := by
  let I : Ideal R := Ideal.span {a}
  let primes : Finset (Ideal R) := I.finite_minimalPrimes_of_isNoetherianRing.toFinset
  have hprimes : ∀ p ∈ primes, p.IsPrime ∧ p.height = 1 := by
    intro p hp
    have hp' : p ∈ I.minimalPrimes := by simpa [primes] using hp
    exact ⟨hp'.isPrime, height_eq_one_of_mem_minimalPrimes_span_singleton ha0 hp'⟩
  obtain ⟨c, _hc0, hc, hred⟩ :=
    exists_nonzero_mem_isReduced_quotient_of_height_one_primes hdim primes hprimes
  refine ⟨c, hred, ?_⟩
  have hcrad : c ∈ I.radical := by
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro p hp
    exact hc p (by simpa [primes] using hp)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hcrad
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

end ReducedPrincipalQuotientDimensionTwo

section ReducedPrincipalQuotientInRadicalIdeal

private lemma covToLT_last {α : Type*} [PartialOrder α]
    (s : RelSeries {(a, b) : α × α | a ⋖ b}) :
    (covToLT s).last = s.last := rfl

/-- A height-one prime in a catenary Noetherian local domain has codimension one in the
dimension of the quotient. -/
@[ega "0 16.1.4" "special case"]
private theorem ringKrullDim_quotient_height_one_add_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hcat : Ring.IsCatenary R) (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ringKrullDim (R ⧸ p) + 1 = ringKrullDim R := by
  let P : PrimeSpectrum R := ⟨p, inferInstance⟩
  have hcov : (⊥ : PrimeSpectrum R) ⋖ P := covBy_bot_of_height_eq_one p hp
  have hstep := coheight_covby_of_catenary
    (_root_.isCatenaryRingSaturated_of_isCatenary hcat) (⊥ : PrimeSpectrum R) P hcov
  have hcast := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hstep
  rw [WithBot.coe_add, Order.coheight_bot_eq_krullDim,
    coheight_eq_ringKrullDim_quotient (R := R) P] at hcast
  simpa [P, ringKrullDim] using hcast.symm

private theorem ringKrullDim_quotient_height_one_eq_sub_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hcat : Ring.IsCatenary R) {d : ℕ} (hdim : ringKrullDim R = d)
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ringKrullDim (R ⧸ p) = (d - 1 : ℕ) := by
  have hsum := ringKrullDim_quotient_height_one_add_one hcat p hp
  rw [hdim] at hsum
  exact eq_natCast_sub_one_of_add_one_eq hsum

/-- The tail of a system of parameters remains a system of parameters after quotienting by its
first element, when the quotient has the expected dimension. -/
private theorem isSystemOfParameters_map_quotient_tail
    {R : Type*} [CommRing R] [IsLocalRing R]
    {f : R} [IsLocalRing (R ⧸ Ideal.span {f})]
    (gs : List R)
    (hgs : IsLocalRing.IsSystemOfParameters (f :: gs))
    (hdim : ringKrullDim (R ⧸ Ideal.span {f}) = gs.length) :
    IsLocalRing.IsSystemOfParameters
      (gs.map (Ideal.Quotient.mk (Ideal.span {f}))) := by
  let I : Ideal R := Ideal.span {f}
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hker : RingHom.ker q ≤ Ideal.ofList (f :: gs) := by
    rw [Ideal.mk_ker]
    exact span_singleton_le_ofList_cons f gs
  constructor
  · rw [← map_mk_ofList_cons,
      ← Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective hker, hgs.1]
    exact IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
  · simpa [q, I] using hdim

/-- An ideal in a finite antichain of prime ideals has an element that avoids every other
ideal in the antichain. -/
private theorem exists_mem_notMem_other_of_finite_prime_antichain
    {R : Type*} [CommRing R] (S : Set (Ideal R)) (hS : S.Finite)
    (hprime : ∀ p ∈ S, p.IsPrime)
    (hanti : ∀ p ∈ S, ∀ q ∈ S, p ≤ q → p = q)
    (p : Ideal R) (hp : p ∈ S) :
    ∃ a : R, a ∈ p ∧ ∀ q ∈ S, q ≠ p → a ∉ q := by
  let T : Set (Ideal R) := S \ {p}
  have hT : T.Finite := hS.subset (Set.sdiff_subset)
  have hnsub : ¬ (p : Set R) ⊆ ⋃ q ∈ T, (q : Set R) := by
    intro hsub
    obtain ⟨q, hq, hpq⟩ :=
      (Ideal.subset_union_prime_finite hT ⊥ ⊥
        (by intro q hq _ _; exact hprime q hq.1)).mp hsub
    exact hq.2 (hanti p hp q hq.1 hpq).symm
  obtain ⟨a, ha, haout⟩ := Set.not_subset.mp hnsub
  exact ⟨a, ha, fun q hq hqp haq => haout (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr
    ⟨⟨hq, by simpa using hqp⟩, haq⟩⟩)⟩

/-- Every nonzero radical ideal of a discrete valuation ring contains its maximal ideal. -/
private theorem maximalIdeal_le_of_isRadical_of_ne_bot
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (I : Ideal R) (hI : I.IsRadical) (hI0 : I ≠ ⊥) : maximalIdeal R ≤ I := by
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, hx⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hpow : ϖ ^ n ∈ I := by
    have hm := I.mul_mem_left ((u⁻¹ : Rˣ) : R) (hx ▸ hxI)
    simpa only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] using hm
  rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
  exact hI (Ideal.mem_radical_iff.mpr ⟨n, hpow⟩)

private theorem exists_nonzero_mem_isReduced_quotient_of_isRadical_dvr
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (J : Ideal R) (hJ : J.IsRadical) (hJne : J ≠ ⊥) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ Ideal.span {f}) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmem : ϖ ∈ J := maximalIdeal_le_of_isRadical_of_ne_bot J hJ hJne
    (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ)
  refine ⟨ϖ, hϖ.ne_zero, hmem, ?_⟩
  exact (Ideal.isRadical_iff_quotient_reduced _).mp
    (Ideal.IsPrime.isRadical ((Ideal.span_singleton_prime hϖ.prime.ne_zero).mpr hϖ.prime))

private theorem exists_nonzero_mem_isReduced_quotient_of_top
    {R : Type*} [CommRing R] [Nontrivial R] (J : Ideal R) (hJ : J = ⊤) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ Ideal.span {f}) := by
  refine ⟨1, one_ne_zero, by simp [hJ], ?_⟩
  rw [Ideal.span_singleton_eq_top.mpr isUnit_one]
  infer_instance

private theorem exists_nonzero_mem_isReduced_quotient_of_isRadical_dim_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hdim : ringKrullDim R = 1)
    (J : Ideal R) (hJ : J.IsRadical) (hJne : J ≠ ⊥) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ Ideal.span {f}) := by
  have := isDiscreteValuationRing_of_ringKrullDim_eq_one hdim
  exact exists_nonzero_mem_isReduced_quotient_of_isRadical_dvr J hJ hJne

/-- A bounded natural-valued function on a nonempty set attains its maximum. -/
private theorem exists_max_nat_of_bounded_on
    {α : Type*} (s : Set α) (hs : s.Nonempty) (t : α → ℕ) (B : ℕ)
    (hB : ∀ x ∈ s, t x ≤ B) :
    ∃ x ∈ s, ∀ y ∈ s, t y ≤ t x := by
  have hfinite : (t '' s).Finite :=
    (Set.finite_le_nat B).subset (by
      rintro n ⟨x, hx, rfl⟩
      exact hB x hx)
  obtain ⟨x, hx⟩ := hfinite.exists_maximalFor' t s hs
  exact ⟨x, hx.prop, fun y hy => (le_total (t y) (t x)).elim id (hx.2 hy)⟩

/-- If a perturbation preserves every old minimal prime, has no more minimal primes, and is
locally radical at the old primes, then its principal ideal is radical. -/
private theorem span_singleton_isRadical_of_minimalPrimes_ncard_le
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] {f g : R} (hg : g ≠ 0)
    (hcontain : (Ideal.span {f}).minimalPrimes ⊆
      (Ideal.span {g}).minimalPrimes)
    (hcard : (Ideal.span {g}).minimalPrimes.ncard ≤
      (Ideal.span {f}).minimalPrimes.ncard)
    (hlocal : ∀ p ∈ (Ideal.span {f}).minimalPrimes, ∀ [p.IsPrime],
      (Ideal.map (algebraMap R (Localization.AtPrime p))
        (Ideal.span {g})).IsRadical) :
    (Ideal.span {g}).IsRadical := by
  have heq : (Ideal.span {f}).minimalPrimes =
      (Ideal.span {g}).minimalPrimes :=
    Set.eq_of_subset_of_ncard_le hcontain hcard
      (Ideal.finite_minimalPrimes_of_isNoetherianRing R _)
  apply span_singleton_isRadical_of_height_one_localizations hg
  intro p hp hheight hgp
  exact hlocal p (heq ▸ mem_minimalPrimes_span_singleton_of_height_one hg hheight hgp)

/-- Taking a quotient by an ideal containing `I` commutes with first quotienting by `I`. -/
private theorem ringKrullDim_quotient_map_eq
    {R : Type*} [CommRing R] {I p : Ideal R} (hIp : I ≤ p) :
    ringKrullDim ((R ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) p) =
      ringKrullDim (R ⧸ p) := by
  have hker : RingHom.ker (Ideal.Quotient.factor hIp) =
      Ideal.map (Ideal.Quotient.mk I) p := Ideal.Quotient.factor_ker hIp
  let e : ((R ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) p) ≃+* (R ⧸ p) :=
    (Ideal.quotientEquiv (RingHom.ker (Ideal.Quotient.factor hIp))
      (Ideal.map (Ideal.Quotient.mk I) p) (RingEquiv.refl (R ⧸ I))
      (by simp [hker])).symm.trans
        (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.factor_surjective hIp))
  exact ringKrullDim_eq_of_ringEquiv e

/-- Taking a quotient by an ideal containing `I` commutes with first quotienting by `I`. -/
private alias ringKrullDim_quotQuot_eq_of_le := ringKrullDim_quotient_map_eq

/-- Every minimal component of a nonzero principal quotient has full dimension in a catenary
Noetherian local domain. -/
private theorem ringKrullDim_quotient_minimalPrime_eq_of_catenary
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hcat : Ring.IsCatenary R) {d : ℕ} (hdim : ringKrullDim R = d)
    {f : R} (hf : f ≠ 0) (hfm : f ∈ maximalIdeal R)
    {q : Ideal (R ⧸ Ideal.span {f})}
    (hq : q ∈ minimalPrimes (R ⧸ Ideal.span {f})) :
    ringKrullDim ((R ⧸ Ideal.span {f}) ⧸ q) =
      ringKrullDim (R ⧸ Ideal.span {f}) := by
  let I : Ideal R := Ideal.span {f}
  let π : R →+* R ⧸ I := Ideal.Quotient.mk I
  let p : Ideal R := Ideal.comap π q
  have hpmin : p ∈ I.minimalPrimes := by
    have h := Ideal.minimalPrimes_comap_of_surjective (f := π) Ideal.Quotient.mk_surjective
      (show q ∈ (⊥ : Ideal (R ⧸ I)).minimalPrimes from hq)
    simpa only [p, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, I, π] using h
  have : p.IsPrime := hpmin.isPrime
  have hmap : Ideal.map π p = q :=
    Ideal.map_comap_of_surjective π Ideal.Quotient.mk_surjective q
  calc
    ringKrullDim ((R ⧸ Ideal.span {f}) ⧸ q) =
        ringKrullDim ((R ⧸ I) ⧸ Ideal.map π p) := by rw [hmap]
    _ = ringKrullDim (R ⧸ p) := ringKrullDim_quotQuot_eq_of_le hpmin.le
    _ = (d - 1 : ℕ) := ringKrullDim_quotient_height_one_eq_sub_one hcat hdim p
      (height_eq_one_of_mem_minimalPrimes_span_singleton hf hpmin)
    _ = ringKrullDim (R ⧸ Ideal.span {f}) :=
      (ringKrullDim_quotient_span_singleton_eq_sub_one hdim hf hfm).symm

/-- The number of height-one components of a nonzero principal divisor is bounded by the
length of any parameter quotient beginning with that element. -/
private theorem ncard_minimalPrimes_span_singleton_le_length_of_isSystemOfParameters
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hcat : Ring.IsCatenary R) {d : ℕ} (hdim : ringKrullDim R = d)
    {f : R} (hf : f ≠ 0) (hfm : f ∈ maximalIdeal R)
    (gs : List R) (hgs : IsSystemOfParameters (f :: gs))
    (hlen : gs.length = d - 1) :
    ((Ideal.span {f}).minimalPrimes.ncard : ℕ∞) ≤
      Module.length R (R ⧸ Ideal.ofList (f :: gs)) := by
  let I : Ideal R := Ideal.span {f}
  let S := R ⧸ I
  let π : R →+* S := Ideal.Quotient.mk I
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top <|
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfm)
  have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hItop
  have : IsLocalRing S := IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
  have hdimS : ringKrullDim S = gs.length := by
    simpa [S, I, hlen] using ringKrullDim_quotient_span_singleton_eq_sub_one hdim hf hfm
  have hgsS : IsSystemOfParameters (gs.map π) :=
    isSystemOfParameters_map_quotient_tail gs hgs hdimS
  have hfull (q : Ideal S) (hq : q ∈ minimalPrimes S) :
      ringKrullDim (S ⧸ q) = ringKrullDim S :=
    ringKrullDim_quotient_minimalPrime_eq_of_catenary hcat hdim hf hfm hq
  let e : {q : Ideal S // q ∈ minimalPrimes S ∧
      ringKrullDim (S ⧸ q) = ringKrullDim S} ≃
      {q : Ideal S // q ∈ minimalPrimes S} :=
    { toFun := fun q => ⟨q.1, q.2.1⟩
      invFun := fun q => ⟨q.1, q.2, hfull q.1 q.2⟩
      left_inv := fun q => Subtype.ext rfl
      right_inv := fun q => Subtype.ext rfl }
  calc
    ((Ideal.span {f}).minimalPrimes.ncard : ℕ∞) =
        (Nat.card (minimalPrimes S) : ℕ∞) := by
          rw [← Nat.card_coe_set_eq, natCard_minimalPrimes_quotient_eq]
    _ = (Nat.card {q : Ideal S // q ∈ minimalPrimes S ∧
          ringKrullDim (S ⧸ q) = ringKrullDim S} : ℕ∞) := by
          exact_mod_cast (Nat.card_congr e).symm
    _ ≤ Module.length S (S ⧸ Ideal.ofList (gs.map π)) :=
      (natCard_fullDimensionalMinimalPrimes_le_length_quotient_of_isSystemOfParameters hgsS).2
    _ = Module.length R (R ⧸ Ideal.ofList (f :: gs)) :=
      (length_quotient_ofList_cons_eq_length_quotient_map f gs).symm

/-- High-order perturbations of a nonzero parameter have a uniformly bounded number of
minimal prime divisors. -/
private theorem exists_uniform_bound_minimalPrimes_perturbation
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hcat : Ring.IsCatenary R) {d : ℕ} (hdim : ringKrullDim R = d)
    {f : R} (hf : f ≠ 0) (hfm : f ∈ maximalIdeal R) :
    ∃ N B : ℕ, 0 < N ∧ ∀ h ∈ maximalIdeal R ^ N,
      f + h ≠ 0 ∧ (Ideal.span {f + h}).minimalPrimes.ncard ≤ B := by
  have hfmin : ∀ p ∈ minimalPrimes R, f ∉ p := by
    simpa [IsDomain.minimalPrimes_eq_singleton_bot] using hf
  obtain ⟨gs, N₀, hlen, _, hgs, hstable⟩ :=
    exists_isSystemOfParameters_cons_stable_under_add_of_avoids_minimalPrimes
      d hdim f hfm hfmin
  have hnotall : ¬ ∀ n : ℕ, f ∈ maximalIdeal R ^ n := by
    intro hall
    have hi : f ∈ (⨅ n : ℕ, maximalIdeal R ^ n) :=
      (Submodule.mem_iInf (fun n : ℕ => maximalIdeal R ^ n)).mpr hall
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R)
      (maximalIdeal.isMaximal R).ne_top] at hi
    exact hf (by simpa using hi)
  push Not at hnotall
  obtain ⟨N₁, hN₁⟩ := hnotall
  have hfinite : Module.length R (R ⧸ Ideal.ofList (f :: gs)) < ⊤ := by
    have h := HilbertSamuel.length_quotient_lt_top (Ideal.ofList (f :: gs)) hgs.1 R 0
    have hs : Ideal.ofList (f :: gs) ^ (0 + 1) • (⊤ : Submodule R R) =
        Ideal.ofList (f :: gs) := by simp
    rwa [hs] at h
  obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.mp hfinite.ne
  refine ⟨N₀ + N₁ + 1, B, by omega, ?_⟩
  intro h hh
  have hh₀ : h ∈ maximalIdeal R ^ N₀ :=
    Ideal.pow_le_pow_right (by omega : N₀ ≤ N₀ + N₁ + 1) hh
  have hh₁ : h ∈ maximalIdeal R ^ N₁ :=
    Ideal.pow_le_pow_right (by omega : N₁ ≤ N₀ + N₁ + 1) hh
  have hhm : h ∈ maximalIdeal R := Ideal.pow_le_self (by omega : N₀ + N₁ + 1 ≠ 0) hh
  have hfadd : f + h ≠ 0 := fun hz => hN₁ (by
    rw [eq_neg_of_add_eq_zero_left hz]
    exact (maximalIdeal R ^ N₁).neg_mem hh₁)
  have hgs' := (hstable h hh₀).1
  have hcard := ncard_minimalPrimes_span_singleton_le_length_of_isSystemOfParameters
    hcat hdim hfadd ((maximalIdeal R).add_mem hfm hhm) gs hgs' hlen
  rw [← (hstable h hh₀).2, ← hB] at hcard
  exact ⟨hfadd, by exact_mod_cast hcard⟩

/-- Among sufficiently small perturbations in an ideal, choose one with the largest possible
number of minimal prime divisors. -/
private theorem exists_maximal_minimalPrimes_perturbation
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hcat : Ring.IsCatenary R) {d : ℕ} (hdim : ringKrullDim R = d)
    (J : Ideal R) {f : R} (hf : f ≠ 0) (hfJ : f ∈ J)
    (hfm : f ∈ maximalIdeal R) :
    ∃ N : ℕ, ∃ g : R, g ≠ 0 ∧ g ∈ J ∧ g ∈ maximalIdeal R ∧
      ∀ h ∈ maximalIdeal R ^ N, h ∈ J →
        (Ideal.span {g + h}).minimalPrimes.ncard ≤
          (Ideal.span {g}).minimalPrimes.ncard := by
  obtain ⟨N, B, hNpos, hbound⟩ :=
    exists_uniform_bound_minimalPrimes_perturbation hcat hdim hf hfm
  let s : Set R := {h | h ∈ maximalIdeal R ^ N ∧ h ∈ J}
  have hsne : s.Nonempty := ⟨0, by simp [s]⟩
  let t : R → ℕ := fun h => (Ideal.span {f + h}).minimalPrimes.ncard
  have htbound : ∀ h ∈ s, t h ≤ B := fun h hh => (hbound h hh.1).2
  obtain ⟨h₀, hh₀, hmax⟩ := exists_max_nat_of_bounded_on s hsne t B htbound
  have h₀m : h₀ ∈ maximalIdeal R := Ideal.pow_le_self (by omega : N ≠ 0) hh₀.1
  have hg0 := (hbound h₀ hh₀.1).1
  refine ⟨N, f + h₀, hg0, J.add_mem hfJ hh₀.2,
    (maximalIdeal R).add_mem hfm h₀m, ?_⟩
  intro h hh hJ
  have hsum : h₀ + h ∈ s :=
    ⟨(maximalIdeal R ^ N).add_mem hh₀.1 hh, J.add_mem hh₀.2 hJ⟩
  simpa only [t, add_assoc] using hmax (h₀ + h) hsum

/-- A locally simple perturbation of an element with maximal prime support has radical
principal ideal. -/
private theorem exists_reduced_quotient_of_maximal_perturbation
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [IsIntegrallyClosed R] (J : Ideal R) (N : ℕ) {g : R}
    (hgJ : g ∈ J)
    (hmax : ∀ h ∈ IsLocalRing.maximalIdeal R ^ N, h ∈ J →
      (Ideal.span {g + h}).minimalPrimes.ncard ≤
        (Ideal.span {g}).minimalPrimes.ncard)
    (hrepair : ∃ h : R, h ∈ IsLocalRing.maximalIdeal R ^ N ∧ h ∈ J ∧
      g + h ≠ 0 ∧
      (∀ p ∈ (Ideal.span {g}).minimalPrimes,
        p ∈ (Ideal.span {g + h}).minimalPrimes) ∧
      (∀ p ∈ (Ideal.span {g}).minimalPrimes, ∀ [p.IsPrime],
        (Ideal.map (algebraMap R (Localization.AtPrime p))
          (Ideal.span {g + h})).IsRadical)) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ Ideal.span {f}) := by
  obtain ⟨h, hh, hJ, hne, hcontain, hlocal⟩ := hrepair
  refine ⟨g + h, hne, J.add_mem hgJ hJ, ?_⟩
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact span_singleton_isRadical_of_minimalPrimes_ncard_le hne
    hcontain (hmax h hh hJ) hlocal

/-- A uniformizer does not belong to the square of the maximal ideal. -/
private theorem irreducible_notMem_maximalIdeal_sq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {x : R} (hx : Irreducible x) : x ∉ maximalIdeal R ^ 2 := by
  rw [hx.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨a, ha⟩
  have he : 1 = x * a := by
    apply mul_left_cancel₀ hx.ne_zero
    simpa only [mul_one, pow_two, mul_assoc] using ha
  exact hx.not_isUnit (isUnit_of_dvd_one ⟨a, he⟩)

/-- A nonzero radical ideal has an element whose image at a height-one prime lies outside
the square of the local maximal ideal. -/
private theorem exists_mem_notMem_local_maximalIdeal_sq
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (I p : Ideal R) [p.IsPrime]
    (hI : I.IsRadical) (hI0 : I ≠ ⊥) (hp : p.height = 1) :
    ∃ b ∈ I, algebraMap R (Localization.AtPrime p) b ∉
      maximalIdeal (Localization.AtPrime p) ^ 2 := by
  let S := Localization.AtPrime p
  let φ : R →+* S := algebraMap R S
  have : IsDiscreteValuationRing S := isDiscreteValuationRing_at_height_one p hp
  have hmaprad : (Ideal.map φ I).IsRadical := by
    apply Ideal.radical_eq_iff.mp
    rw [← IsLocalization.map_radical p.primeCompl S I, hI.radical]
  have hinj : Function.Injective φ :=
    IsLocalization.injective S p.primeCompl_le_nonZeroDivisors
  have hmap0 : Ideal.map φ I ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (f := φ) hinj).not.mpr hI0
  have hle := maximalIdeal_le_of_isRadical_of_ne_bot (Ideal.map φ I) hmaprad hmap0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hnot : ¬ I ≤ Ideal.comap φ (maximalIdeal S ^ 2) := by
    intro h
    have h' := (Ideal.map_le_iff_le_comap.mpr h).trans' hle
    exact irreducible_notMem_maximalIdeal_sq hϖ
      (h' (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ))
  exact Set.not_subset.mp hnot

/-- Finite prime avoidance supplies an element of any power of the maximal ideal that
is a unit at each of finitely many nonmaximal primes. -/
@[sga "3 V 4.1" "local ring, special case"]
private theorem exists_mem_pow_notMem_primes
    {R : Type*} [CommRing R] [IsLocalRing R]
    (S : Set (Ideal R)) (hS : S.Finite) (hprime : ∀ p ∈ S, p.IsPrime)
    (hne : ∀ p ∈ S, p ≠ maximalIdeal R) (N : ℕ) :
    ∃ y ∈ maximalIdeal R ^ N, ∀ p ∈ S, y ∉ p :=
  exists_mem_pow_notMem_finite_primes S hS hprime hne N

/-- Local first-order elements can be combined into one perturbation, using separating
factors squared to make every other summand vanish to second order. -/
private theorem exists_perturbation_mem_notMem_local_sq
    {R ι : Type*} [CommRing R] [IsLocalRing R] [Finite ι]
    (p : ι → Ideal R) [∀ i, (p i).IsPrime] (J : Ideal R) (N : ℕ)
    (g y : R) (a b : ι → R)
    (hg : ∀ i, g ∈ p i)
    (hy : y ∈ maximalIdeal R ^ N) (hyout : ∀ i, y ∉ p i)
    (ha : ∀ i, a i ∈ p i) (haout : ∀ i j, i ≠ j → a i ∉ p j)
    (hbJ : ∀ i, b i ∈ J) (hbp : ∀ i, b i ∈ p i)
    (hb2 : ∀ i, algebraMap R (Localization.AtPrime (p i)) (b i) ∉
      maximalIdeal (Localization.AtPrime (p i)) ^ 2) :
    ∃ h ∈ maximalIdeal R ^ N, h ∈ J ∧ ∀ i,
      algebraMap R (Localization.AtPrime (p i)) (g + h) ∈
        maximalIdeal (Localization.AtPrime (p i)) ∧
      algebraMap R (Localization.AtPrime (p i)) (g + h) ∉
        maximalIdeal (Localization.AtPrime (p i)) ^ 2 := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let A i := Localization.AtPrime (p i)
  let φ (i : ι) : R →+* A i := algebraMap R (A i)
  let m (i : ι) := maximalIdeal (A i)
  let w (i : ι) := b i * (∏ j ∈ Finset.univ.erase i, a j ^ 2) * y
  let t (i : ι) := if φ i g ∈ m i ^ 2 then w i else 0
  have hwN (i : ι) : w i ∈ maximalIdeal R ^ N :=
    (maximalIdeal R ^ N).mul_mem_left _ hy
  have hwJ (i : ι) : w i ∈ J :=
    J.mul_mem_right _ (J.mul_mem_right _ (hbJ i))
  have hwi (i : ι) : φ i (w i) ∈ m i ∧ φ i (w i) ∉ m i ^ 2 := by
    have hbmem : φ i (b i) ∈ m i :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (A i) (p i) (b i)).mpr (hbp i)
    have hunit : IsUnit (φ i ((∏ j ∈ Finset.univ.erase i, a j ^ 2) * y)) := by
      rw [map_mul]
      apply IsUnit.mul
      · rw [map_prod]
        apply IsUnit.prod_iff.mpr
        intro j hj
        rw [map_pow]
        exact ((IsLocalization.AtPrime.isUnit_to_map_iff (A i) (p i) (a j)).mpr
          (haout j i (Finset.mem_erase.mp hj).1)).pow 2
      · exact (IsLocalization.AtPrime.isUnit_to_map_iff (A i) (p i) y).mpr (hyout i)
    have heq : φ i (w i) = φ i ((∏ j ∈ Finset.univ.erase i, a j ^ 2) * y) *
        φ i (b i) := by simp only [w, map_mul]; ring
    rw [heq]
    exact ⟨(m i).mul_mem_left _ hbmem,
      fun h => hb2 i (((m i ^ 2).unit_mul_mem_iff_mem hunit).mp h)⟩
  have hwoff (i j : ι) (hij : i ≠ j) : φ i (w j) ∈ m i ^ 2 := by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun k : ι => a k ^ 2)
      (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
    have hai : φ i (a i) ^ 2 ∈ m i ^ 2 := Ideal.pow_mem_pow
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff (A i) (p i) (a i)).mpr (ha i)) 2
    have heq : φ i (w j) = φ i (a i) ^ 2 * (φ i (b j) * φ i c * φ i y) := by
      simp only [w, hc, map_mul, map_pow]
      ring
    rw [heq]
    exact (m i ^ 2).mul_mem_right _ hai
  refine ⟨∑ i, t i, ?_, ?_, ?_⟩
  · apply Ideal.sum_mem
    intro i _
    dsimp [t]
    split_ifs
    · exact hwN i
    · exact Ideal.zero_mem _
  · apply Ideal.sum_mem
    intro i _
    dsimp [t]
    split_ifs
    · exact hwJ i
    · exact J.zero_mem
  · intro i
    have hrest : (∑ j ∈ Finset.univ.erase i, φ i (t j)) ∈ m i ^ 2 := by
      apply Ideal.sum_mem
      intro j hj
      dsimp [t]
      split_ifs
      · exact hwoff i j (Ne.symm (Finset.mem_erase.mp hj).1)
      · simp
    have hrestm : (∑ j ∈ Finset.univ.erase i, φ i (t j)) ∈ m i :=
      (Ideal.pow_le_self (I := m i) (by omega : 2 ≠ 0)) hrest
    have hgmem : φ i g ∈ m i :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (A i) (p i) g).mpr (hg i)
    show φ i (g + ∑ j, t j) ∈ m i ∧ φ i (g + ∑ j, t j) ∉ m i ^ 2
    rw [map_add, map_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    by_cases hgi : φ i g ∈ m i ^ 2
    · have hti : t i = w i := ite_eq_left hgi
      rw [hti]
      refine ⟨(m i).add_mem hgmem ((m i).add_mem hrestm (hwi i).1), ?_⟩
      intro h
      apply (hwi i).2
      convert (m i ^ 2).sub_mem ((m i ^ 2).sub_mem h hgi) hrest using 1
      ring
    · have hti : t i = 0 := ite_eq_right hgi
      rw [hti, map_zero, add_zero]
      refine ⟨(m i).add_mem hgmem hrestm, ?_⟩
      intro h
      apply hgi
      simpa only [add_sub_cancel_right] using (m i ^ 2).sub_mem h hrest

/-- A nonzero element of a radical ideal can be perturbed in any prescribed power of the
maximal ideal to be locally simple at every old height-one prime, provided those primes
are nonmaximal. -/
private theorem exists_locally_simple_perturbation
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [IsIntegrallyClosed R] (J : Ideal R) (hJ : J.IsRadical) (N : ℕ)
    {g : R} (hg0 : g ≠ 0) (hgJ : g ∈ J) (hgm : g ∈ maximalIdeal R)
    (hnmax : ∀ p ∈ (Ideal.span {g}).minimalPrimes, p ≠ maximalIdeal R) :
    ∃ h : R, h ∈ maximalIdeal R ^ N ∧ h ∈ J ∧ g + h ≠ 0 ∧
      (∀ p ∈ (Ideal.span {g}).minimalPrimes,
        p ∈ (Ideal.span {g + h}).minimalPrimes) ∧
      (∀ p ∈ (Ideal.span {g}).minimalPrimes, ∀ [p.IsPrime],
        (Ideal.map (algebraMap R (Localization.AtPrime p))
          (Ideal.span {g + h})).IsRadical) := by
  classical
  let S := (Ideal.span {g}).minimalPrimes
  have hS : S.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing R _
  have hprime (p : Ideal R) (hp : p ∈ S) : p.IsPrime := hp.isPrime
  have hanti (p : Ideal R) (hp : p ∈ S) (q : Ideal R) (hq : q ∈ S)
      (hpq : p ≤ q) : p = q := le_antisymm hpq (hq.2 hp.1 hpq)
  have hheight (p : Ideal R) (hp : p ∈ S) : p.height = 1 :=
    height_eq_one_of_mem_minimalPrimes_span_singleton hg0 hp
  have : Finite S := hS.to_subtype
  let p : S → Ideal R := Subtype.val
  have (i : S) : (p i).IsPrime := hprime (p i) i.2
  obtain ⟨y, hy, hyout⟩ := exists_mem_pow_notMem_primes S hS hprime hnmax N
  have hexA (i : S) : ∃ a ∈ p i, ∀ q ∈ S, q ≠ p i → a ∉ q :=
    exists_mem_notMem_other_of_finite_prime_antichain S hS hprime hanti (p i) i.2
  choose a ha haout using hexA
  have hexB (i : S) : ∃ b ∈ J ⊓ p i,
      algebraMap R (Localization.AtPrime (p i)) b ∉
        maximalIdeal (Localization.AtPrime (p i)) ^ 2 := by
    have hI0 : J ⊓ p i ≠ ⊥ := by
      intro heq
      have hmem : g ∈ J ⊓ p i := ⟨hgJ, i.2.le (Ideal.mem_span_singleton_self g)⟩
      rw [heq] at hmem
      exact hg0 hmem
    exact exists_mem_notMem_local_maximalIdeal_sq (J ⊓ p i) (p i)
      (hJ.inf (hprime (p i) i.2).isRadical) hI0 (hheight (p i) i.2)
  choose b hb hb2 using hexB
  obtain ⟨h, hhN, hhJ, hlocal⟩ := exists_perturbation_mem_notMem_local_sq p J N g y a b
    (fun i => i.2.le (Ideal.mem_span_singleton_self g)) hy (fun i => hyout (p i) i.2)
    ha (fun i j hij => haout i (p j) j.2 (fun heq => hij (Subtype.ext heq.symm)))
    (fun i => (hb i).1) (fun i => (hb i).2) hb2
  have hgne : g + h ≠ 0 := by
    obtain ⟨q, hq, _⟩ := Ideal.exists_minimalPrimes_le
      (J := maximalIdeal R) (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgm))
    intro heq
    have hnot := (hlocal ⟨q, hq⟩).2
    rw [heq, map_zero] at hnot
    exact hnot (Ideal.zero_mem _)
  refine ⟨h, hhN, hhJ, hgne, ?_, ?_⟩
  · intro q hq
    have : q.IsPrime := hprime q hq
    apply mem_minimalPrimes_span_singleton_of_height_one hgne (hheight q hq)
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime q) q (g + h)).mp (hlocal ⟨q, hq⟩).1
  · intro q hq hqp
    have : IsDiscreteValuationRing (Localization.AtPrime q) :=
      isDiscreteValuationRing_at_height_one q (hheight q hq)
    exact isRadical_map_span_singleton_of_mem_not_mem_sq q (hlocal ⟨q, hq⟩).1
      (hlocal ⟨q, hq⟩).2

/-- **Stacks 0BWZ.** A nonzero radical ideal in a catenary Noetherian local normal domain
contains a nonzero element whose principal quotient is reduced. -/
@[stacks 0BWZ]
theorem exists_nonzero_mem_isReduced_quotient_of_isRadical
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    [IsIntegrallyClosed R] (hcat : Ring.IsCatenary R) (J : Ideal R) (hJ : J.IsRadical)
    (hJne : J ≠ ⊥) :
    ∃ f : R, f ≠ 0 ∧ f ∈ J ∧ IsReduced (R ⧸ Ideal.span {f}) := by
  by_cases htop : J = ⊤
  · exact exists_nonzero_mem_isReduced_quotient_of_top J htop
  have hJm : J ≤ maximalIdeal R := le_maximalIdeal htop
  obtain ⟨f, hfJ, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJne
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
  have henot : e ≠ ⊤ := by
    intro ht
    apply ringKrullDim_ne_top (R := R)
    rw [← he, ht]
    rfl
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp henot
  have hdim : ringKrullDim R = d := by rw [← he, ← hd]; rfl
  by_cases hd0 : d = 0
  · have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by simp [hdim, hd0])
    have hfield : IsField R := Ring.KrullDimLE.isField_of_isDomain
    have hunit : IsUnit f := isUnit_iff_exists_inv.mpr (hfield.mul_inv_cancel hf0)
    exact False.elim (htop (J.eq_top_of_isUnit_mem hfJ hunit))
  by_cases hd1 : d = 1
  · exact exists_nonzero_mem_isReduced_quotient_of_isRadical_dim_one
      (by simpa [hd1] using hdim) J hJ hJne
  obtain ⟨N, g, hg0, hgJ, hgm, hmax⟩ :=
    exists_maximal_minimalPrimes_perturbation hcat hdim J hf0 hfJ (hJm hfJ)
  apply exists_reduced_quotient_of_maximal_perturbation J N hgJ hmax
  apply exists_locally_simple_perturbation J hJ N hg0 hgJ hgm
  intro p hp
  exact ne_maximalIdeal_of_height_eq_one (by rw [hdim]; exact_mod_cast hd1)
    (height_eq_one_of_mem_minimalPrimes_span_singleton hg0 hp)

end ReducedPrincipalQuotientInRadicalIdeal
