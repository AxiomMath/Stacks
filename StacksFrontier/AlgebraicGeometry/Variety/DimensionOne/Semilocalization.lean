module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Semilocalization at finitely many prime ideals

The complement of a finite union of prime ideals is multiplicative, because a product lies in
one of the primes only if a factor does. Localizing there gives a semilocal ring whose maximal
ideals are exactly the maximal members of the given family, identified by contraction.

## Main definitions

* `Ideal.primeFamilyCompl` is the complement of the union of the given prime ideals, regarded
  as a submonoid.

## Main results

* `Ideal.finite_maximalSpectrum_localization_primeFamilyCompl` gives semilocality.
* `Ideal.bijOn_under_maximalSpectrum_localization_primeFamilyCompl` identifies the maximal
  ideals by contraction.

## Implementation notes

The finite family is a finset of prime ideals, with primality included in each member's type.
The localization is abstract, so the assertions apply to any algebra which localizes at this
submonoid. Semilocality is finiteness of the maximal spectrum. The correspondence is the
canonical contraction map, expressed as a bijection onto the maximal members of the finset.

## References

* [Stacks Project, Tag 09N6](https://stacks.math.columbia.edu/tag/09N6)
-/

@[expose] public section

namespace Ideal

variable {A : Type*} [CommRing A]

/-- The elements outside every prime ideal in a finite family. -/
@[stacks 09N6 "the multiplicative system"]
public abbrev primeFamilyCompl (s : Finset {p : Ideal A // p.IsPrime}) : Submonoid A :=
  ⨅ p ∈ s, p.1.primeCompl (hp := p.2)

private lemma primeFamilyCompl_disjoint_iff {s : Finset {p : Ideal A // p.IsPrime}}
    {p : Ideal A} :
    Disjoint (primeFamilyCompl s : Set A) (p : Set A) ↔ ∃ q ∈ s, p ≤ q.1 := by
  classical
  constructor
  · intro hd
    have hsub : (p : Set A) ⊆
        ⋃ q ∈ (s.image Subtype.val : Set (Ideal A)), (q : Set A) := by
      intro x hx
      by_contra hn
      apply (Set.disjoint_left.mp hd) ?_ hx
      simpa [primeFamilyCompl, Ideal.mem_primeCompl_iff] using
        (show ∀ q ∈ s, x ∉ q.1 from fun q hq hxq =>
          hn (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_image_of_mem Subtype.val hq)) hxq))
    obtain ⟨q, hq, hpq⟩ :=
      (Ideal.subset_union_prime (s := s.image Subtype.val) (f := id)
        (a := ⊥) (b := ⊥) (I := p) (by
          intro q hq _ _
          rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
          exact r.2)).mp hsub
    rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
    exact ⟨r, hr, hpq⟩
  · rintro ⟨q, hq, hpq⟩
    refine Set.disjoint_left.mpr fun x hxS hxp => ?_
    have hxS' : ∀ (a : Ideal A) (b : a.IsPrime),
        (⟨a, b⟩ : {p : Ideal A // p.IsPrime}) ∈ s → x ∉ a := by
      simpa [primeFamilyCompl, Ideal.mem_primeCompl_iff] using hxS
    exact hxS' q.1 q.2 hq (hpq hxp)

private lemma primeFamilyCompl_member_disjoint {s : Finset {p : Ideal A // p.IsPrime}}
    (q : {p : Ideal A // p.IsPrime}) (hq : q ∈ s) :
    Disjoint (primeFamilyCompl s : Set A) (q.1 : Set A) :=
  primeFamilyCompl_disjoint_iff.mpr ⟨q, hq, le_rfl⟩

private lemma isPrime_map_member {s : Finset {p : Ideal A // p.IsPrime}} (B : Type*)
    [CommRing B] [Algebra A B] [IsLocalization (primeFamilyCompl s) B]
    (q : {p : Ideal A // p.IsPrime}) (hq : q ∈ s) : (q.1.map (algebraMap A B)).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (primeFamilyCompl s) B q.1 q.2
    (primeFamilyCompl_member_disjoint q hq)

private lemma maximalSpectrum_under_eq_of_le_member
    {s : Finset {p : Ideal A // p.IsPrime}} {B : Type*} [CommRing B] [Algebra A B]
    [IsLocalization (primeFamilyCompl s) B] (m : MaximalSpectrum B)
    (q : {p : Ideal A // p.IsPrime}) (hq : q ∈ s)
    (hsub : m.asIdeal.under A ≤ q.1) : m.asIdeal.under A = q.1 := by
  rw [m.isMaximal.eq_of_le (isPrime_map_member B q hq).ne_top
    ((IsLocalization.map_under (primeFamilyCompl s) B m.asIdeal).symm.trans_le
      (Ideal.map_mono hsub))]
  exact IsLocalization.under_map_of_isPrime_disjoint (primeFamilyCompl s) B q.2
    (primeFamilyCompl_member_disjoint q hq)

private lemma exists_under_le_member {s : Finset {p : Ideal A // p.IsPrime}} {B : Type*}
    [CommRing B] [Algebra A B] [IsLocalization (primeFamilyCompl s) B]
    (m : MaximalSpectrum B) : ∃ q ∈ s, m.asIdeal.under A ≤ q.1 :=
  primeFamilyCompl_disjoint_iff.mp
    ((IsLocalization.isPrime_iff_isPrime_disjoint (primeFamilyCompl s) B m.asIdeal).mp
      m.isMaximal.isPrime).2

private lemma maximalSpectrum_under_injective {s : Finset {p : Ideal A // p.IsPrime}}
    {B : Type*} [CommRing B] [Algebra A B] [IsLocalization (primeFamilyCompl s) B] :
    Function.Injective fun m : MaximalSpectrum B => m.asIdeal.under A := by
  intro m n h
  apply MaximalSpectrum.toPrimeSpectrum_injective
  apply PrimeSpectrum.ext
  calc
    m.asIdeal = (m.asIdeal.under A).map (algebraMap A B) :=
      (IsLocalization.map_under (primeFamilyCompl s) B m.asIdeal).symm
    _ = (n.asIdeal.under A).map (algebraMap A B) := congrArg _ h
    _ = n.asIdeal := IsLocalization.map_under (primeFamilyCompl s) B n.asIdeal

/-- Localization outside finitely many prime ideals is semilocal. -/
@[stacks 09N6 "semilocality"]
public theorem finite_maximalSpectrum_localization_primeFamilyCompl
    (s : Finset {p : Ideal A // p.IsPrime})
    {B : Type*} [CommRing B] [Algebra A B] [IsLocalization (primeFamilyCompl s) B] :
    Finite (MaximalSpectrum B) := by
  choose g hgs hg using exists_under_le_member (s := s) (B := B)
  refine Finite.of_injective (fun m => (⟨g m, hgs m⟩ : {q // q ∈ s})) fun m n h => ?_
  exact maximalSpectrum_under_injective (s := s)
    ((maximalSpectrum_under_eq_of_le_member m _ (hgs m) (hg m)).trans
      ((congrArg Subtype.val (congrArg Subtype.val h)).trans
        (maximalSpectrum_under_eq_of_le_member n _ (hgs n) (hg n)).symm))

/-- Contraction identifies the maximal ideals of the localization with the maximal members of
the finite family of prime ideals. -/
@[stacks 09N6 "the maximal ideals", ega "I 8.1.2" "partial"]
public theorem bijOn_under_maximalSpectrum_localization_primeFamilyCompl
    (s : Finset {p : Ideal A // p.IsPrime})
    {B : Type*} [CommRing B] [Algebra A B] [IsLocalization (primeFamilyCompl s) B] :
    Set.BijOn (fun m : MaximalSpectrum B => m.asIdeal.under A) Set.univ
      {p : Ideal A | (∃ q ∈ s, p = q.1) ∧
        ∀ q ∈ s, p ≤ q.1 → p = q.1} := by
  refine ⟨?_, fun m _ n _ h => maximalSpectrum_under_injective (s := s) h, ?_⟩
  · intro m _
    obtain ⟨q, hq, hpq⟩ := exists_under_le_member (s := s) m
    have hmunder := maximalSpectrum_under_eq_of_le_member m q hq hpq
    exact ⟨⟨q, hq, hmunder⟩, fun r hr hpr =>
      maximalSpectrum_under_eq_of_le_member m r hr (by simpa [hmunder] using hpr)⟩
  · rintro p ⟨⟨q, hq, rfl⟩, hmax⟩
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ (isPrime_map_member B q hq).ne_top
    obtain ⟨r, hr, hMr⟩ := exists_under_le_member (s := s) ⟨M, hM⟩
    exact ⟨⟨M, hM⟩, Set.mem_univ _,
      (maximalSpectrum_under_eq_of_le_member ⟨M, hM⟩ r hr hMr).trans
        (hmax r hr ((Ideal.map_le_iff_le_comap.mp hJM).trans hMr)).symm⟩

end Ideal
