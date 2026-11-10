module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.SurjectiveOnStalks
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents

/-!
# Minimal primes and residue fields of a localization

Let `A` be a localization of `R` at the complement of a prime `p`.  Contraction along
`R → A` identifies the minimal primes of `A` with the minimal primes of `R` contained in
`p`, and corresponding primes have the same residue field.  Consequently the product of the
residue fields of the minimal primes of `A` is the localization, at the image of `R \ p`, of
the product of the residue fields of the minimal primes of `R`.

## Main definitions

* `minimalPrimes.residueFieldProduct` is the product of the residue fields of the minimal
  primes of a commutative ring, and `minimalPrimes.enumResidueFieldProduct` the same product
  for an enumeration of those primes.
* `minimalPrimes.localizationResidueFieldProductHom` is the comparison map from an enumerated
  product of the residue fields at the minimal primes of `R` to the product for `A`.

## Main results

* `minimalPrimes.under_mem_minimalPrimes_of_isLocalization` and
  `minimalPrimes.exists_under_eq`: contraction is a bijection from the minimal primes of `A`
  onto the minimal primes of `R` contained in `p`.
* `minimalPrimes.isLocalization_residueFieldProduct`: the product for `A` is the localization
  of the product for `R` at the image of the complement of `p`.

## Implementation notes

The source of the comparison map is a product indexed by an arbitrary enumeration `σ` of the
minimal primes of `R` rather than by the subtype `minimalPrimes R` itself, so that a product
indexed by another type in bijection with the minimal primes needs no reindexing.

A minimal prime of `R` not contained in `p` contributes a factor that the localization kills,
and the element of `R \ p` doing so is a product over the finitely many such primes; this is
why the localization statement assumes the index type finite.

Surjectivity of the comparison map is proved by writing an element of the target as a sum of
elements supported at one index, whose preimages are given by `Function.update`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public section

universe u

namespace minimalPrimes

/-- A minimal prime ideal is prime. -/
instance isPrime_coe {A : Type u} [CommRing A] (q : minimalPrimes A) :
    (q : Ideal A).IsPrime :=
  q.2.1.1

/-- The product of the residue fields of the minimal primes of a commutative ring. -/
abbrev residueFieldProduct (A : Type u) [CommRing A] : Type u :=
  ∀ q : minimalPrimes A, Ideal.ResidueField (q : Ideal A)

section Comparison

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {ι : Type u} (σ : ι → Ideal R) [∀ i, (σ i).IsPrime]

/-- A product of residue fields of `R`, indexed by an enumeration `σ` of prime ideals. -/
abbrev enumResidueFieldProduct : Type u := ∀ i, Ideal.ResidueField (σ i)

/-- The comparison map from an enumerated product of residue fields of `R` to the product of
the residue fields at the minimal primes of an `R`-algebra `A`, given an indexing `u` of the
minimal primes of `A` by indices whose prime contracts correctly. -/
noncomputable def localizationResidueFieldProductHom
    (u : minimalPrimes A → ι) (hu : ∀ q, σ (u q) = Ideal.under R (q : Ideal A)) :
    enumResidueFieldProduct σ →+* residueFieldProduct A :=
  RingHom.pi fun q =>
    (Ideal.ResidueField.map (σ (u q)) (q : Ideal A) (algebraMap R A) (hu q)).comp
      (Pi.evalRingHom (fun i => Ideal.ResidueField (σ i)) (u q))

/-- The `q`-component of `localizationResidueFieldProductHom σ u hu x` is the image of the
`u q`-component of `x` under the induced map of residue fields. -/
lemma localizationResidueFieldProductHom_apply
    (u : minimalPrimes A → ι) (hu : ∀ q, σ (u q) = Ideal.under R (q : Ideal A))
    (x : enumResidueFieldProduct σ) (q : minimalPrimes A) :
    localizationResidueFieldProductHom σ u hu x q =
      Ideal.ResidueField.map (σ (u q)) (q : Ideal A) (algebraMap R A) (hu q) (x (u q)) := rfl

end Comparison

section Localization

variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
variable (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A p]

include p in
/-- The contraction to `R` of a minimal prime of a localization of `R` at a prime `p` is a
minimal prime of `R`. -/
lemma under_mem_minimalPrimes_of_isLocalization (q : minimalPrimes A) :
    Ideal.under R (q : Ideal A) ∈ minimalPrimes R :=
  (PrimeSpectrum.minimalPrimesLocalizationEquivMinimalPrimesBelow R p A q).2.1

/-- The contraction to `R` of a minimal prime of `A` is contained in `p`. -/
lemma under_le (q : minimalPrimes A) : Ideal.under R (q : Ideal A) ≤ p :=
  (PrimeSpectrum.minimalPrimesLocalizationEquivMinimalPrimesBelow R p A q).2.2

include p in
/-- Contraction to `R` is injective on the minimal primes of `A`. -/
lemma under_injective :
    Function.Injective fun q : minimalPrimes A => Ideal.under R (q : Ideal A) := by
  intro q₁ q₂ h
  exact (PrimeSpectrum.minimalPrimesLocalizationEquivMinimalPrimesBelow R p A).injective
    (Subtype.ext h)

/-- Every minimal prime of `R` contained in `p` is the contraction of a minimal prime of `A`. -/
lemma exists_under_eq (p' : Ideal R) (hp' : p' ∈ minimalPrimes R) (hle : p' ≤ p) :
    ∃ q : minimalPrimes A, Ideal.under R (q : Ideal A) = p' := by
  refine ⟨(PrimeSpectrum.minimalPrimesLocalizationEquivMinimalPrimesBelow R p A).symm
    ⟨p', hp', hle⟩, ?_⟩
  have := (PrimeSpectrum.minimalPrimesLocalizationEquivMinimalPrimesBelow R p A).apply_symm_apply
    ⟨p', hp', hle⟩
  exact congrArg (fun z : { q : Ideal R // q ∈ minimalPrimes R ∧ q ≤ p } => (z : Ideal R)) this

variable {ι : Type u} {σ : ι → Ideal R} [∀ i, (σ i).IsPrime]
variable (hmem : ∀ i, σ i ∈ minimalPrimes R) (hinj : Function.Injective σ)
  (hsurj : ∀ p' ∈ minimalPrimes R, ∃ i, σ i = p') (hfin : Finite ι)

omit [∀ i, (σ i).IsPrime] in
include p hsurj in
/-- Some index of the enumeration matches the contraction of a minimal prime of `A`. -/
lemma exists_eq_under (q : minimalPrimes A) : ∃ i, σ i = Ideal.under R (q : Ideal A) :=
  hsurj _ (under_mem_minimalPrimes_of_isLocalization p A q)

include p in
/-- The residue field at a minimal prime of `A` is the residue field of `R` at the matching
index of the enumeration. -/
lemma bijective_residueFieldMap_under (u : minimalPrimes A → ι)
    (hu : ∀ q, σ (u q) = Ideal.under R (q : Ideal A)) (q : minimalPrimes A) :
    Function.Bijective
      (Ideal.ResidueField.map (σ (u q)) (q : Ideal A) (algebraMap R A) (hu q)) :=
  (RingHom.surjectiveOnStalks_of_isLocalization p.primeCompl A).residueFieldMap_bijective
    _ _ (hu q)

/-- The residue field at a minimal prime of `A`, as an isomorphic copy of the residue field of
`R` at the matching index of the enumeration. -/
noncomputable abbrev residueFieldEquivUnder (u : minimalPrimes A → ι)
    (hu : ∀ q, σ (u q) = Ideal.under R (q : Ideal A)) (q : minimalPrimes A) :
    Ideal.ResidueField (σ (u q)) ≃+* Ideal.ResidueField (q : Ideal A) :=
  RingEquiv.ofBijective _ (bijective_residueFieldMap_under p A u hu q)

omit [∀ i, (σ i).IsPrime] in
include p in
/-- An indexing `u` of the minimal primes of `A` compatible with contraction is injective. -/
lemma index_injective (u : minimalPrimes A → ι)
    (hu : ∀ q, σ (u q) = Ideal.under R (q : Ideal A)) : Function.Injective u := by
  intro q₁ q₂ h
  refine under_injective p A ?_
  change Ideal.under R (q₁ : Ideal A) = Ideal.under R (q₂ : Ideal A)
  rw [← hu q₁, ← hu q₂, h]

omit [∀ i, (σ i).IsPrime] in
include hmem hinj in
/-- Every index `i` with `σ i ≤ p` is the index `u q` of some minimal prime `q` of `A`. -/
lemma exists_index_eq (u : minimalPrimes A → ι)
    (hu : ∀ q, σ (u q) = Ideal.under R (q : Ideal A)) (i : ι) (hle : σ i ≤ p) :
    ∃ q : minimalPrimes A, u q = i := by
  obtain ⟨q, hq⟩ := exists_under_eq p A (σ i) (hmem i) hle
  exact ⟨q, hinj (by rw [hu q, hq])⟩

include p hfin in
/-- For a finite index type, the comparison map `localizationResidueFieldProductHom σ u hu` is
surjective. -/
lemma localizationResidueFieldProductHom_surjective (u : minimalPrimes A → ι)
    (hu : ∀ q, σ (u q) = Ideal.under R (q : Ideal A)) :
    Function.Surjective (localizationResidueFieldProductHom σ u hu) := by
  classical
  have hιfin : Finite ι := hfin
  have : Finite (minimalPrimes A) :=
    Finite.of_injective u (index_injective p A u hu)
  have : Fintype (minimalPrimes A) := Fintype.ofFinite _
  intro z
  refine ⟨∑ q : minimalPrimes A, Function.update (0 : enumResidueFieldProduct σ) (u q)
    ((residueFieldEquivUnder p A u hu q).symm (z q)), ?_⟩
  funext q
  rw [map_sum, Finset.sum_apply]
  refine (Finset.sum_eq_single q (fun q₀ _ hne => ?_)
    (fun h => absurd (Finset.mem_univ q) h)).trans ?_
  · rw [localizationResidueFieldProductHom_apply,
      Function.update_of_ne (fun h => hne (index_injective p A u hu h.symm)),
      Pi.zero_apply, map_zero]
  · rw [localizationResidueFieldProductHom_apply, Function.update_self]
    exact (residueFieldEquivUnder p A u hu q).apply_symm_apply (z q)

include p hfin hmem hinj in
/-- The product of the residue fields at the minimal primes of a localization of `R` at a prime
`p` is the localization, at the image of the complement of `p`, of the product of the residue
fields at the minimal primes of `R`. -/
theorem isLocalization_residueFieldProduct (u : minimalPrimes A → ι)
    (hu : ∀ q, σ (u q) = Ideal.under R (q : Ideal A)) :
    letI : Algebra (enumResidueFieldProduct σ) (residueFieldProduct A) :=
      (localizationResidueFieldProductHom σ u hu).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (enumResidueFieldProduct σ) p.primeCompl)
      (residueFieldProduct A) := by
  classical
  let : Algebra (enumResidueFieldProduct σ) (residueFieldProduct A) :=
    (localizationResidueFieldProductHom σ u hu).toAlgebra
  have halg : ∀ x : enumResidueFieldProduct σ,
      algebraMap (enumResidueFieldProduct σ) (residueFieldProduct A) x =
        localizationResidueFieldProductHom σ u hu x := fun _ => rfl
  have hιfin : Finite ι := hfin
  have : Fintype ι := Fintype.ofFinite _
  have hpi : ∀ (r : R) (i : ι), algebraMap R (enumResidueFieldProduct σ) r i =
      algebraMap R (Ideal.ResidueField (σ i)) r := fun _ _ => rfl
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨s, hs, hy⟩ := y.2
    rw [Pi.isUnit_iff]
    intro q
    rw [halg, localizationResidueFieldProductHom_apply, ← hy]
    rw [hpi, Ideal.ResidueField.map_algebraMap]
    exact (IsLocalization.map_units A ⟨s, hs⟩).map
      (algebraMap A (Ideal.ResidueField (q : Ideal A)))
  · intro z
    obtain ⟨x, hx⟩ :=
      localizationResidueFieldProductHom_surjective p A hfin u hu z
    exact ⟨⟨x, 1⟩, by simpa [halg] using hx.symm⟩
  · intro x y hxy
    simp only [halg] at hxy
    have key : ∀ i : ι, ∃ a : R, a ∈ p.primeCompl ∧ (¬ (σ i ≤ p) → a ∈ σ i) := by
      intro i
      by_cases h : σ i ≤ p
      · exact ⟨1, fun hone => p.ne_top_iff_one.mp (Ideal.IsPrime.ne_top ‹p.IsPrime›) hone,
          fun hc => absurd h hc⟩
      · obtain ⟨a, ha, ha'⟩ := IsConcreteLE.not_le_iff_exists.mp h
        exact ⟨a, ha', fun _ => ha⟩
    choose t htmem htbad using key
    refine ⟨⟨algebraMap R (enumResidueFieldProduct σ) (∏ i : ι, t i),
      ∏ i : ι, t i, Submonoid.prod_mem _ (fun i _ => htmem i), rfl⟩, ?_⟩
    funext i
    by_cases hle : σ i ≤ p
    · obtain ⟨q, rfl⟩ := exists_index_eq p A hmem hinj u hu i hle
      have hq := congrFun hxy q
      rw [localizationResidueFieldProductHom_apply,
        localizationResidueFieldProductHom_apply] at hq
      simp only [Pi.mul_apply]
      rw [(residueFieldEquivUnder p A u hu q).injective hq]
    · have hzero :
          (algebraMap R (enumResidueFieldProduct σ) (∏ i : ι, t i)) i = 0 := by
        rw [hpi, Ideal.algebraMap_residueField_eq_zero]
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
        rw [hc]
        exact Ideal.mul_mem_right _ _ (htbad i hle)
      simp only [Pi.mul_apply, hzero, zero_mul]

end Localization

end minimalPrimes
