module

import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.KrullDimension.DimensionOneNoetherianLocal
public import StacksFrontier.RingTheory.Artinian.Basic
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.Ext
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.RingTheory.Serre.Reduced

/-!
# Parameters in a one-dimensional Noetherian local ring

In a one-dimensional Noetherian local ring, an element of the maximal ideal cuts out the
closed point precisely when it avoids every minimal prime.  Equivalently, its localization
is the product of the localizations at the minimal primes.  Such an element always exists.
When the ring has depth one these conditions also characterize nonzerodivisors and the total
ring of fractions; for a reduced ring the factors are the residue fields.

## Main results

* `IsLocalRing.radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes` and
  `IsLocalRing.notMem_minimalPrimes_iff_localizationAway_equiv_pi_localizationAtPrime` give the
  first three equivalent conditions.
* `IsLocalRing.exists_radical_span_eq_maximalIdeal` gives existence.
* `IsLocalRing.notMem_minimalPrimes_iff_mem_nonZeroDivisors_of_depth_eq_one` and
  `IsLocalRing.notMem_minimalPrimes_iff_localizationAway_equiv_fractionRing_of_depth_eq_one`
  give the two additional characterizations at depth one.
* `IsLocalRing.depth_eq_one_of_isReduced` and
  `IsLocalRing.notMem_minimalPrimes_iff_localizationAway_equiv_pi_residueField_of_isReduced`
  give the reduced case and its residue-field characterization.

## Implementation notes

The equality of algebras in the source is expressed by the existence of an `A`-algebra
equivalence.  The declarations respectively state (1) iff (2), (2) iff (3), existence,
(2) iff (4), (2) iff (5), the depth assertion for reduced rings, and (2) iff (6).

## References

* [Stacks Project, Tag 0C3R](https://stacks.math.columbia.edu/tag/0C3R)
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

/-- The maximal ideal times the top submodule is a proper submodule. -/
private lemma maximalIdeal_smul_top_ne_top (A : Type*) [CommRing A] [IsLocalRing A] :
    maximalIdeal A • (⊤ : Submodule A A) ≠ ⊤ := by
  simpa using (IsLocalRing.maximalIdeal.isMaximal A).ne_top

/-- In a one-dimensional Noetherian ring, every prime is minimal or maximal. -/
private lemma minimal_or_isMaximal_of_krullDim_eq_one
    {A : Type*} [CommRing A] [IsNoetherianRing A] (hdim : ringKrullDim A = 1)
    {p : Ideal A} (hp : p.IsPrime) : p ∈ minimalPrimes A ∨ p.IsMaximal :=
  Ring.krullDimLE_one_iff.mp (Ring.krullDimLE_iff.mpr hdim.le) p hp

/-- The image of the element `f` in any algebra equivalent to `Localization.Away f` is a unit. -/
private lemma isUnit_algebraMap_of_algEquiv_localizationAway
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (f : A)
    (e : Localization.Away f ≃ₐ[A] B) : IsUnit (algebraMap A B f) := by
  rw [← e.commutes]
  exact (IsLocalization.Away.algebraMap_isUnit f).map e

/-- A regular element of the maximal ideal witnesses that the depth is at least one. -/
private lemma one_le_depth_of_regular {A : Type*} [CommRing A] [IsLocalRing A] (t : A)
    (ht : t ∈ maximalIdeal A) (htreg : IsSMulRegular A t) :
    1 ≤ Module.depth A (maximalIdeal A) A := by
  have hreg : RingTheory.Sequence.IsRegular A [t] := by
    rw [RingTheory.Sequence.isRegular_cons_iff]
    refine ⟨htreg, ?_⟩
    have : Nontrivial (QuotSMulTop t A) := by
      apply (Submodule.Quotient.nontrivial_iff).mpr
      intro h
      have h1 : (1 : A) ∈ (⊤ : Submodule A A) := trivial
      rw [← h, Submodule.mem_smul_pointwise_iff_exists] at h1
      obtain ⟨a, -, ha⟩ := h1
      rw [smul_eq_mul] at ha
      exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
        (Ideal.eq_top_of_isUnit_mem _ ht (IsUnit.of_mul_eq_one a ha))
    exact RingTheory.Sequence.IsRegular.nil A _
  rw [Module.depth, ite_eq_right (maximalIdeal_smul_top_ne_top A)]
  exact le_iSup₂_of_le [t] ⟨by simpa using ht, hreg⟩ (by simp)

/-- At dimension one and depth one, the associated primes are exactly the minimal primes. -/
private lemma associatedPrimes_eq_minimalPrimes_of_depth_eq_one
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) (hdepth : Module.depth A (maximalIdeal A) A = 1) :
    associatedPrimes A A = minimalPrimes A := by
  apply Set.Subset.antisymm
  · intro p hp
    rcases minimal_or_isMaximal_of_krullDim_eq_one hdim hp.isPrime with hmin | hmax
    · exact hmin
    · let : p.IsMaximal := hmax
      have hle := Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes hp
      rw [hdepth] at hle
      let : Field (A ⧸ p) := Ideal.Quotient.field p
      have hz : ringKrullDim (A ⧸ p) ≤ 0 :=
        Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 (A ⧸ p))
      have : (↑(1 : ℕ∞) : WithBot ℕ∞) ≤ 0 := hle.trans hz
      exact (not_le_of_gt (by decide : (0 : WithBot ℕ∞) < 1) this).elim
  · have h := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A A
    rwa [Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul A A)] at h

/-- An element of the maximal ideal of a one-dimensional Noetherian local ring cuts out the
closed point exactly when it is in no minimal prime. -/
@[stacks 0C3R "parts (1) and (2)"]
public lemma radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) {f : A} (hf : f ∈ maximalIdeal A) :
    (Ideal.span {f}).radical = maximalIdeal A ↔
      ∀ p ∈ minimalPrimes A, f ∉ p := by
  rw [← zeroLocus_singleton_eq_iff_radical_span_singleton_eq]
  have hm1 : (maximalIdeal A).height = 1 := by
    have hm : ((maximalIdeal A).height : WithBot ℕ∞) = ringKrullDim A :=
      maximalIdeal_height_eq_ringKrullDim
    rw [hdim] at hm
    exact_mod_cast hm
  have hnotmin : maximalIdeal A ∉ minimalPrimes A := by
    intro hmin
    rw [← Ideal.height_eq_zero_iff, hm1] at hmin
    exact one_ne_zero hmin
  constructor
  · intro h p hp hfp
    let q : PrimeSpectrum A := ⟨p, hp.1.1⟩
    have hp' : q ∈ PrimeSpectrum.zeroLocus {f} := by
      simpa [PrimeSpectrum.mem_zeroLocus] using hfp
    rw [h] at hp'
    have hpm : p = maximalIdeal A := by
      simpa only [q, IsLocalRing.closedPoint] using
        congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hp')
    exact hnotmin (hpm ▸ hp)
  · intro hav
    ext p
    constructor
    · intro hfp
      rcases minimal_or_isMaximal_of_krullDim_eq_one hdim p.isPrime with hp | hp
      · exact (hav p hp (by simpa [PrimeSpectrum.mem_zeroLocus] using hfp)).elim
      · exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hp)
    · rintro rfl
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact hf

/-- Avoiding all minimal primes is equivalent to localization away from the element being
the product of the local rings at the minimal primes. -/
@[stacks 0C3R "parts (2) and (3)"]
public lemma notMem_minimalPrimes_iff_localizationAway_equiv_pi_localizationAtPrime
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) {f : A} (hf : f ∈ maximalIdeal A) :
    (∀ p ∈ minimalPrimes A, f ∉ p) ↔
      Nonempty (Localization.Away f ≃ₐ[A]
        (∀ p : minimalPrimes A,
          @Localization.AtPrime A _ p.1 p.2.1.1)) := by
  classical
  constructor
  · intro hav
    let S := Localization.Away f
    have hprimes : {p : Ideal A | p.IsPrime ∧
        Disjoint (Submonoid.powers f : Set A) (p : Set A)} = minimalPrimes A := by
      ext p
      constructor
      · rintro ⟨hp, hdis⟩
        rcases minimal_or_isMaximal_of_krullDim_eq_one hdim hp with h | h
        · exact h
        · have hfp := (Ideal.disjoint_powers_iff_notMem f hp.isRadical).mp hdis
          exact (hfp (IsLocalRing.eq_maximalIdeal h ▸ hf)).elim
      · intro hp
        exact ⟨hp.isPrime, (Ideal.disjoint_powers_iff_notMem f hp.isPrime.isRadical).mpr
          (hav p hp)⟩
    let e : PrimeSpectrum S ≃o minimalPrimes A :=
      (PrimeSpectrum.equivSubtype S).trans
        ((IsLocalization.orderIsoOfPrime (Submonoid.powers f) S).trans
          (Set.orderIsoOfEq _ _ hprimes))
    have : Ring.KrullDimLE 0 S := by
      apply Ring.krullDimLE_zero_iff.mpr
      intro p hp
      obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
      have hle : (e ⟨p, hp⟩).val ≤ (e ⟨m, hm.isPrime⟩).val := e.monotone hpm
      have heq : e ⟨p, hp⟩ = e ⟨m, hm.isPrime⟩ :=
        Subtype.ext (le_antisymm hle ((e ⟨m, hm.isPrime⟩).property.2
          ⟨(e ⟨p, hp⟩).property.isPrime, bot_le⟩ hle))
      have hpm' : p = m := congrArg PrimeSpectrum.asIdeal (e.injective heq)
      exact hpm' ▸ hm
    have : IsArtinianRing S := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
    let L := fun p : minimalPrimes A => @Localization.AtPrime A _ p.val p.property.isPrime
    let e₁ : S ≃ₐ[A] (∀ p : PrimeSpectrum S, Localization.AtPrime p.asIdeal) :=
      (PrimeSpectrum.toPiLocalizationEquiv S).restrictScalars A
    let e₂ : (∀ p : PrimeSpectrum S, Localization.AtPrime p.asIdeal) ≃ₐ[A]
        (∀ p : PrimeSpectrum S, L (e p)) :=
      AlgEquiv.piCongrRight fun p =>
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (Submonoid.powers f) p.asIdeal).symm
    exact ⟨e₁.trans (e₂.trans (AlgEquiv.piCongrLeft A L e.toEquiv))⟩
  · rintro ⟨e⟩ p hp
    let p' : minimalPrimes A := ⟨p, hp⟩
    have : p.IsPrime := hp.isPrime
    have hu : IsUnit (algebraMap A (Localization.AtPrime p) f) :=
      Pi.isUnit_iff.mp (isUnit_algebraMap_of_algEquiv_localizationAway f e) p'
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p f).mp hu

/-- A one-dimensional Noetherian local ring has an element of its maximal ideal whose
principal ideal has radical equal to the maximal ideal. -/
@[stacks 0C3R "existence"]
public lemma exists_radical_span_eq_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (hdim : ringKrullDim A = 1) :
    ∃ f ∈ maximalIdeal A, (Ideal.span {f}).radical = maximalIdeal A := by
  obtain ⟨f, hf, -, hrad⟩ := (IsLocalRing.ringKrullDim_eq_one_tfae (R := A)).out 1 4 |>.mp hdim
  exact ⟨f, hf, hrad⟩

/-- At depth one, the elements avoiding all minimal primes are precisely the
nonzerodivisors. -/
@[stacks 0C3R "part (4)"]
public lemma notMem_minimalPrimes_iff_mem_nonZeroDivisors_of_depth_eq_one
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) (hdepth : Module.depth A (maximalIdeal A) A = 1) (f : A) :
    (∀ p ∈ minimalPrimes A, f ∉ p) ↔ f ∈ nonZeroDivisors A := by
  have hass := associatedPrimes_eq_minimalPrimes_of_depth_eq_one hdim hdepth
  rw [← hass]
  simpa only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_compl_iff, not_exists, not_and] using
    (show f ∉ ⋃ p ∈ associatedPrimes A A, (p : Set A) ↔ f ∈ nonZeroDivisors A by
      rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]; simp)

/-- At depth one, avoiding all minimal primes is equivalent to localization away from the
element being the total ring of fractions. -/
@[stacks 0C3R "part (5)"]
public lemma notMem_minimalPrimes_iff_localizationAway_equiv_fractionRing_of_depth_eq_one
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 1) (hdepth : Module.depth A (maximalIdeal A) A = 1)
    {f : A} (hf : f ∈ maximalIdeal A) :
    (∀ p ∈ minimalPrimes A, f ∉ p) ↔
      Nonempty (Localization.Away f ≃ₐ[A] FractionRing A) := by
  constructor
  · intro hav
    have hfnzd :=
      (notMem_minimalPrimes_iff_mem_nonZeroDivisors_of_depth_eq_one hdim hdepth f).mp hav
    have hpowers : Submonoid.powers f ≤ nonZeroDivisors A :=
      Submonoid.powers_le.mpr hfnzd
    have hdvd : ∀ g ∈ nonZeroDivisors A, ∃ s ∈ Submonoid.powers f, g ∣ s := by
      intro g hg
      by_cases hgu : IsUnit g
      · exact ⟨1, Submonoid.one_mem _, (isUnit_iff_dvd_one.mp hgu)⟩
      have hgavoid :=
        (notMem_minimalPrimes_iff_mem_nonZeroDivisors_of_depth_eq_one hdim hdepth g).mpr hg
      have hradg :=
        (radical_span_eq_maximalIdeal_iff_notMem_minimalPrimes hdim
          (IsLocalRing.mem_maximalIdeal g |>.mpr hgu)).mpr hgavoid
      obtain ⟨n, hn⟩ : f ∈ (Ideal.span {g}).radical := hradg ▸ hf
      exact ⟨f ^ n, ⟨n, rfl⟩, Ideal.mem_span_singleton.mp hn⟩
    have hloc : IsLocalization (nonZeroDivisors A) (Localization.Away f) :=
      (IsLocalization.iff_of_le_of_exists_dvd (S := Localization.Away f)
        (Submonoid.powers f) (nonZeroDivisors A) hpowers hdvd).mp inferInstance
    exact ⟨IsLocalization.algEquiv (nonZeroDivisors A) _ _⟩
  · rintro ⟨e⟩
    apply (notMem_minimalPrimes_iff_mem_nonZeroDivisors_of_depth_eq_one hdim hdepth f).mpr
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    apply IsFractionRing.injective A (FractionRing A)
    apply (isUnit_algebraMap_of_algEquiv_localizationAway f e).mul_left_cancel
    rw [← map_mul, mul_comm f a, ha, map_zero, mul_zero]

/-- A reduced one-dimensional Noetherian local ring has depth one. -/
@[stacks 0C3R "reduced rings have depth one"]
public lemma depth_eq_one_of_isReduced
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdim : ringKrullDim A = 1) :
    Module.depth A (maximalIdeal A) A = 1 := by
  apply le_antisymm
  · have hle :=
      Module.depth_le_supportDim A (maximalIdeal A) A (maximalIdeal_smul_top_ne_top A)
    rw [Module.supportDim_self_eq_ringKrullDim, hdim] at hle
    exact_mod_cast hle
  · obtain ⟨t, ht, hreg⟩ := exists_regular_mem_maximalIdeal (S := A) (by rw [hdim]; simp)
    exact one_le_depth_of_regular t ht hreg

/-- In a reduced one-dimensional Noetherian local ring, avoiding all minimal primes is
equivalent to localization away from the element being the product of the residue fields at
the minimal primes. -/
@[stacks 0C3R "part (6)"]
public lemma notMem_minimalPrimes_iff_localizationAway_equiv_pi_residueField_of_isReduced
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdim : ringKrullDim A = 1) {f : A} (hf : f ∈ maximalIdeal A) :
    (∀ p ∈ minimalPrimes A, f ∉ p) ↔
      Nonempty (Localization.Away f ≃ₐ[A]
        (∀ p : minimalPrimes A, @Ideal.ResidueField A _ p.1 p.2.1.1)) := by
  classical
  let L := fun p : minimalPrimes A => @Localization.AtPrime A _ p.val p.property.isPrime
  let K := fun p : minimalPrimes A => @Ideal.ResidueField A _ p.val p.property.isPrime
  have he : ∀ p : minimalPrimes A, Nonempty (L p ≃ₐ[A] K p) := by
    intro p
    let : p.val.IsPrime := p.property.isPrime
    let : Field (L p) := (isField_localizationAtPrime_of_minimal A p.val p.property).toField
    exact ⟨AlgEquiv.ofBijective (IsScalarTower.toAlgHom A (L p) (K p))
      ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩⟩
  let e := AlgEquiv.piCongrRight fun p => (he p).some
  rw [notMem_minimalPrimes_iff_localizationAway_equiv_pi_localizationAtPrime hdim hf]
  exact ⟨fun ⟨d⟩ => ⟨d.trans e⟩, fun ⟨d⟩ => ⟨d.trans e.symm⟩⟩

end IsLocalRing
