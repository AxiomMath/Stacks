module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Localizations of a semi-local Dedekind domain are basic open subsets

Let `A` be a Dedekind domain with finitely many maximal ideals. Its prime ideals are `⊥` and the
maximal ideals. Hence for a maximal ideal `𝔪`, an element `f ∉ 𝔪` lying in all the other maximal
ideals has `D(f) = {⊥, 𝔪}`, and the localization `A_𝔪` is the localization `A_f`; likewise the
fraction field is a localization `A_f` for a nonzero `f` lying in every nonzero maximal ideal.
On spectra, `Spec A_𝔪 ⟶ Spec A` and `Spec L ⟶ Spec A` are therefore open immersions, with images
the primes contained in `𝔪`, respectively the generic point.

## Main results

* `Stacks.Models.isLocalization_away_of_forall_disjoint`: a localization `S = M⁻¹A` is the
  localization at the powers of `f ∈ M` once every prime avoiding `f` avoids `M`.
* `Stacks.Models.exists_isLocalization_away_of_isLocalization_atPrime` and
  `Stacks.Models.exists_isLocalization_away_of_isFractionRing`: the localizations at a maximal
  ideal and the fraction field of a semi-local Dedekind domain are localizations away from an
  element.
* `Stacks.Models.isOpenImmersion_specMap_of_isLocalization_atPrime` and
  `Stacks.Models.isOpenImmersion_specMap_of_isFractionRing`: the corresponding morphisms of
  spectra are open immersions.
* `Stacks.Models.range_specMap_of_isLocalization_atPrime` and
  `Stacks.Models.range_specMap_of_isFractionRing`: their images.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Models

variable {A : Type u} [CommRing A]

/-- A localization `S = M⁻¹A` is the localization of `A` at the powers of an element `f ∈ M` as
soon as every prime ideal not containing `f` is disjoint from `M`. -/
theorem isLocalization_away_of_forall_disjoint (M : Submonoid A) (S : Type u) [CommRing S]
    [Algebra A S] [IsLocalization M S] (f : A) (hf : f ∈ M)
    (h : ∀ P : Ideal A, P.IsPrime → f ∉ P → Disjoint (M : Set A) P) :
    IsLocalization.Away f S := by
  have hunit : ∀ s ∈ M, IsUnit (algebraMap A (Localization.Away f) s) := by
    intro s hs
    by_contra hns
    obtain ⟨Q, hQ, hsQ⟩ := exists_max_ideal_of_mem_nonunits hns
    have hP : (Q.comap (algebraMap A (Localization.Away f))).IsPrime := hQ.isPrime.comap _
    have hfP : f ∉ Q.comap (algebraMap A (Localization.Away f)) := fun hfQ =>
      hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hfQ (IsLocalization.Away.algebraMap_isUnit f))
    exact Set.disjoint_left.mp (h _ hP hfP) hs hsQ
  have : IsLocalization M (Localization.Away f) :=
    IsLocalization.of_le (Submonoid.powers f) M (Submonoid.powers_le.mpr hf) hunit
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers f)
    (IsLocalization.algEquiv M (Localization.Away f) S)

/-- If there are finitely many maximal ideals, there is an element outside a prime `P` lying in
every maximal ideal other than `P`, provided the maximal ideals contained in `P` equal `P`. -/
private theorem exists_notMem_forall_mem_of_finite_isMaximal_aux
    (hfin : {m : Ideal A | m.IsMaximal}.Finite) (P : Ideal A) [hP : P.IsPrime]
    (hle : ∀ m : Ideal A, m.IsMaximal → m ≤ P → m = P) :
    ∃ f : A, f ∉ P ∧ ∀ m : Ideal A, m.IsMaximal → m ≠ P → f ∈ m := by
  classical
  have hex : ∀ m : Ideal A, m.IsMaximal → m ≠ P → ∃ a ∈ m, a ∉ P := fun m hm hne =>
    Set.not_subset.mp fun h => hne (hle m hm h)
  choose! a ha using hex
  let s := hfin.toFinset.filter (· ≠ P)
  refine ⟨∏ m ∈ s, a m, fun hmem => ?_, fun m hm hne => ?_⟩
  · obtain ⟨m, hms, hm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    have hms' := Finset.mem_filter.mp hms
    exact (ha m (hfin.mem_toFinset.mp hms'.1) hms'.2).2 hm
  · exact Ideal.prod_mem _ (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hm, hne⟩)
      (ha m hm hne).1

/-- If the set of maximal ideals is finite, then for every maximal ideal `m` there is an element
outside `m` lying in every other maximal ideal. -/
theorem exists_notMem_forall_mem_of_finite_isMaximal
    (hfin : {m : Ideal A | m.IsMaximal}.Finite) (m : Ideal A) [hm : m.IsMaximal] :
    ∃ f : A, f ∉ m ∧ ∀ m' : Ideal A, m'.IsMaximal → m' ≠ m → f ∈ m' :=
  exists_notMem_forall_mem_of_finite_isMaximal_aux hfin m fun _ hm' h => hm'.eq_of_le hm.ne_top h

/-- If the set of maximal ideals of a domain is finite, there is a nonzero element lying in
every nonzero maximal ideal. -/
theorem exists_ne_zero_forall_mem_of_finite_isMaximal [IsDomain A]
    (hfin : {m : Ideal A | m.IsMaximal}.Finite) :
    ∃ f : A, f ≠ 0 ∧ ∀ m : Ideal A, m.IsMaximal → m ≠ ⊥ → f ∈ m :=
  exists_notMem_forall_mem_of_finite_isMaximal_aux hfin ⊥ fun _ _ h => le_bot_iff.mp h

variable [IsDedekindDomain A]

/-- In a Dedekind domain a prime ideal contained in two distinct maximal ideals is zero. -/
theorem eq_bot_of_le_of_le_of_ne {P m m' : Ideal A} (hP : P.IsPrime) [m.IsMaximal]
    [m'.IsMaximal] (hm : P ≤ m) (hm' : P ≤ m') (hne : m ≠ m') : P = ⊥ := by
  by_contra hbot
  have hPmax := hP.isMaximal hbot
  exact hne ((hPmax.eq_of_le (Ideal.IsMaximal.ne_top ‹_›) hm).symm.trans
    (hPmax.eq_of_le (Ideal.IsMaximal.ne_top ‹_›) hm'))

/-- **Localizations at maximal ideals of a semi-local Dedekind domain are basic opens.** If a
Dedekind domain `A` has finitely many maximal ideals, its localization at a maximal ideal `m` is
the localization at the powers of an element `f ∉ m`. -/
theorem exists_isLocalization_away_of_isLocalization_atPrime
    (hfin : {m : Ideal A | m.IsMaximal}.Finite) (m : Ideal A) [hm : m.IsMaximal]
    (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalization.AtPrime A' m] :
    ∃ f : A, f ∉ m ∧ IsLocalization.Away f A' := by
  obtain ⟨f, hfm, hf⟩ := exists_notMem_forall_mem_of_finite_isMaximal hfin m
  refine ⟨f, hfm, isLocalization_away_of_forall_disjoint m.primeCompl A' f hfm ?_⟩
  intro P hP hfP
  have hPm : P ≤ m := by
    by_contra hle
    exact hfP (hf P (hP.isMaximal (by rintro rfl; exact hle bot_le)) fun h => hle h.le)
  exact Set.disjoint_left.mpr fun s hs hsP => hs (hPm hsP)

/-- **The fraction field of a semi-local Dedekind domain is a basic open.** If a Dedekind domain
`A` has finitely many maximal ideals, its fraction field is the localization of `A` at the powers
of a nonzero element. -/
theorem exists_isLocalization_away_of_isFractionRing
    (hfin : {m : Ideal A | m.IsMaximal}.Finite) (L : Type u) [Field L] [Algebra A L]
    [IsFractionRing A L] : ∃ f : A, f ≠ 0 ∧ IsLocalization.Away f L := by
  obtain ⟨f, hf0, hf⟩ := exists_ne_zero_forall_mem_of_finite_isMaximal hfin
  refine ⟨f, hf0, isLocalization_away_of_forall_disjoint (nonZeroDivisors A) L f
    (mem_nonZeroDivisors_of_ne_zero hf0) ?_⟩
  intro P hP hfP
  have hPbot : P = ⊥ := by
    by_contra hbot
    exact hfP (hf P (hP.isMaximal hbot) hbot)
  refine Set.disjoint_left.mpr fun s hs hsP => ?_
  rw [hPbot, SetLike.mem_coe, Ideal.mem_bot] at hsP
  exact nonZeroDivisors.ne_zero hs hsP

/-- For a semi-local Dedekind domain `A`, the morphism `Spec A_m ⟶ Spec A` is an open
immersion. -/
theorem isOpenImmersion_specMap_of_isLocalization_atPrime
    (hfin : {m : Ideal A | m.IsMaximal}.Finite) (m : Ideal A) [m.IsMaximal]
    (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalization.AtPrime A' m] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A A'))) := by
  obtain ⟨f, -, hf⟩ := exists_isLocalization_away_of_isLocalization_atPrime hfin m A'
  exact IsOpenImmersion.of_isLocalization f

/-- For a semi-local Dedekind domain `A` with fraction field `L`, the morphism
`Spec L ⟶ Spec A` is an open immersion. -/
theorem isOpenImmersion_specMap_of_isFractionRing
    (hfin : {m : Ideal A | m.IsMaximal}.Finite) (L : Type u) [Field L] [Algebra A L]
    [IsFractionRing A L] : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A L))) := by
  obtain ⟨f, -, hf⟩ := exists_isLocalization_away_of_isFractionRing hfin L
  exact IsOpenImmersion.of_isLocalization f

omit [IsDedekindDomain A] in
/-- The image of `Spec A_m ⟶ Spec A` consists of the primes contained in `m`. -/
theorem range_specMap_of_isLocalization_atPrime (m : Ideal A) [m.IsPrime]
    (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalization.AtPrime A' m] :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap A A'))) =
      {P : PrimeSpectrum A | P.asIdeal ≤ m} := by
  refine (PrimeSpectrum.localization_comap_range A' m.primeCompl).trans ?_
  ext P
  simp only [Set.mem_ofPred_eq, Ideal.primeCompl, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk]
  constructor
  · intro hd x hx
    by_contra hxm
    exact Set.disjoint_left.mp hd hxm hx
  · intro hle
    exact Set.disjoint_left.mpr fun x hx hxP => hx (hle hxP)

omit [IsDedekindDomain A] in
/-- The image of `Spec L ⟶ Spec A`, for `L` the fraction field of the domain `A`, is the generic
point. -/
theorem range_specMap_of_isFractionRing [IsDomain A] (L : Type u) [Field L] [Algebra A L]
    [IsFractionRing A L] :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap A L))) =
      {P : PrimeSpectrum A | P.asIdeal = ⊥} := by
  refine (PrimeSpectrum.localization_comap_range L (nonZeroDivisors A)).trans ?_
  ext P
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hd
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    by_contra hx0
    exact Set.disjoint_left.mp hd (mem_nonZeroDivisors_of_ne_zero hx0) hx
  · intro hbot
    refine Set.disjoint_left.mpr fun x hx hxP => ?_
    rw [hbot, SetLike.mem_coe, Ideal.mem_bot] at hxP
    exact nonZeroDivisors.ne_zero hx hxP

end Stacks.Models

end
