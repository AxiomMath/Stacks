module

public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator.LocalDuality

/-!
# Annihilators of localizations

Annihilators of the localizations of a finite module, uniformly over a set of primes; the
localization of `H^i_T(K)` at a prime as local cohomology of the localized complex; and the Krull
dimension of `(A/𝔭)_𝔮` read off a dimension function.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Stacks.Algebraization (krullDimToEInt)

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.LocalCohomology

open CategoryTheory.Limits CategoryTheory.Pretriangulated

theorem annihilator_localization_iff_notMem_support_smul
    {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    (J : Ideal A) (q : PrimeSpectrum A) :
    J ≤ Module.annihilator A (LocalizedModule q.asIdeal.primeCompl M) ↔
      q ∉ Module.support A ↥(J • (⊤ : Submodule A M)) := by
  rw [Module.notMem_support_iff]
  let f := LocalizedModule.mkLinearMap q.asIdeal.primeCompl M
  let N := J • (⊤ : Submodule A M)
  have hloc : Subsingleton (LocalizedModule q.asIdeal.primeCompl N) ↔
      N.localized₀ q.asIdeal.primeCompl f = ⊥ := by
    rw [← Submodule.subsingleton_iff_eq_bot]
    exact (IsLocalizedModule.linearEquiv q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N)
      (N.toLocalized₀ q.asIdeal.primeCompl f)).toEquiv.subsingleton_congr
  rw [hloc, Submodule.localized₀_smul, Submodule.localized₀_top]
  rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top]

private theorem isOpen_annihilator_localization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (J : Ideal A) :
    IsOpen {q : PrimeSpectrum A |
      J ≤ Module.annihilator A (LocalizedModule q.asIdeal.primeCompl M)} := by
  simp_rw [annihilator_localization_iff_notMem_support_smul]
  show IsOpen (Module.support A ↥(J • (⊤ : Submodule A M)))ᶜ
  rw [Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

private theorem exists_uniform_annihilator_localization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (S T : Set (PrimeSpectrum A))
    (h : ∀ q ∈ S, ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
      J ≤ Module.annihilator A (LocalizedModule q.asIdeal.primeCompl M)) :
    ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
      ∀ q ∈ S, J ≤ Module.annihilator A (LocalizedModule q.asIdeal.primeCompl M) := by
  classical
  choose J hJT hJ using fun q : S => h q q.property
  let U (q : S) : Set (PrimeSpectrum A) :=
    {r | J q ≤ Module.annihilator A (LocalizedModule r.asIdeal.primeCompl M)}
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact S).elim_finite_subcover U
    (fun q => isOpen_annihilator_localization M (J q))
    (fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, hJ ⟨q, hq⟩⟩)
  refine ⟨t.inf J, ?_, ?_⟩
  · have hfin : ∀ t : Finset S, PrimeSpectrum.zeroLocus ((t.inf J : Ideal A) : Set A) ⊆ T := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | @insert q t hq ih =>
          rw [Finset.inf_insert, PrimeSpectrum.zeroLocus_inf]
          exact Set.union_subset (hJT q) ih
    exact hfin t
  · intro q hq
    obtain ⟨r, hr, hqr⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact (Finset.inf_le hr).trans hqr

open Module.associatedPrimes in
theorem mem_support_iff_exists_associatedPrime_le
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] (q : PrimeSpectrum A) :
    q ∈ Module.support A M ↔
      ∃ p : Ideal A, p ∈ associatedPrimes A M ∧ p ≤ q.asIdeal := by
  constructor
  · intro hq
    let B := Localization.AtPrime q.asIdeal
    let N := LocalizedModule q.asIdeal.primeCompl M
    have : Nontrivial N := Module.mem_support_iff.mp hq
    have : IsNoetherianRing B :=
      IsLocalization.isNoetherianRing q.asIdeal.primeCompl B inferInstance
    obtain ⟨P, hP⟩ := associatedPrimes.nonempty B N
    have hPprime : P.IsPrime := hP.isPrime
    refine ⟨P.comap (algebraMap A B), ?_, ?_⟩
    · exact comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
        q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
        P hP (Ideal.FG.of_isNoetherianRing _)
    · exact ((IsLocalization.AtPrime.orderIsoOfPrime B q.asIdeal) ⟨P, hPprime⟩).property.2
  · rintro ⟨p, hp, hpq⟩
    have : p.IsPrime := hp.isPrime
    have hpM : (⟨p, hp.isPrime⟩ : PrimeSpectrum A) ∈ Module.support A M := by
      by_contra h
      have : Subsingleton (LocalizedModule p.primeCompl M) := Module.notMem_support_iff.mp h
      exact not_isAssociatedPrime_of_subsingleton
        (Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp)
    exact Module.mem_support_mono hpq hpM

theorem support_subset_of_associatedPrimes_subset
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (h : ∀ (p : Ideal A) (hp : p ∈ associatedPrimes A M),
      (⟨p, hp.isPrime⟩ : PrimeSpectrum A) ∈ T) :
    Module.support A M ⊆ T := by
  intro q hq
  obtain ⟨p, hp, hpq⟩ := (mem_support_iff_exists_associatedPrime_le M q).mp hq
  exact hT ((PrimeSpectrum.le_iff_specializes ⟨p, hp.isPrime⟩ q).mp hpq) (h p hp)

theorem exists_annihilator_localization_iff
    {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (q : PrimeSpectrum A)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) :
    (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
      J ≤ Module.annihilator A (LocalizedModule q.asIdeal.primeCompl M)) ↔
    ∀ p : PrimeSpectrum A, p.asIdeal ≤ q.asIdeal → p ∈ Module.support A M → p ∈ T := by
  let B := Localization.AtPrime q.asIdeal
  let N := LocalizedModule q.asIdeal.primeCompl M
  let f := LocalizedModule.mkLinearMap q.asIdeal.primeCompl M
  have hbase := IsLocalizedModule.isBaseChange q.asIdeal.primeCompl B f
  have : Module.Finite B N := Module.Finite.equiv hbase.equiv
  let e := IsLocalization.AtPrime.orderIsoOfPrime B q.asIdeal
  constructor
  · rintro ⟨J, hJ, hJN⟩ p hpq hpM
    let Q := e.symm ⟨p.asIdeal, p.isPrime, hpq⟩
    let p' : PrimeSpectrum B := ⟨Q.val, Q.property⟩
    have he : (e Q).val = p.asIdeal := congrArg Subtype.val (e.apply_symm_apply _)
    have hc : PrimeSpectrum.comap (algebraMap A B) p' = p := PrimeSpectrum.ext he
    have hp'N : p' ∈ Module.support B N := by
      rw [hbase.support_eq_preimage_comap]
      show PrimeSpectrum.comap (algebraMap A B) p' ∈ Module.support A M
      rw [hc]
      exact hpM
    apply hJ
    show J ≤ p.asIdeal
    intro a ha
    rw [← he]
    apply Module.annihilator_le_of_mem_support hp'N
    rw [Module.mem_annihilator]
    intro x
    simpa only [algebraMap_smul] using Module.mem_annihilator.mp (hJN ha) x
  · intro h
    let J := (Module.annihilator B N).comap (algebraMap A B)
    refine ⟨J, ?_, ?_⟩
    · intro r hr
      obtain ⟨Q, hQ, hprime, hQr⟩ :=
        Ideal.exists_ideal_comap_le_prime r.asIdeal (Module.annihilator B N) hr
      let p' : PrimeSpectrum B := ⟨Q, hprime⟩
      let p := PrimeSpectrum.comap (algebraMap A B) p'
      have hpq : p.asIdeal ≤ q.asIdeal := (e ⟨Q, hprime⟩).property.2
      have hpM : p ∈ Module.support A M := by
        have hp'N : p' ∈ Module.support B N := Module.mem_support_iff_of_finite.mpr hQ
        rw [hbase.support_eq_preimage_comap] at hp'N
        exact hp'N
      exact hT ((PrimeSpectrum.le_iff_specializes p r).mp hQr) (h p hpq hpM)
    · intro a ha
      change algebraMap A B a ∈ Module.annihilator B N at ha
      rw [Module.mem_annihilator] at ha ⊢
      intro x
      simpa only [algebraMap_smul] using ha x

theorem exists_uniform_annihilator_localization_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (S T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) :
    (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
      ∀ q ∈ S, J ≤ Module.annihilator A (LocalizedModule q.asIdeal.primeCompl M)) ↔
    ∀ q ∈ S, ∀ p : PrimeSpectrum A,
      p.asIdeal ≤ q.asIdeal → p ∈ Module.support A M → p ∈ T := by
  constructor
  · rintro ⟨J, hJ, hJM⟩ q hq
    exact (exists_annihilator_localization_iff M q T hT).mp ⟨J, hJ, hJM q hq⟩
  · intro h
    exact exists_uniform_annihilator_localization M S T
      (fun q hq => (exists_annihilator_localization_iff M q T hT).mpr (h q hq))

/-- **Local cohomology with support in `T` commutes with localization at a prime.** Extending
scalars along `A → A_𝔮` carries `H^i_T(K)` to `H^i_{T_𝔮}(K_𝔮)`, where `T_𝔮` is the preimage of
`T` in `Spec(A_𝔮)` and `K_𝔮` is the localized complex of
`Stacks.LocalCohomology.localizedComplex`.  The subset `T` is arbitrary among the
specialization-stable ones and the prime `𝔮` is arbitrary; this is flat base change
[Stacks, Tag 0EF5] along `A → A_𝔮` for a bounded-below object.

The form in which a client usually wants it is
`Stacks.LocalCohomology.localCohomologyLocalizationLinearEquiv`, where extension of scalars has
been rewritten as the localized module. -/
noncomputable def localCohomologyLocalizationIso
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (q : PrimeSpectrum A) (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap A (Localization.AtPrime q.asIdeal))).obj
      (localCohomologyWithSupportInPlus
        A T K i) ≅
      localCohomologyWithSupportInPlus
        (Localization.AtPrime q.asIdeal)
        ((PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q.asIdeal))) ⁻¹' T)
        (localizedComplex.{u, v} q K) i := by
  let B := Localization.AtPrime q.asIdeal
  let f := algebraMap A B
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing q.asIdeal.primeCompl B inferInstance
  let F := ModuleCat.extendScalars.{u, u, max u v} f
  letI : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _ hf
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i
  let R := derivedSectionsWithSupportIn.{u, v} B
    ((PrimeSpectrum.comap f) ⁻¹' T)
  let e := derivedExtensionScalarsIsoMap.{u, v} f hf
  let eBC := (derivedSectionsWithSupportInPlusBaseChangeIso.{u, v, u} f hf T hT).val
  exact ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso F i).app
      ((derivedSectionsWithSupportInPlus
        A T).obj K).obj).symm ≪≫
    H.mapIso ((e.app _).symm ≪≫ eBC.app K ≪≫ R.mapIso (e.app K.obj)) ≪≫
    (localCohomologyPlusIso B ((PrimeSpectrum.comap f) ⁻¹' T) (localizedComplex.{u, v} q K) i).symm

private theorem annihilator_le_localizedModule
    {A : Type u} [CommRing A] (S : Submonoid A)
    (M : Type u) [AddCommGroup M] [Module A M] :
    Module.annihilator A M ≤ Module.annihilator A (LocalizedModule S M) := by
  intro r hr
  rw [Module.mem_annihilator] at hr ⊢
  intro x
  induction x using LocalizedModule.induction_on with
  | _ m s => rw [LocalizedModule.smul'_mk, hr, LocalizedModule.zero_mk]

/-- **The localization of `H^i_T(K)` at `𝔮` is the local cohomology of the localized complex.**
This is `Stacks.LocalCohomology.localCohomologyLocalizationIso` with the extension of scalars
along `A → A_𝔮` identified with `LocalizedModule 𝔮ᶜ`, so that the left-hand side is literally
the module whose nontriviality is membership of `𝔮` in `Module.support A (H^i_T(K))`. -/
noncomputable def localCohomologyLocalizationLinearEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (q : PrimeSpectrum A) (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) (i : ℤ) :
    LocalizedModule q.asIdeal.primeCompl
      (localCohomologyWithSupportInPlus
        A T K i) ≃ₗ[Localization.AtPrime q.asIdeal]
      localCohomologyWithSupportInPlus
        (Localization.AtPrime q.asIdeal)
        ((PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q.asIdeal))) ⁻¹' T)
        (localizedComplex.{u, v} q K) i := by
  let M := localCohomologyWithSupportInPlus
    A T K i
  let B := Localization.AtPrime q.asIdeal
  let e := IsLocalizedModule.isBaseChange q.asIdeal.primeCompl B
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
  exact e.equiv.symm.trans
    ((StacksDraft.PseudoCoherence.extendScalarsTensorIso (S := B) M).symm ≪≫
      localCohomologyLocalizationIso T hT q K i).toLinearEquiv

theorem map_annihilator_le_localCohomology_localizedComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (q : PrimeSpectrum A) (K : DerivedCategory.Plus (ModuleCat.{u} A)) (i : ℤ) :
    (Module.annihilator A
      (localCohomologyWithSupportInPlus
        A T K i)).map (algebraMap A (Localization.AtPrime q.asIdeal)) ≤
      Module.annihilator (Localization.AtPrime q.asIdeal)
        (localCohomologyWithSupportInPlus
          (Localization.AtPrime q.asIdeal)
          ((PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q.asIdeal))) ⁻¹' T)
          (localizedComplex.{u, u} q K) i) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Module.mem_annihilator]
  let e := localCohomologyLocalizationLinearEquiv T hT q K i
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← e.map_smul, algebraMap_smul]
  rw [Module.mem_annihilator.mp (annihilator_le_localizedModule q.asIdeal.primeCompl _ ha) x,
    map_zero]

theorem support_localCohomologyPlus_subset
    {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory.Plus (ModuleCat.{u} A)) (i : ℤ) :
    Module.support A
      (localCohomologyWithSupportInPlus
        A T K i) ⊆ T :=
  (supportModuleProperty A T : ObjectProperty (ModuleCat.{u} A)).prop_of_iso
    (localCohomologyPlusIso A T K i).symm
    (Stacks.LocalCohomology.support_localCohomologyWithSupportIn_subset T K.obj i)

theorem pow_le_annihilator_localCohomology_of_homology
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (a : ℤ) (n : ℕ) [K.obj.IsGE a] (I : Ideal A)
    (hI : ∀ i : ℤ, i ≤ a + n → I ≤ Module.annihilator A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    ∀ i : ℤ, i ≤ a + n → I ^ (n + 1) ≤ Module.annihilator A
      (localCohomologyWithSupportInPlus
        A T K i) := by
  let F := derivedSectionsWithSupportIn.{u, u} A T
  let : F.Linear A := Stacks.LocalCohomology.derivedSectionsWithSupportIn_linear A T
  let : F.CommShift ℤ := Stacks.LocalCohomology.derivedSectionsWithSupportIn_commShift A T
  let : F.IsTriangulated := Stacks.LocalCohomology.derivedSectionsWithSupportIn_isTriangulated A T
  have h := pow_le_annihilator_homology_map_of_homology F
    (fun X b hX => isGE_derivedSectionsWithSupportIn A T X b) a n K.obj I hI
  intro i hi
  exact (h i hi).trans_eq (localCohomologyPlusIso A T K i).symm.toLinearEquiv.annihilator_eq

private theorem krullDim_eq_rank_difference
    {α : Type*} [PartialOrder α] [BoundedOrder α]
    (ρ : α → ℤ) (hρ : StrictMono ρ)
    (hstep : ∀ x y : α, x ⋖ y → ρ y = ρ x + 1) :
    Order.krullDim α = ((ρ ⊤ - ρ ⊥).toNat : ℕ) := by
  have hlen (s : LTSeries α) : (s.length : ℤ) ≤ ρ ⊤ - ρ ⊥ := by
    let t : LTSeries ℤ := s.map ρ hρ
    have h := t.apply_add_index_le_apply_add_index_int 0 (Fin.last s.length) (Fin.zero_le _)
    have h₁ := hρ.monotone (bot_le : (⊥ : α) ≤ s.head)
    have h₂ := hρ.monotone (le_top : s.last ≤ (⊤ : α))
    change ρ (s 0) + (Fin.last s.length).val ≤
      ρ (s (Fin.last s.length)) + (0 : Fin (s.length + 1)).val at h
    simp only [Fin.val_last, Fin.val_zero, Int.natCast_zero, add_zero] at h
    change ρ ⊥ ≤ ρ (s 0) at h₁
    change ρ (s (Fin.last s.length)) ≤ ρ ⊤ at h₂
    omega
  have : FiniteDimensionalOrder α := by
    apply (not_infiniteDimensionalOrder_iff (α := α)).mp
    intro hInf
    obtain ⟨s, hs⟩ := hInf.exists_relSeries_with_length ((ρ ⊤ - ρ ⊥).toNat + 1)
    have h := hlen s
    rw [hs] at h
    omega
  have : WellFoundedLT α := ⟨SetRel.IsWellFounded.of_finiteDimensional {(x, y) : α × α | x < y}⟩
  have : WellFoundedGT α := ⟨SetRel.IsWellFounded.inv_of_finiteDimensional {(x, y) : α × α | x < y}⟩
  obtain ⟨t, e, he, hbot, htop⟩ :=
    (LTSeries.longestOf α).exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
  have hv : ∀ j : Fin (t.length + 1), ρ (t j) = ρ t.head + j.val := by
    intro j
    induction j using Fin.induction with
    | zero => simp [RelSeries.head]
    | succ j ih =>
        have h := hstep _ _ (t.step j)
        simp only [Fin.val_succ]
        change ρ (t j.castSucc) = ρ t.head + (j.val : ℤ) at ih
        omega
  have htlen : (t.length : ℤ) = ρ ⊤ - ρ ⊥ := by
    have h := hv (Fin.last t.length)
    change ρ t.last = ρ t.head + t.length at h
    rw [hbot, htop] at h
    omega
  have hle : (LTSeries.longestOf α).length ≤ t.length := by
    have h := Fintype.card_le_of_injective e e.injective
    simpa using h
  have htle := LTSeries.longestOf_is_longest
    (⟨t.length, t, fun i => (t.step i).lt⟩ : LTSeries α)
  change t.length ≤ (LTSeries.longestOf α).length at htle
  rw [Order.krullDim_eq_length_of_finiteDimensionalOrder]
  congr 1
  have hl := hlen (LTSeries.longestOf α)
  omega

private theorem krullDim_Icc_dimensionFunction
    {A : Type u} [CommRing A]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (p q : PrimeSpectrum A) (hpq : p ≤ q) :
    Order.krullDim (Set.Icc p q) = ((δ p - δ q).toNat : ℕ) := by
  let : Fact (p ≤ q) := ⟨hpq⟩
  suffices h : Order.krullDim (Set.Icc p q) = ((-δ q - -δ p).toNat : ℕ) by
    simpa only [neg_sub_neg] using h
  apply krullDim_eq_rank_difference (fun r : Set.Icc p q => -δ r.val)
  · intro r s hrs
    exact neg_lt_neg (δ.strictAnti_specializes
      ((PrimeSpectrum.le_iff_specializes _ _).mp hrs.le) (fun h => hrs.ne (Subtype.ext h)))
  · intro r s hrs
    have himm : TopologicalSpace.IsImmediateSpecialization r.val s.val := by
      refine ⟨(PrimeSpectrum.le_iff_specializes _ _).mp hrs.le, ?_, ?_⟩
      · exact fun heq => hrs.ne (Subtype.ext heq)
      · intro z hrz hzs
        have hrz' := (PrimeSpectrum.le_iff_specializes _ _).mpr hrz
        have hzs' := (PrimeSpectrum.le_iff_specializes _ _).mpr hzs
        let z' : Set.Icc p q := ⟨z, r.property.1.trans hrz', hzs'.trans s.property.2⟩
        have hmid := hrs.eq_or_eq (show r ≤ z' from hrz') (show z' ≤ s from hzs')
        exact hmid.imp (fun h => congrArg Subtype.val h) (fun h => congrArg Subtype.val h)
    have h := δ.step_immediate himm
    omega

private noncomputable def localizedQuotientSpectrumOrderIso
    {A : Type u} [CommRing A] (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) :
    letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hpq
    PrimeSpectrum (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal))) ≃o
      Set.Icc p q := by
  letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpq
  let Q : PrimeSpectrum (A ⧸ p.asIdeal) :=
    ⟨q.asIdeal.map (Ideal.Quotient.mk p.asIdeal), inferInstance⟩
  let e := p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  have heQ : (e Q).val = q := by
    apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk p.asIdeal)
      (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)) = q.asIdeal
    rw [Ideal.comap_map_quotientMk, sup_eq_right.mpr hpq]
  let e' : Set.Iic Q ≃o Set.Icc p q :=
    { toFun := fun r => ⟨(e r.val).val, (e r.val).property,
          by have h := e.monotone r.property; change (e r.val).val ≤ (e Q).val at h; rwa [heQ] at h⟩
      invFun := fun r => ⟨e.symm ⟨r.val, r.property.1⟩,
          by
            apply e.le_iff_le.mp
            rw [e.apply_symm_apply]
            change r.val ≤ (e Q).val
            rw [heQ]
            exact r.property.2⟩
      left_inv := fun r => Subtype.ext (e.symm_apply_apply r.val)
      right_inv := by
        intro r
        apply Subtype.ext
        change (e (e.symm ⟨r.val, r.property.1⟩)).val = r.val
        exact congrArg Subtype.val (e.apply_symm_apply _)
      map_rel_iff' := by intro r s; exact e.le_iff_le }
  exact (IsLocalization.AtPrime.primeSpectrumOrderIso _ Q.asIdeal).trans e'

theorem ringKrullDim_localizedQuotient_eq_dimensionFunction
    {A : Type u} [CommRing A]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) :
    letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hpq
    ringKrullDim (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal))) =
      ((δ p - δ q).toNat : ℕ) := by
  let : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpq
  exact (Order.krullDim_eq_of_orderIso (localizedQuotientSpectrumOrderIso p q hpq)).trans
    (krullDim_Icc_dimensionFunction δ p q hpq)

theorem bdd_dimensionFunction_of_krullDim_le
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A)) (N : ℕ)
    (hN : ringKrullDim A ≤ (N : ℕ)) :
    ∃ a b : ℤ, ∀ q, a ≤ δ q ∧ δ q ≤ b := by
  obtain ⟨a, ha⟩ := ((PrimeSpectrum.finite_setOfPred_isMin A).image δ.toFun).bddBelow
  obtain ⟨b, hb⟩ := ((PrimeSpectrum.finite_setOfPred_isMin A).image δ.toFun).bddAbove
  refine ⟨a - N, b, ?_⟩
  intro q
  obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal A) ≤ q.asIdeal)
  let p : PrimeSpectrum A := ⟨P, hP.1.1⟩
  have hp : IsMin p := PrimeSpectrum.isMin_iff.mpr hP
  have hap : a ≤ δ p := ha ⟨p, hp, rfl⟩
  have hpb : δ p ≤ b := hb ⟨p, hp, rfl⟩
  have hpq : δ q ≤ δ p := by
    by_cases h : p = q
    · simp [h]
    · exact (δ.strictAnti_specializes ((PrimeSpectrum.le_iff_specializes _ _).mp hPq) h).le
  have hd : Order.krullDim (Set.Icc p q) ≤ ringKrullDim A :=
    Order.krullDim_le_of_strictMono Subtype.val (fun _ _ h => h)
  rw [krullDim_Icc_dimensionFunction δ p q hPq] at hd
  have hd' : (δ p - δ q).toNat ≤ N := by exact_mod_cast hd.trans hN
  constructor <;> omega

end Stacks.LocalCohomology
