module

public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator.LocalizationAnnihilators
import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom

/-!
# The depth-plus-dimension criterion

Local cohomology at the closed points of the strata of a dimension function, the annihilator
criterion for a bounded-below complex with finite cohomology ([Stacks, Tag 0EHZ]), and Faltings'
annihilator theorem for a finite module ([Stacks, Tag 0EFC]).
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Stacks.Algebraization (krullDimToEInt)

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.LocalCohomology

open CategoryTheory.Limits CategoryTheory.Pretriangulated

private theorem isGE_localizedComplex
    {A : Type u} [CommRing A] (q : PrimeSpectrum A)
    (K : DerivedCategory.Plus (ModuleCat.{u} A)) (a : ℤ) [K.obj.IsGE a] :
    (localizedComplex.{u, u} q K).obj.IsGE a := by
  let F := ModuleCat.extendScalars.{u, u, u}
    (algebraMap A (Localization.AtPrime q.asIdeal))
  let : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  apply (DerivedCategory.isGE_iff _ a).mpr
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isGE K.obj a i hi)).of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso F i).app K.obj)

private theorem closedSupport_subset_localizedSupport
    {A : Type u} [CommRing A] (q : PrimeSpectrum A)
    (T : Set (PrimeSpectrum A)) (hq : q ∈ T) :
    PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _) ⊆
      PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q.asIdeal)) ⁻¹' T := by
  intro p hp
  have heq : p = closedPoint (Localization.AtPrime q.asIdeal) :=
    le_antisymm le_top hp
  subst p
  have hc : PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q.asIdeal))
      (closedPoint (Localization.AtPrime q.asIdeal)) = q :=
    PrimeSpectrum.ext (IsLocalization.AtPrime.under_maximalIdeal _ _)
  change PrimeSpectrum.comap _ _ ∈ T
  rw [hc]
  exact hq

/-- Localizing at `q` and applying derived sections preserves being bounded below by `a`. -/
private theorem isGE_derivedSections_localizedComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (q : PrimeSpectrum A) (K : DerivedCategory.Plus (ModuleCat.{u} A)) (a : ℤ) [K.obj.IsGE a] :
    ((derivedSectionsWithSupportInPlus.{u, u} (Localization.AtPrime q.asIdeal)
      (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q.asIdeal)) ⁻¹' T)).obj
        (localizedComplex.{u, u} q K)).obj.IsGE a := by
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have : (localizedComplex.{u, u} q K).obj.IsGE a := isGE_localizedComplex q K a
  have := isGE_derivedSectionsWithSupportIn (Localization.AtPrime q.asIdeal)
    (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q.asIdeal)) ⁻¹' T)
    (localizedComplex.{u, u} q K).obj a
  apply (DerivedCategory.isGE_iff _ a).mpr
  intro j hj
  exact (DerivedCategory.isZero_of_isGE _ a j hj).of_iso
    (localCohomologyPlusIso _ _ (localizedComplex.{u, u} q K) j)

/-- Annihilators of local cohomology at the closed point are unchanged by first applying derived
sections supported on the pullback of `T`. -/
private theorem annihilator_localCohomology_derivedSections_localizedComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (q : PrimeSpectrum A) (hq : q ∈ T) (K : DerivedCategory.Plus (ModuleCat.{u} A)) (i : ℤ) :
    Module.annihilator (Localization.AtPrime q.asIdeal)
      (localCohomologyWithSupportInPlus (Localization.AtPrime q.asIdeal)
        (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
        ((derivedSectionsWithSupportInPlus.{u, u} (Localization.AtPrime q.asIdeal)
          (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q.asIdeal)) ⁻¹' T)).obj
            (localizedComplex.{u, u} q K)) i) =
      Module.annihilator (Localization.AtPrime q.asIdeal)
        (localCohomologyWithSupportInPlus (Localization.AtPrime q.asIdeal)
          (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
          (localizedComplex.{u, u} q K) i) := by
  have : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  have hTq : StableUnderSpecialization
      (PrimeSpectrum.comap (algebraMap A (Localization.AtPrime q.asIdeal)) ⁻¹' T) := by
    intro p r hpr hp
    exact hT (hpr.map (PrimeSpectrum.continuous_comap _)) hp
  let e := localCohomologyPlusCompIso (Localization.AtPrime q.asIdeal)
    (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _)) _ hTq
    (localizedComplex.{u, u} q K) i
  rw [Set.inter_eq_left.mpr (closedSupport_subset_localizedSupport q T hq)] at e
  exact e.toLinearEquiv.annihilator_eq

private theorem pow_map_le_annihilator_localCohomology_closedPoint
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (a : ℤ) (n : ℕ) [K.obj.IsGE a] (J : Ideal A)
    (hJ : ∀ i : ℤ, i ≤ a + n → J ≤ Module.annihilator A
      (localCohomologyWithSupportInPlus A T K i))
    (q : PrimeSpectrum A) (hq : q ∈ T) (i : ℤ) (hi : i ≤ a + n) :
    (J.map (algebraMap A (Localization.AtPrime q.asIdeal))) ^ (n + 1) ≤
      Module.annihilator (Localization.AtPrime q.asIdeal)
        (localCohomologyWithSupportInPlus (Localization.AtPrime q.asIdeal)
          (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
          (localizedComplex.{u, u} q K) i) := by
  let B := Localization.AtPrime q.asIdeal
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing q.asIdeal.primeCompl B inferInstance
  let Z := PrimeSpectrum.zeroLocus (maximalIdeal B : Set B)
  let X := (derivedSectionsWithSupportInPlus.{u, u} B
    (PrimeSpectrum.comap (algebraMap A B) ⁻¹' T)).obj (localizedComplex.{u, u} q K)
  have : X.obj.IsGE a := isGE_derivedSections_localizedComplex T q K a
  have h := pow_le_annihilator_localCohomology_of_homology B Z X a n
    (J.map (algebraMap A B)) (fun j hj =>
      (Ideal.map_mono (hJ j hj)).trans
        (map_annihilator_le_localCohomology_localizedComplex T hT q K j)) i hi
  exact h.trans_eq (annihilator_localCohomology_derivedSections_localizedComplex T hT q hq K i)

open Module.associatedPrimes in
private theorem localized_submodule_le_sections_of_dimension
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (N : Submodule A M) (n : ℤ)
    (hN : ∀ p ∈ Module.support A N, δ p ≤ n)
    (q : PrimeSpectrum A) (hq : δ q = n) :
    N.localized' (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M) ≤
        sectionsWithSupportIn (Localization.AtPrime q.asIdeal)
          (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
          (LocalizedModule q.asIdeal.primeCompl M) := by
  let B := Localization.AtPrime q.asIdeal
  let S := q.asIdeal.primeCompl
  let f := LocalizedModule.mkLinearMap S M
  let N' := N.localized' B S f
  let Z := PrimeSpectrum.zeroLocus (maximalIdeal B : Set B)
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing S B inferInstance
  have hsupport : Module.support B N' ⊆ Z := by
    apply support_subset_of_associatedPrimes_subset N' Z
      (by
        intro p r hpr hp
        change maximalIdeal B ≤ p.asIdeal at hp
        change maximalIdeal B ≤ r.asIdeal
        exact hp.trans ((PrimeSpectrum.le_iff_specializes p r).mpr hpr))
    intro P hP
    let r : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    let p := PrimeSpectrum.comap (algebraMap A B) r
    have hpAssoc : p.asIdeal ∈ associatedPrimes A N :=
      comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
        S (N.toLocalized' B S f) P hP (Ideal.FG.of_isNoetherianRing _)
    have hpN : p ∈ Module.support A N :=
      (mem_support_iff_exists_associatedPrime_le N p).mpr ⟨p.asIdeal, hpAssoc, le_rfl⟩
    have hp : δ p ≤ n := hN p hpN
    let e := IsLocalization.AtPrime.primeSpectrumOrderIso B q.asIdeal
    have hpq : p ≤ q := (e r).property
    have hp_eq : p = q := by
      by_contra h
      have hlt := δ.strictAnti_specializes ((PrimeSpectrum.le_iff_specializes _ _).mp hpq) h
      omega
    have heq : r = closedPoint B := by
      apply e.injective
      apply Subtype.ext
      change p = PrimeSpectrum.comap (algebraMap A B) (closedPoint B)
      rw [hp_eq]
      exact (PrimeSpectrum.ext (IsLocalization.AtPrime.under_maximalIdeal B q.asIdeal)).symm
    change maximalIdeal B ≤ r.asIdeal
    rw [heq]
    exact le_rfl
  have htop := (sectionsWithSupportIn_eq_top_iff B Z N').mpr hsupport
  intro x hx
  have hmem : (⟨x, hx⟩ : N') ∈ sectionsWithSupportIn B Z N' := by
    rw [htop]
    trivial
  rw [mem_sectionsWithSupportIn_iff] at hmem ⊢
  have htor : Ideal.torsionOf B N' (⟨x, hx⟩ : N') =
      Ideal.torsionOf B (LocalizedModule S M) x := by
    ext r
    simp only [Ideal.mem_torsionOf_iff]
    exact Subtype.ext_iff
  rwa [htor] at hmem

private theorem mul_le_annihilator_localization_of_dimension
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (J : Ideal A) (n : ℤ)
    (hJ : ∀ p ∈ Module.support A ↥(J • (⊤ : Submodule A M)), δ p ≤ n)
    (q : PrimeSpectrum A) (hq : δ q = n)
    (D : Ideal (Localization.AtPrime q.asIdeal))
    (hD : D ≤ Module.annihilator (Localization.AtPrime q.asIdeal)
      (sectionsWithSupportIn (Localization.AtPrime q.asIdeal)
        (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
        (LocalizedModule q.asIdeal.primeCompl M))) :
    J.map (algebraMap A (Localization.AtPrime q.asIdeal)) * D ≤
      Module.annihilator (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) := by
  let B := Localization.AtPrime q.asIdeal
  let L := LocalizedModule q.asIdeal.primeCompl M
  let Z := PrimeSpectrum.zeroLocus (maximalIdeal B : Set B)
  have hN := localized_submodule_le_sections_of_dimension M δ (J • ⊤) n hJ q hq
  rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top] at hN
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro x
  have hax : a • x ∈ sectionsWithSupportIn B Z L :=
    hN (Submodule.smul_mem_smul ha (Submodule.mem_top))
  have hz := Module.mem_annihilator.mp (hD hb) (⟨a • x, hax⟩ : sectionsWithSupportIn B Z L)
  have hz' : b • (a • x) = 0 := congrArg Subtype.val hz
  simpa only [← mul_smul, mul_comm b a] using hz'

private theorem map_mul_pow_le_annihilator_localized_sections
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (a : ℤ) (k : ℕ) [K.obj.IsGE a] (I J : Ideal A)
    (hI : ∀ j : ℤ, j < a + k → I ≤ Module.annihilator A
      (localCohomologyWithSupportInPlus A T K j))
    (q : PrimeSpectrum A) (hq : q ∈ T)
    (hJ : J.map (algebraMap A (Localization.AtPrime q.asIdeal)) ≤
      Module.annihilator (Localization.AtPrime q.asIdeal)
        (localCohomologyWithSupportInPlus (Localization.AtPrime q.asIdeal)
          (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
          (localizedComplex.{u, u} q K) (a + k))) :
    (J * I ^ k).map (algebraMap A (Localization.AtPrime q.asIdeal)) ≤
      Module.annihilator (Localization.AtPrime q.asIdeal)
        (sectionsWithSupportIn (Localization.AtPrime q.asIdeal)
          (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
          (LocalizedModule q.asIdeal.primeCompl
            (localCohomologyWithSupportInPlus A T K (a + k)))) := by
  let B := Localization.AtPrime q.asIdeal
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing q.asIdeal.primeCompl B inferInstance
  let Z := PrimeSpectrum.zeroLocus (maximalIdeal B : Set B)
  let X := (derivedSectionsWithSupportInPlus.{u, u} B
    (PrimeSpectrum.comap (algebraMap A B) ⁻¹' T)).obj (localizedComplex.{u, u} q K)
  have : X.obj.IsGE a := isGE_derivedSections_localizedComplex T q K a
  have hJX : J.map (algebraMap A B) ≤ Module.annihilator B
      (localCohomologyWithSupportInPlus B Z X (a + (k : ℤ))) :=
    hJ.trans_eq
      (annihilator_localCohomology_derivedSections_localizedComplex T hT q hq K (a + k)).symm
  have hsections : (J * I ^ k).map (algebraMap A B) ≤ Module.annihilator B
      ((sectionsWithSupportInFunctor.{u, u} B Z).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} B) (a + k)).obj X)) := by
    rw [Ideal.map_mul, Ideal.map_pow]
    cases k with
    | zero =>
        simp only [pow_zero, mul_one]
        have : X.obj.IsGE (a + ((0 : ℕ) : ℤ)) := by
          rw [show a + ((0 : ℕ) : ℤ) = a by omega]
          infer_instance
        exact hJX.trans_eq
          (localCohomologyLowestIso B Z X (a + ((0 : ℕ) : ℤ))).toLinearEquiv.annihilator_eq
    | succ k =>
        have hlow : ∀ j : ℤ, j ≤ a + k → I.map (algebraMap A B) ≤
            Module.annihilator B
              ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} B) j).obj X) := by
          intro j hj
          exact (Ideal.map_mono (hI j (by omega))).trans
            (map_annihilator_le_localCohomology_localizedComplex T hT q K j)
        have hi : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by omega
        let eJ : localCohomologyWithSupportInPlus B Z X (a + ((k + 1 : ℕ) : ℤ)) ≅
            localCohomologyWithSupportInPlus B Z X (a + k + 1) :=
          eqToIso (congrArg (fun j => localCohomologyWithSupportInPlus B Z X j) hi)
        let eH := eqToIso (congrArg (fun j =>
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} B) j).obj X) hi.symm)
        exact (mul_pow_le_annihilator_sections_homology B Z X a k (I.map (algebraMap A B))
          (J.map (algebraMap A B)) hlow (hJX.trans_eq eJ.toLinearEquiv.annihilator_eq)).trans_eq
            ((sectionsWithSupportInFunctor.{u, u} B Z).mapIso eH).toLinearEquiv.annihilator_eq
  let eH := localCohomologyLocalizationLinearEquiv T hT q K (a + k)
  let eS := (sectionsWithSupportInFunctor.{u, u} B Z).mapIso eH.toModuleIso
  exact hsections.trans_eq eS.toLinearEquiv.annihilator_eq.symm

private theorem map_le_annihilator_iff
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Type*) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (J : Ideal A) :
    J.map (algebraMap A B) ≤ Module.annihilator B M ↔ J ≤ Module.annihilator A M := by
  rw [Ideal.map_le_iff_le_comap]
  have heq : (Module.annihilator B M).comap (algebraMap A B) = Module.annihilator A M := by
    ext a
    simp only [Ideal.mem_comap, Module.mem_annihilator, algebraMap_smul]
  rw [heq]

private theorem notMem_support_dualCohomology_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (q : PrimeSpectrum A) (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (i : ℤ) :
    q ∉ Module.support A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K.obj))) ↔
      IsZero (localCohomologyWithSupportInPlus (Localization.AtPrime q.asIdeal)
        (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
        (localizedComplex.{u, u} q K) (-Dualizing.dualizingDimension ω q - i)) := by
  rw [Module.notMem_support_iff,
    ← Module.annihilator_eq_top_iff (R := Localization.AtPrime q.asIdeal),
    annihilator_localizedDualCohomology_eq_localCohomology q K hK ω hω i,
    Module.annihilator_eq_top_iff, ModuleCat.isZero_iff_subsingleton]

private theorem localCohomology_isZero_of_global_annihilator
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T T' : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hT' : StableUnderSpecialization T')
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (a : ℤ) (n : ℕ) [K.obj.IsGE a] (J : Ideal A)
    (hJT' : PrimeSpectrum.zeroLocus (J : Set A) ⊆ T')
    (hJ : ∀ i : ℤ, i ≤ a + n → J ≤ Module.annihilator A
      (localCohomologyWithSupportInPlus A T K i))
    (p q : PrimeSpectrum A) (hp : p ∉ T') (hq : q ∈ T)
    (hpq : p.asIdeal ≤ q.asIdeal) (i : ℤ) (hi : i ≤ a + n) :
    IsZero (localCohomologyWithSupportInPlus (Localization.AtPrime p.asIdeal)
      (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime p.asIdeal) : Set _))
      (localizedComplex.{u, u} p K)
      (-Dualizing.dualizingDimension ω p + Dualizing.dualizingDimension ω q + i)) := by
  let j := -Dualizing.dualizingDimension ω q - i
  let E := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
    ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K.obj))
  have : Module.Finite A E :=
    Dualizing.dualizingDerivedHom_finiteCohomology A ω hω K.obj hK j
  have hAnn : J ^ (n + 1) ≤ Module.annihilator A (LocalizedModule q.asIdeal.primeCompl E) := by
    rw [← map_le_annihilator_iff (B := Localization.AtPrime q.asIdeal), Ideal.map_pow]
    change (J.map (algebraMap A (Localization.AtPrime q.asIdeal))) ^ (n + 1) ≤ _
    rw [annihilator_localizedDualCohomology_eq_localCohomology q K hK ω hω j]
    have heq : -Dualizing.dualizingDimension ω q - j = i := by dsimp [j]; omega
    rw [heq]
    exact pow_map_le_annihilator_localCohomology_closedPoint T hT K a n J hJ q hq i hi
  have hzero : p ∉ Module.support A E := by
    intro hsupport
    apply hp
    apply (exists_annihilator_localization_iff E q T' hT').mp
      ⟨J ^ (n + 1), ?_, hAnn⟩ p hpq hsupport
    rwa [PrimeSpectrum.zeroLocus_pow _ (Nat.succ_ne_zero _)]
  have hz := (notMem_support_dualCohomology_iff p K hK ω hω j).mp hzero
  convert hz using 2
  dsimp [j]
  omega

private theorem exists_annihilator_localCohomology_dimension_stratum
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T T' : Set (PrimeSpectrum A)) (hT' : StableUnderSpecialization T')
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (s : ℤ)
    (hdepth : ∀ p q : PrimeSpectrum A, p ∉ T' → q ∈ T → p.asIdeal ≤ q.asIdeal →
      ((s - Dualizing.dualizingDimension ω p + Dualizing.dualizingDimension ω q : ℤ) : EInt) <
        DerivedCategory.Plus.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal)) (localizedComplex.{u, u} p K))
    (n i : ℤ) (hi : i ≤ s) :
    ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      ∀ q ∈ T, Dualizing.dualizingDimension ω q = n →
        J.map (algebraMap A (Localization.AtPrime q.asIdeal)) ≤
          Module.annihilator (Localization.AtPrime q.asIdeal)
            (localCohomologyWithSupportInPlus (Localization.AtPrime q.asIdeal)
              (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
              (localizedComplex.{u, u} q K) i) := by
  let j := -n - i
  let E := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
    ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K.obj))
  have : Module.Finite A E :=
    Dualizing.dualizingDerivedHom_finiteCohomology A ω hω K.obj hK j
  have hsupport : ∀ q ∈ {q ∈ T | Dualizing.dualizingDimension ω q = n},
      ∀ p : PrimeSpectrum A, p.asIdeal ≤ q.asIdeal → p ∈ Module.support A E → p ∈ T' := by
    intro q hq p hpq hpE
    by_contra hp
    have hd := hdepth p q hp hq.1 hpq
    have hz := localCohomology_isZero_of_lt_depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal)) (localizedComplex.{u, u} p K)
      (-Dualizing.dualizingDimension ω p - j) (lt_of_le_of_lt ?_ hd)
    · exact ((notMem_support_dualCohomology_iff p K hK ω hω j).mpr hz) hpE
    · apply WithBotTop.coe_le_coe.mpr
      dsimp [j]
      rw [hq.2]
      omega
  obtain ⟨J, hJT', hJE⟩ := (exists_uniform_annihilator_localization_iff E
    {q ∈ T | Dualizing.dualizingDimension ω q = n} T' hT').mpr hsupport
  refine ⟨J, hJT', ?_⟩
  intro q hq hn
  have h := (map_le_annihilator_iff (B := Localization.AtPrime q.asIdeal)
    (LocalizedModule q.asIdeal.primeCompl E) J).mpr (hJE q ⟨hq, hn⟩)
  rw [annihilator_localizedDualCohomology_eq_localCohomology q K hK ω hω j] at h
  have heq : -Dualizing.dualizingDimension ω q - j = i := by dsimp [j]; omega
  rwa [heq] at h

private theorem eint_lt_add_iff (d : WithTop ℤ) (s c : ℤ) :
    (s : EInt) < (d : EInt) + (c : EInt) ↔ ((s - c : ℤ) : EInt) < (d : EInt) := by
  cases d using WithTop.recTopCoe with
  | top =>
      change (WithBot.some (s : WithTop ℤ) : EInt) < WithBot.some (⊤ + (c : WithTop ℤ)) ↔
        (WithBot.some ((s - c : ℤ) : WithTop ℤ) : EInt) < WithBot.some ⊤
      simp only [WithBot.coe_lt_coe, top_add, WithTop.coe_lt_top]
  | coe d =>
      change (s : EInt) < ((d + c : ℤ) : EInt) ↔ ((s - c : ℤ) : EInt) < (d : EInt)
      simp only [WithBotTop.coe_lt_coe]
      omega

/-- The depth-plus-dimension inequality for `p ≤ q` rewritten with the dualizing dimension
shift. -/
private theorem depth_add_dim_gt_iff_shift_lt_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (s : ℤ) (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal) :
    letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hpq
    ((DerivedCategory.Plus.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal)) (localizedComplex.{u, u} p K) : EInt) +
      krullDimToEInt
        (ringKrullDim (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))) >
      (s : EInt)) ↔
    ((s - Dualizing.dualizingDimension ω p + Dualizing.dualizingDimension ω q : ℤ) : EInt) <
      DerivedCategory.Plus.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal)) (localizedComplex.{u, u} p K) := by
  let : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpq
  obtain ⟨δ, hδ⟩ : ∃ δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A),
      ∀ p, δ p = Dualizing.dualizingDimension ω p :=
    ⟨Dualizing.dualizingDimensionFunction ω hω,
      Dualizing.dualizingDimensionFunction_apply ω hω⟩
  have hδpq : δ q ≤ δ p := by
    by_cases heq : p = q
    · simp [heq]
    · exact (δ.strictAnti_specializes ((PrimeSpectrum.le_iff_specializes _ _).mp hpq) heq).le
  rw [ringKrullDim_localizedQuotient_eq_dimensionFunction δ p q hpq]
  change (s : EInt) < _ + (((δ p - δ q).toNat : ℤ) : EInt) ↔ _
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hδpq), eint_lt_add_iff, ← hδ p, ← hδ q,
    sub_sub_eq_add_sub, sub_add_eq_add_sub]

private theorem depth_add_dim_gt_of_annihilator_sameUniverse
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T T' : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hT' : StableUnderSpecialization T')
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (s : ℤ) (J : Ideal A) (hJT' : PrimeSpectrum.zeroLocus (J : Set A) ⊆ T')
    (hJ : ∀ i : ℤ, i ≤ s → J ≤ Module.annihilator A
      (localCohomologyWithSupportInPlus A T K i))
    (p q : PrimeSpectrum A) (hp : p ∉ T') (hq : q ∈ T)
    (hpq : p.asIdeal ≤ q.asIdeal) :
    letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hpq
    (DerivedCategory.Plus.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal)) (localizedComplex.{u, u} p K) : EInt) +
      krullDimToEInt
        (ringKrullDim (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))) >
      (s : EInt) := by
  rw [depth_add_dim_gt_iff_shift_lt_depth ω hω s K p q hpq]
  apply depth_gt_of_localCohomology_isZero
  intro i hi
  obtain ⟨b, hb⟩ := K.property
  let a := min b s
  have : K.obj.IsGE b := hb
  have : K.obj.IsGE a := DerivedCategory.TStructure.t.isGE_of_ge K.obj a b (min_le_left _ _)
  let n := (s - a).toNat
  have hn : a + (n : ℤ) = s := by dsimp [n, a]; omega
  have hz := localCohomology_isZero_of_global_annihilator T T' hT hT' K hK ω hω a n J hJT'
    (by simpa only [hn] using hJ) p q hp hq hpq
    (i + Dualizing.dualizingDimension ω p - Dualizing.dualizingDimension ω q) (by omega)
  convert hz using 2
  omega

private theorem support_smul_subset_of_le
    {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    {I J : Ideal A} (hIJ : I ≤ J) :
    Module.support A ↥(I • (⊤ : Submodule A M)) ⊆
      Module.support A ↥(J • (⊤ : Submodule A M)) :=
  Module.support_subset_of_injective
    (Submodule.inclusion (Submodule.smul_mono_left hIJ))
    (Submodule.inclusion_injective _)

private theorem zeroLocus_pow_subset {A : Type u} [CommRing A]
    (I : Ideal A) (k : ℕ) :
    PrimeSpectrum.zeroLocus ((I ^ k : Ideal A) : Set A) ⊆ PrimeSpectrum.zeroLocus (I : Set A) := by
  cases k with
  | zero => simp
  | succ k => rw [PrimeSpectrum.zeroLocus_pow I (Nat.succ_ne_zero k)]

private theorem exists_annihilator_degree_of_local_strata
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T T' : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (l b : ℤ) (hδ : ∀ p, l ≤ δ p ∧ δ p ≤ b)
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (a : ℤ) (k : ℕ) [K.obj.IsGE a] (I : Ideal A)
    (hIT' : PrimeSpectrum.zeroLocus (I : Set A) ⊆ T')
    (hI : ∀ j : ℤ, j < a + k → I ≤ Module.annihilator A
      (localCohomologyWithSupportInPlus A T K j))
    (hloc : ∀ n : ℤ, ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      ∀ q ∈ T, δ q = n → J.map (algebraMap A (Localization.AtPrime q.asIdeal)) ≤
        Module.annihilator (Localization.AtPrime q.asIdeal)
          (localCohomologyWithSupportInPlus (Localization.AtPrime q.asIdeal)
            (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
            (localizedComplex.{u, u} q K) (a + k))) :
    ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      J ≤ Module.annihilator A (localCohomologyWithSupportInPlus A T K (a + k)) := by
  let M := localCohomologyWithSupportInPlus A T K (a + k)
  have hMT := support_localCohomologyPlus_subset T K (a + k)
  have hdesc : ∀ t : ℕ, ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      ∀ q ∈ Module.support A ↥(J • (⊤ : Submodule A M)), δ q ≤ b - t := by
    intro t
    induction t with
    | zero => exact ⟨⊤, by simp, fun q _ => by simpa using (hδ q).2⟩
    | succ t ih =>
        obtain ⟨J, hJT', hJ⟩ := ih
        obtain ⟨L, hLT', hL⟩ := hloc (b - t)
        refine ⟨J * (L * I ^ k), ?_, ?_⟩
        · rw [PrimeSpectrum.zeroLocus_mul, PrimeSpectrum.zeroLocus_mul]
          exact Set.union_subset hJT'
            (Set.union_subset hLT' ((zeroLocus_pow_subset I k).trans hIT'))
        · intro q hq
          have hqJ := support_smul_subset_of_le M (Ideal.mul_le_left : J * (L * I ^ k) ≤ J) hq
          have hqn := hJ q hqJ
          by_contra hn
          have heq : δ q = b - t := by omega
          have hqT : q ∈ T := hMT ((Module.support_subset_of_injective
            ((J * (L * I ^ k)) • (⊤ : Submodule A M)).subtype Subtype.val_injective) hq)
          have hD := map_mul_pow_le_annihilator_localized_sections T hT K a k I L hI q hqT
            (hL q hqT heq)
          have hann := mul_le_annihilator_localization_of_dimension M δ J (b - t) hJ q heq
            ((L * I ^ k).map (algebraMap A (Localization.AtPrime q.asIdeal))) hD
          rw [← Ideal.map_mul, map_le_annihilator_iff] at hann
          exact (annihilator_localization_iff_notMem_support_smul M (J * (L * I ^ k)) q).mp hann hq
  obtain ⟨J, hJT', hJ⟩ := hdesc (b - l + 1).toNat
  refine ⟨J, hJT', ?_⟩
  have hzero : Module.support A ↥(J • (⊤ : Submodule A M)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have h₁ := hJ q hq
    have h₂ := (hδ q).1
    omega
  have hsub := Module.support_eq_empty_iff.mp hzero
  have hbot := (Submodule.subsingleton_iff_eq_bot (p := J • (⊤ : Submodule A M))).mp hsub
  rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top] at hbot
  exact hbot

private theorem exists_annihilator_of_local_strata
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T T' : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (l b : ℤ) (hδ : ∀ p, l ≤ δ p ∧ δ p ≤ b)
    (K : DerivedCategory.Plus (ModuleCat.{u} A)) (s : ℤ)
    (hloc : ∀ n i : ℤ, i ≤ s →
      ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
        ∀ q ∈ T, δ q = n → J.map (algebraMap A (Localization.AtPrime q.asIdeal)) ≤
          Module.annihilator (Localization.AtPrime q.asIdeal)
            (localCohomologyWithSupportInPlus (Localization.AtPrime q.asIdeal)
              (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
              (localizedComplex.{u, u} q K) i)) :
    ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      ∀ i : ℤ, i ≤ s → J ≤ Module.annihilator A
        (localCohomologyWithSupportInPlus A T K i) := by
  obtain ⟨a₀, ha₀⟩ := K.property
  let a := min a₀ s
  have : K.obj.IsGE a₀ := ha₀
  have : K.obj.IsGE a := DerivedCategory.TStructure.t.isGE_of_ge K.obj a a₀ (min_le_left _ _)
  have hdegrees : ∀ k : ℕ, a + k ≤ s + 1 →
      ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
        ∀ i : ℤ, i < a + k → J ≤ Module.annihilator A
          (localCohomologyWithSupportInPlus A T K i) := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨⊤, by simp, ?_⟩
        intro i hi
        have := isGE_derivedSectionsWithSupportIn A T K.obj a
        have hz := (DerivedCategory.isZero_of_isGE
          ((derivedSectionsWithSupportIn.{u, u} A T).obj K.obj) a i (by simpa using hi)).of_iso
          (localCohomologyPlusIso A T K i)
        have := ModuleCat.isZero_iff_subsingleton.mp hz
        exact fun r _ => Module.mem_annihilator.mpr fun x => Subsingleton.elim _ _
    | succ k ih =>
        intro hk
        obtain ⟨I, hIT', hI⟩ := ih (by omega)
        obtain ⟨J, hJT', hJ⟩ := exists_annihilator_degree_of_local_strata T T' hT δ l b hδ K a k I
          hIT' hI (fun n => hloc n (a + k) (by omega))
        refine ⟨I ⊓ J, ?_, ?_⟩
        · rw [PrimeSpectrum.zeroLocus_inf]
          exact Set.union_subset hIT' hJT'
        · intro i hi
          by_cases h : i < a + k
          · exact inf_le_left.trans (hI i h)
          · have heq : i = a + k := by omega
            subst i
            exact inf_le_right.trans hJ
  obtain ⟨J, hJT', hJ⟩ := hdegrees ((s - a).toNat + 1) (by dsimp [a]; omega)
  exact ⟨J, hJT', fun i hi => hJ i (by dsimp [a]; omega)⟩

private theorem annihilator_iff_depth_sameUniverse
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (T T' : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hT' : StableUnderSpecialization T')
    (s : ℤ) (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      ∀ i : ℤ, i ≤ s → J ≤ Module.annihilator A (localCohomologyWithSupportInPlus A T K i)) ↔
    (∀ p q : PrimeSpectrum A, p ∉ T' → q ∈ T → (hpq : p.asIdeal ≤ q.asIdeal) →
      letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
        Ideal.isPrime_map_quotientMk_of_isPrime hpq
      ((DerivedCategory.Plus.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal)) (localizedComplex.{u, u} p K) : EInt) +
        krullDimToEInt
          (ringKrullDim (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))) >
        (s : EInt))) := by
  refine ⟨fun ⟨J, hJT', hJ⟩ =>
    depth_add_dim_gt_of_annihilator_sameUniverse T T' hT hT' K hK ω hω s J hJT' hJ, ?_⟩
  · intro hdepth
    obtain ⟨δ, hδ⟩ : ∃ δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A),
      ∀ p, δ p = Dualizing.dualizingDimension ω p :=
    ⟨Dualizing.dualizingDimensionFunction ω hω,
      Dualizing.dualizingDimensionFunction_apply ω hω⟩
    have hdim := Dualizing.ringKrullDim_lt_top_of_isDualizingComplex hω
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ringKrullDim A ≤ (N : ℕ) := by
      by_cases he : ringKrullDim A = ⊥
      · exact ⟨0, he ▸ bot_le⟩
      obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp he
      have hdtop : d ≠ ⊤ := by
        intro h
        rw [← hd, h] at hdim
        exact lt_irrefl _ hdim
      obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hdtop
      exact ⟨N, by rw [← hd, ← hN]; rfl⟩
    obtain ⟨l, b, hbound⟩ := bdd_dimensionFunction_of_krullDim_le δ N hN
    have hshift : ∀ p q : PrimeSpectrum A, p ∉ T' → q ∈ T → p.asIdeal ≤ q.asIdeal →
        ((s - Dualizing.dualizingDimension ω p + Dualizing.dualizingDimension ω q : ℤ) : EInt) <
          DerivedCategory.Plus.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal)) (localizedComplex.{u, u} p K) := by
      intro p q hp hq hpq
      exact (depth_add_dim_gt_iff_shift_lt_depth ω hω s K p q hpq).mp (hdepth p q hp hq hpq)
    apply exists_annihilator_of_local_strata T T' hT δ l b hbound K s
    intro n i hi
    obtain ⟨J, hJT', hJ⟩ := exists_annihilator_localCohomology_dimension_stratum T T' hT' K hK ω
      hω s hshift n i hi
    exact ⟨J, hJT', fun q hq hn => hJ q hq ((hδ q).symm.trans hn)⟩

/-- Uniform annihilation of low local cohomology is equivalent to the
depth–dimension inequality along all relevant chains of primes. -/
@[stacks 0EHZ]
public theorem exists_annihilator_localCohomology_iff_depth_add_dim
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (omega : DerivedCategory (ModuleCat.{u} A))
    (_homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (T T' : Set (PrimeSpectrum A)) (_hTT' : T ⊆ T')
    (_hT : StableUnderSpecialization T)
    (_hT' : StableUnderSpecialization T')
    (s : ℤ) (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (_hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
      ∀ i : ℤ, i ≤ s → J ≤ Module.annihilator A
        (localCohomologyWithSupportInPlus
          A T K i)) ↔
    (∀ p q : PrimeSpectrum A, p ∉ T' → q ∈ T → (hpq : p.asIdeal ≤ q.asIdeal) →
      letI : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
        Ideal.isPrime_map_quotientMk_of_isPrime hpq
      ((DerivedCategory.Plus.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (localizedComplex p K) : EInt) +
        krullDimToEInt
          (ringKrullDim (Localization.AtPrime
            (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)))) > (s : EInt))) :=
  annihilator_iff_depth_sameUniverse omega _homega T T' _hT _hT' s K _hK

/-! ### Faltings' annihilator theorem -/

/-- **Stacks 0EHZ.** The annihilator criterion for a bounded-below complex with finite
cohomology over a Noetherian ring admitting a dualizing complex, in the predicate form in
which this library states it. -/
@[stacks 0EHZ "the criterion, in predicate form"]
public theorem annihilatorDepthCriterionPlus (A : Type u) [CommRing A] [IsNoetherianRing A] :
    AnnihilatorDepthCriterionPlus.{u, u, u} A :=
  fun omega homega T T' hTT' hT hT' s K hK ↦
    exists_annihilator_localCohomology_iff_depth_add_dim A omega homega T T' hTT' hT hT' s K hK

/-- **Stacks 0EFC, Faltings' annihilator theorem.** For a finite module `M` over a Noetherian
ring with a dualizing complex and nested specialization-closed subsets `T ⊆ T'`, an ideal
supported in `T'` annihilates `H^i_T(M)` for every `i ≤ s` exactly when
`depth_{A_p}(M_p) + dim((A/p)_q) > s` for every `p ∉ T'` and `q ∈ T` with `p ⊆ q`. -/
@[stacks 0EFC]
public theorem exists_ideal_le_annihilator_localCohomology_iff
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T T' : Set (PrimeSpectrum A)) (hTT' : T ⊆ T')
    (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    (s : ℤ) (hs : 0 ≤ s)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega)) :
    (∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T' ∧
        ∀ i : ℤ, i ≤ s → J ≤ Module.annihilator A
          (localCohomologyWithSupportIn.{u, u} A T
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A M)) i)) ↔
      (∀ p q : PrimeSpectrum A, p ∉ T' → q ∈ T → p.asIdeal ≤ q.asIdeal →
        Stacks.Algebraization.enatToEInt
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M)) +
          krullDimToEInt
            (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
              p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > (s : EInt)) :=
  annihilatorDepthCriterion_of_annihilatorDepthCriterionPlus.{u, u, u} A
    (annihilatorDepthCriterionPlus.{u} A) M T T' hTT' hT hT' s hs omega homega

end Stacks.LocalCohomology
