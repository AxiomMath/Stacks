module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Basic
public import StacksFrontier.AlgebraicGeometry.SemilocalFibre.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition
public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.Away
import StacksFrontier.RingTheory.Length.SemiLocal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.Defs
import all StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.Defs

/-!
# Preparing nonzerodivisors for the tame symbol: finite modifications and glueing

This file collects the steps of the construction in
`StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.Construction` that move
preparations between finite modifications: composites of finite modifications whose cokernels are
killed by a power of the maximal ideal, the finite extension in which two nonzerodivisors become
comparable at every maximal ideal, and the glueing of local preparations at the finitely many
maximal ideals of a finite modification into one preparation.

## Main results

* `AlgebraicGeometry.annihilated_quotient_trans_of_local_finite_extensions`: a composite of two
  finite modifications of local rings whose cokernels are killed by powers of the maximal ideals
  again has this property.

The private lemmas used by the construction provide, from the input
`AlgebraicGeometry.FiniteExtensionPreparingTwoNonzerodivisors`, a finite extension in which, at
every maximal ideal, one of two nonzerodivisors divides the other; glue, from the input
`AlgebraicGeometry.RingHomGluingAtMaximalIdeals`, preparations at the maximal ideals of a finite
modification to a preparation over the base; and prepare a pair `x, y` with `y = x ^ m * c` for a
unit `c` in a finite local modification.

## References

* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace AlgebraicGeometry

private theorem isUnit_or_isUnit_of_span_pair_eq_top
    {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (h : Ideal.span ({a, b} : Set R) = ⊤) : IsUnit a ∨ IsUnit b := by
  by_contra hn
  push Not at hn
  have ha : a ∈ maximalIdeal R := by
    by_contra hna
    exact hn.1 (notMem_maximalIdeal.mp hna)
  have hb : b ∈ maximalIdeal R := by
    by_contra hnb
    exact hn.2 (notMem_maximalIdeal.mp hnb)
  have hle : Ideal.span ({a, b} : Set R) ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have htop : (⊤ : Ideal R) ≤ maximalIdeal R := by simpa only [h] using hle
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp htop)

private theorem comparable_of_common_factor_and_comaximal
    {R : Type*} [CommRing R] [IsLocalRing R]
    {a b t a' b' : R} (ha : a = t * a') (hb : b = t * b')
    (h : Ideal.span ({a', b'} : Set R) = ⊤) : a ∣ b ∨ b ∣ a := by
  rcases isUnit_or_isUnit_of_span_pair_eq_top h with hu | hu
  · left
    refine ⟨(↑(hu.unit)⁻¹ : R) * b', ?_⟩
    rw [hb, ha]
    calc
      t * b' = t * ((hu.unit : R) * ↑hu.unit⁻¹) * b' := by simp
      _ = t * a' * (↑hu.unit⁻¹ * b') := by rw [hu.unit_spec]; ring
  · right
    refine ⟨(↑(hu.unit)⁻¹ : R) * a', ?_⟩
    rw [ha, hb]
    calc
      t * a' = t * ((hu.unit : R) * ↑hu.unit⁻¹) * a' := by simp
      _ = t * b' * (↑hu.unit⁻¹ * a') := by rw [hu.unit_spec]; ring

private theorem span_pair_map_eq_top
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {a b : R} (h : Ideal.span ({a, b} : Set R) = ⊤) :
    Ideal.span ({f a, f b} : Set S) = ⊤ := by
  have hm := congrArg (Ideal.map f) h
  simpa only [Ideal.map_span, Ideal.map_top, Set.image_insert_eq,
    Set.image_singleton] using hm

private theorem annihilator_power_to_smul_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (n : ℕ)
    (h : I ^ n ≤ Module.annihilator R
      (S ⧸ (Algebra.linearMap R S).range)) :
    I ^ n • (⊤ : Submodule R S) ≤
      LinearMap.range (Algebra.linearMap R S) := by
  rw [Submodule.smul_le]
  intro a ha b _
  have hz := (Module.mem_annihilator.mp (h ha))
    (Submodule.Quotient.mk b : S ⧸ (Algebra.linearMap R S).range)
  exact (Submodule.Quotient.mk_eq_zero _).mp (by
    simpa only [Submodule.Quotient.mk_smul] using hz)

private theorem exists_finite_extension_pair_locally_comparable
    (h02Q7 : FiniteExtensionPreparingTwoNonzerodivisors.{u})
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim : ringKrullDim A = 1) (a b : A)
    (ha : IsRegular a) (hb : IsRegular b)
    (ham : a ∈ maximalIdeal A) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧
      (∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
        LinearMap.range (Algebra.linearMap A B)) ∧
      IsRegular (algebraMap A B a) ∧ IsRegular (algebraMap A B b) ∧
      ∀ (q : Ideal B) [q.IsMaximal],
        ringKrullDim (Localization.AtPrime q) = 1 ∧
          (algebraMap B (Localization.AtPrime q) (algebraMap A B a) ∣
            algebraMap B (Localization.AtPrime q) (algebraMap A B b) ∨
          algebraMap B (Localization.AtPrime q) (algebraMap A B b) ∣
            algebraMap B (Localization.AtPrime q) (algebraMap A B a)) := by
  obtain ⟨B, instB, algB, hfin, hinj, hann, t, a', b', ht, ha', hb', hta, htb, hspan⟩ :=
    h02Q7 A hdim a b
      (ha.mem_nonZeroDivisors) (hb.mem_nonZeroDivisors)
  let _ : CommRing B := instB
  let _ : Algebra A B := algB
  have hreg {c : A} {c' : B} (hc : algebraMap A B c = t * c') (hc' : c' ∈ nonZeroDivisors B) :
      IsRegular (algebraMap A B c) := by
    rw [hc]
    exact isRegular_mul_iff.mpr
      ⟨isRegular_iff_mem_nonZeroDivisors.mpr ht, isRegular_iff_mem_nonZeroDivisors.mpr hc'⟩
  refine ⟨B, instB, algB, hfin, hinj, ?_, hreg hta ha', hreg htb hb', ?_⟩
  · obtain ⟨n, hn⟩ := hann
    exact ⟨n, annihilator_power_to_smul_top (maximalIdeal A) n hn⟩
  · intro q hq
    let R := Localization.AtPrime q
    let f : B →+* R := algebraMap B R
    have hta' : f (algebraMap A B a) = f t * f a' := by rw [hta, map_mul]
    have htb' : f (algebraMap A B b) = f t * f b' := by rw [htb, map_mul]
    constructor
    · exact local_dimension_one_of_integral hdim ham (hreg hta ha') q
    · exact comparable_of_common_factor_and_comaximal hta' htb'
        (span_pair_map_eq_top f hspan)

private theorem smul_top_to_cokernel_power
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R)
    (h : ∃ n : ℕ, I ^ n • (⊤ : Submodule R S) ≤
      LinearMap.range (Algebra.linearMap R S)) :
    Stacks.RingHomGluing.CokernelIsKilledByIdealPower (algebraMap R S) I := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  intro a ha y
  obtain ⟨x, hx⟩ := (Submodule.smul_le.mp hn) a ha y (by simp)
  exact ⟨x, by simpa [Algebra.linearMap_apply, Algebra.smul_def] using hx⟩

private theorem exists_finite_gluing_at_maximal_ideals
    (h0EAE : RingHomGluingAtMaximalIdeals.{u})
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [Finite (MaximalSpectrum A)]
    (B : MaximalSpectrum A → Type u) [∀ q, CommRing (B q)]
    (f : ∀ q, Localization.AtPrime q.asIdeal →+* B q)
    (hfin : ∀ q, (f q).Finite)
    (hinj : ∀ q, Function.Injective (f q))
    (hcoker : ∀ q,
      Stacks.RingHomGluing.CokernelIsKilledByIdealPower (f q)
        (q.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) :
    ∃ (C : Type u) (_ : CommRing C) (g : A →+* C),
      g.Finite ∧ Function.Injective g ∧
      Stacks.RingHomGluing.CokernelIsKilledByIdealPower g
        (⨅ q : MaximalSpectrum A, q.asIdeal) ∧
      ∀ q, ∃ gq : C →+* B q,
        gq.comp g = (f q).comp (algebraMap A (Localization.AtPrime q.asIdeal)) ∧
        (Submonoid.map g q.asIdeal.primeCompl).IsLocalizationMap gq := by
  let : ∀ q : MaximalSpectrum A, q.asIdeal.IsMaximal := fun q => q.isMaximal
  have hpair : Pairwise (fun i j : MaximalSpectrum A => i.asIdeal ≠ j.asIdeal) := by
    intro i j hij heq
    exact hij (MaximalSpectrum.ext heq)
  have hker (q : MaximalSpectrum A) :
      Stacks.RingHomGluing.KernelIsKilledByIdealPower (f q)
        (q.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) := by
    refine ⟨0, ?_⟩
    intro a ha x hx
    have hx0 : x = 0 := hinj q (by simpa using hx)
    simp [hx0]
  obtain ⟨C, instC, g, hgq, hkg, hcg, hfg, hig, _⟩ :=
    h0EAE
      (fun q : MaximalSpectrum A => q.asIdeal) B hpair f hker hcoker
  exact ⟨C, instC, g, hfg hfin, hig hinj, hcg, hgq⟩

private theorem annihilated_quotient_trans
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (I : Ideal A) (n k : ℕ)
    (hAB : I ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (hBC : ∀ b ∈ I ^ k, ∀ c : C,
      ∃ d : B, b • c = algebraMap B C d) :
    I ^ (n + k) • (⊤ : Submodule A C) ≤
      LinearMap.range (Algebra.linearMap A C) := by
  rw [Submodule.smul_le]
  intro x hx c _
  rw [pow_add] at hx
  apply Submodule.mul_induction_on
    (C := fun x : A => x • c ∈ LinearMap.range (Algebra.linearMap A C)) hx
  · intro a ha b hb
    obtain ⟨d, hd⟩ := hBC b hb c
    have had : a • d ∈ LinearMap.range (Algebra.linearMap A B) :=
      (Submodule.smul_le.mp hAB) a ha d (by simp)
    obtain ⟨z, hz⟩ := had
    refine ⟨z, ?_⟩
    show algebraMap A C z = (a * b) • c
    rw [IsScalarTower.algebraMap_apply A B C z]
    show algebraMap B C ((Algebra.linearMap A B) z) = (a * b) • c
    rw [hz, mul_smul, hd]
    simp only [Algebra.smul_def, map_mul]
    rw [← IsScalarTower.algebraMap_apply A B C a]
  · intro a b ha hb
    rw [add_smul]
    exact Submodule.add_mem _ ha hb

private theorem cokernel_power_over_mapped_ideal
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (I : Ideal A) (J : Ideal B)
    (hIJ : Ideal.map (algebraMap A B) I ≤ J)
    (h : Stacks.RingHomGluing.CokernelIsKilledByIdealPower
      (algebraMap B C) J) :
    ∃ k : ℕ, ∀ a ∈ I ^ k, ∀ c : C,
      ∃ b : B, a • c = algebraMap B C b := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  intro a ha c
  have hmap : algebraMap A B a ∈ J ^ k := by
    apply Ideal.pow_right_mono hIJ k
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem (algebraMap A B) ha
  obtain ⟨b, hb⟩ := hk (algebraMap A B a) hmap c
  refine ⟨b, ?_⟩
  rw [hb, Algebra.smul_def, IsScalarTower.algebraMap_apply A B C a]

private theorem annihilated_quotient_trans_of_jacobson
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [Module.Finite A B]
    (hAB : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B))
    (hBC : Stacks.RingHomGluing.CokernelIsKilledByIdealPower
      (algebraMap B C) (⨅ q : MaximalSpectrum B, q.asIdeal)) :
    ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A C) ≤
      LinearMap.range (Algebra.linearMap A C) := by
  have hIJ : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
      ⨅ q : MaximalSpectrum B, q.asIdeal := by
    refine le_iInf fun q => ?_
    apply Ideal.map_le_iff_le_comap.mpr
    have hmax : ((q.asIdeal).under A).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q.asIdeal
    show maximalIdeal A ≤ (q.asIdeal).under A
    rw [eq_maximalIdeal hmax]
  obtain ⟨n, hn⟩ := hAB
  obtain ⟨k, hk⟩ :=
    cokernel_power_over_mapped_ideal (maximalIdeal A)
      (⨅ q : MaximalSpectrum B, q.asIdeal) hIJ hBC
  exact ⟨n + k, annihilated_quotient_trans (maximalIdeal A) n k hn hk⟩

theorem annihilated_quotient_trans_of_local_finite_extensions
    {A S T : Type*} [CommRing A] [IsLocalRing A]
    [CommRing S] [IsLocalRing S] [CommRing T]
    [Algebra A S] [Algebra S T] [Algebra A T] [IsScalarTower A S T]
    (hlocal : IsLocalHom (algebraMap A S))
    (hAS : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S))
    (hST : ∃ k : ℕ, maximalIdeal S ^ k • (⊤ : Submodule S T) ≤
      LinearMap.range (Algebra.linearMap S T)) :
    ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A T) ≤
      LinearMap.range (Algebra.linearMap A T) := by
  let : IsLocalHom (algebraMap A S) := hlocal
  have hmap : Ideal.map (algebraMap A S) (maximalIdeal A) ≤ maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_le (algebraMap A S)
  obtain ⟨n, hn⟩ := hAS
  obtain ⟨k, hk⟩ := cokernel_power_over_mapped_ideal
    (maximalIdeal A) (maximalIdeal S) hmap
      (smul_top_to_cokernel_power (maximalIdeal S) hST)
  exact ⟨n + k, annihilated_quotient_trans (maximalIdeal A) n k hn hk⟩

private theorem regular_of_ringEquiv_symm
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {x : S} (hx : IsRegular x) : IsRegular (e.symm x) := by
  constructor
  · intro a b hab
    apply e.injective
    apply hx.left
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hab
  · intro a b hab
    apply e.injective
    apply hx.right
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hab

private theorem maximal_image_of_isLocalizationMap
    {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (M : Submonoid R) (hg : M.IsLocalizationMap g)
    (p : Ideal R) [p.IsMaximal]
    (hdisj : Disjoint (M : Set R) (p : Set R)) :
    (p.map g).IsMaximal ∧ (p.map g).comap g = p := by
  let : Algebra R S := g.toAlgebra
  let : IsLocalization M S :=
    (isLocalization_iff_isLocalizationMap M S).mpr hg
  exact ⟨IsLocalization.isMaximal_of_isMaximal_disjoint M S p hdisj,
    IsLocalization.under_map_of_isPrime_disjoint M S
      (inferInstance : p.IsPrime) hdisj⟩

private theorem disjoint_map_primeCompl_of_comap
    {A C : Type*} [CommRing A] [CommRing C]
    (g : A →+* C) (q : Ideal A) [q.IsPrime]
    (p : Ideal C) (hp : p.comap g = q) :
    Disjoint (Submonoid.map g q.primeCompl : Set C) (p : Set C) := by
  apply Set.disjoint_left.mpr
  intro x hxM hxp
  obtain ⟨s, hs, rfl⟩ := hxM
  have hsnot : s ∉ q := hs
  exact hsnot (hp ▸ hxp)

private theorem exists_localRingEquiv_of_isLocalizationMap_at_maximal
    {A C D : Type*} [CommRing A] [CommRing C] [CommRing D]
    (g : A →+* C) (q : Ideal A) [q.IsPrime]
    (p : Ideal C) [p.IsMaximal] (hp : p.comap g = q)
    (f : C →+* D)
    (hf : (Submonoid.map g q.primeCompl).IsLocalizationMap f) :
    ∃ qD : MaximalSpectrum D, qD.asIdeal.comap f = p ∧
      ∃ e : Localization.AtPrime p ≃+* Localization.AtPrime qD.asIdeal,
        ∀ c : C, e (algebraMap C (Localization.AtPrime p) c) =
          algebraMap D (Localization.AtPrime qD.asIdeal) (f c) := by
  let M := Submonoid.map g q.primeCompl
  have hdisj : Disjoint (M : Set C) (p : Set C) :=
    disjoint_map_primeCompl_of_comap g q p hp
  obtain ⟨hmax, hcomap⟩ := maximal_image_of_isLocalizationMap f M hf p hdisj
  let : (p.map f).IsMaximal := hmax
  refine ⟨⟨p.map f, hmax⟩, hcomap, ?_⟩
  let : Algebra C D := f.toAlgebra
  let : IsLocalization M D :=
    (isLocalization_iff_isLocalizationMap M D).mpr hf
  let : IsScalarTower C D (Localization.AtPrime (p.map f)) := inferInstance
  let : IsLocalization.AtPrime (Localization.AtPrime (p.map f)) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := M) (T := Localization.AtPrime (p.map f)) (p.map f) using 1
    exact hcomap.symm
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (Localization.AtPrime (p.map f))
  refine ⟨e.toRingEquiv, ?_⟩
  intro c
  show e (algebraMap C (Localization.AtPrime p) c) = _
  rw [e.commutes]
  exact (IsScalarTower.algebraMap_apply C D (Localization.AtPrime (p.map f)) c).symm

private structure LocalPowerFactorization
    {R : Type*} [CommRing R] {r : ℕ} (a : Fin r → R) where
  parameter : R
  parameter_isRegular : IsRegular parameter
  factorUnit : Fin r → Rˣ
  exponent : Fin r → ℕ
  factorization (i : Fin r) :
    a i = (factorUnit i : R) * parameter ^ exponent i

private theorem exists_preparation_of_local_preparations
    (h0EAE : RingHomGluingAtMaximalIdeals.{u})
    {A S : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S] [IsNoetherianRing S]
    {r : ℕ} (a : Fin r → A)
    (hinj : Function.Injective (algebraMap A S))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S))
    (B : MaximalSpectrum S → Type u)
    [∀ q, CommRing (B q)]
    [∀ q, Algebra (Localization.AtPrime q.asIdeal) (B q)]
    (P : ∀ q : MaximalSpectrum S,
      TameSymbolPreparation
        (fun i => algebraMap S (Localization.AtPrime q.asIdeal)
          (algebraMap A S (a i))) (B q)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Nonempty (TameSymbolPreparation a C) := by
  classical
  let : Finite (MaximalSpectrum S) :=
    Stacks.RingTheory.SemilocalModuleFinite.finite_maximalSpectrum_of_moduleFinite_of_isLocalRing
      A S
  let f : ∀ q : MaximalSpectrum S,
      Localization.AtPrime q.asIdeal →+* B q := fun q => algebraMap _ _
  have hfin (q : MaximalSpectrum S) : (f q).Finite :=
    (RingHom.finite_algebraMap).2 (P q).finite
  have hfinj (q : MaximalSpectrum S) : Function.Injective (f q) :=
    (P q).algebraMap_injective
  have hcoker (q : MaximalSpectrum S) :
      Stacks.RingHomGluing.CokernelIsKilledByIdealPower (f q)
        (q.asIdeal.map (algebraMap S (Localization.AtPrime q.asIdeal))) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact smul_top_to_cokernel_power _ (P q).quotient_annihilated_by_maximalIdeal_power
  obtain ⟨C, instC, g, hfg, hginj, hgcoker, hgq⟩ :=
    exists_finite_gluing_at_maximal_ideals h0EAE B f hfin hfinj hcoker
  let : CommRing C := instC
  let : Algebra S C := g.toAlgebra
  let : Algebra A C := ((g.comp (algebraMap A S))).toAlgebra
  let : IsScalarTower A S C := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite S C := hfg
  have hfinite : Module.Finite A C := Module.Finite.trans S C
  have hinjective : Function.Injective (algebraMap A C) := hginj.comp hinj
  have hquotient : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A C) ≤
      LinearMap.range (Algebra.linearMap A C) :=
    annihilated_quotient_trans_of_jacobson hquot hgcoker
  have hlocal (p : Ideal C) [p.IsMaximal] :
      Nonempty (LocalPowerFactorization
        (fun i => algebraMap C (Localization.AtPrime p)
          (algebraMap A C (a i)))) := by
    have hqmax : (p.under S).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal p
    let q : MaximalSpectrum S := ⟨p.under S, hqmax⟩
    obtain ⟨gq, hcomp, hloc⟩ := hgq q
    have hp : p.comap g = q.asIdeal := rfl
    obtain ⟨qD, _, e, he⟩ :=
      exists_localRingEquiv_of_isLocalizationMap_at_maximal
        g q.asIdeal p hp gq hloc
    let Pq := P q
    refine ⟨{
      parameter := e.symm (Pq.parameter qD.asIdeal)
      parameter_isRegular := regular_of_ringEquiv_symm e
        (Pq.parameter_isRegular qD.asIdeal)
      factorUnit := fun i => Units.map e.symm.toMonoidHom (Pq.factorUnit qD.asIdeal i)
      exponent := Pq.exponent qD.asIdeal
      factorization := ?_ }⟩
    intro i
    apply e.injective
    calc
      e (algebraMap C (Localization.AtPrime p) (algebraMap A C (a i))) =
          algebraMap (B q) (Localization.AtPrime qD.asIdeal)
            (gq (g (algebraMap A S (a i)))) := by
              rw [IsScalarTower.algebraMap_apply A S C]
              exact he (g (algebraMap A S (a i)))
      _ = algebraMap (B q) (Localization.AtPrime qD.asIdeal)
            (f q (algebraMap S (Localization.AtPrime q.asIdeal)
              (algebraMap A S (a i)))) := by
              congr 1
              exact congrArg (fun h : S →+* B q => h (algebraMap A S (a i))) hcomp
      _ = (Pq.factorUnit qD.asIdeal i : Localization.AtPrime qD.asIdeal) *
            Pq.parameter qD.asIdeal ^ Pq.exponent qD.asIdeal i :=
              Pq.factorization qD.asIdeal i
      _ = e ((Units.map e.symm.toMonoidHom (Pq.factorUnit qD.asIdeal i) :
              (Localization.AtPrime p)ˣ) *
            (e.symm (Pq.parameter qD.asIdeal)) ^ Pq.exponent qD.asIdeal i) := by
              simp
  let data (p : Ideal C) [p.IsMaximal] := Classical.choice (hlocal p)
  refine ⟨C, instC, inferInstance, ⟨{
    finite := hfinite
    algebraMap_injective := hinjective
    quotient_annihilated_by_maximalIdeal_power := hquotient
    parameter := fun p _ => (data p).parameter
    parameter_isRegular := fun p _ => (data p).parameter_isRegular
    factorUnit := fun p _ => (data p).factorUnit
    exponent := fun p _ => (data p).exponent
    factorization := fun p _ i => (data p).factorization i }⟩⟩

private theorem preparation_comp_finite_local_modification
    {A S T : Type*} [CommRing A] [IsLocalRing A]
    [CommRing S] [IsLocalRing S] [CommRing T]
    [Algebra A S] [Algebra S T] [Algebra A T] [IsScalarTower A S T]
    [Module.Finite A S]
    {r : ℕ} (a : Fin r → A)
    (hinj : Function.Injective (algebraMap A S))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S))
    (P : TameSymbolPreparation (fun i => algebraMap A S (a i)) T)
    (hlocal : IsLocalHom (algebraMap A S)) :
    Nonempty (TameSymbolPreparation a T) := by
  let : Module.Finite S T := P.finite
  refine ⟨{
    finite := Module.Finite.trans S T
    algebraMap_injective := by
      rw [IsScalarTower.algebraMap_eq A S T]
      exact P.algebraMap_injective.comp hinj
    quotient_annihilated_by_maximalIdeal_power :=
      annihilated_quotient_trans_of_local_finite_extensions hlocal hquot
        P.quotient_annihilated_by_maximalIdeal_power
    parameter := P.parameter
    parameter_isRegular := P.parameter_isRegular
    factorUnit := P.factorUnit
    exponent := P.exponent
    factorization := ?_ }⟩
  intro q hq i
  rw [IsScalarTower.algebraMap_apply A S T]
  exact P.factorization q i

private theorem exists_pair_preparation_of_unit_residual
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {x y c : R} (hx : IsRegular x) (m : ℕ)
    (hc : IsUnit c) (hy : y = x ^ m * c) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Nonempty (TameSymbolPreparation ![x, y] T) := by
  let v : Fin 2 → Rˣ := ![1, hc.unit]
  let e : Fin 2 → ℕ := ![1, m]
  apply exists_tameSymbolPreparation_of_power_factorization ![x, y] x hx v e
  intro i
  fin_cases i
  · simp [v, e]
  · simp [v, e, hy, mul_comm]

private theorem exists_pair_preparation_of_unit_residual_in_finite_local_extension
    {A S : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing S] [IsLocalRing S] [Algebra A S] [Module.Finite A S]
    (x y : A)
    (hinj : Function.Injective (algebraMap A S))
    (hquot : ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A S) ≤
      LinearMap.range (Algebra.linearMap A S))
    (hx : IsRegular (algebraMap A S x))
    (m : ℕ) (c : S) (hc : IsUnit c)
    (hy : algebraMap A S y = (algebraMap A S x) ^ m * c) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T),
      Nonempty (TameSymbolPreparation ![x, y] T) := by
  classical
  let : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  obtain ⟨T, ringT, algT, ⟨P⟩⟩ :=
    exists_pair_preparation_of_unit_residual hx m hc hy
  let : CommRing T := ringT
  let : Algebra S T := algT
  let : Algebra A T := ((algebraMap S T).comp (algebraMap A S)).toAlgebra
  let : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq' rfl
  have heq : (fun i => algebraMap A S ((![x, y] : Fin 2 → A) i)) =
      ![algebraMap A S x, algebraMap A S y] := by
    funext i
    fin_cases i <;> simp
  refine ⟨T, ringT, inferInstance, ?_⟩
  rw [← heq] at P
  exact preparation_comp_finite_local_modification ![x, y] hinj hquot P
    (isLocalHom_of_module_finite_local (A := A) (S := S))

end AlgebraicGeometry
