module

public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.LocalRing.ResidueSection
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.MixedLevelStep

open Stacks.DiscreteValuationRing.AdjoinPthRoot

/-!
# Lowering the level of a degree-`p` extension

A finite separable totally ramified extension which is either a weak solution or lowers the level
to at most `max (0, l - 1, 2 * l - p)` (Stacks Tag 09F5).
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u uA uK uL

open Polynomial

namespace Stacks.DiscreteValuationRing.EppLevelInduction

set_option maxHeartbeats 2000000 in
-- This assembles the whole construction and needs far more than the default budget.
/-- A positive finite-level extension of prime degree in mixed characteristic can be
base-changed by a finite separable extension totally ramified over the bottom discrete
valuation ring so that either the full tower has a weak solution or the level is at most
`max (0, l - 1, 2 * l - p)`. -/
theorem exists_totallyRamified_isWeakSolution_or_extensionLevel_le_or_finiteSupport_of_uniformizer
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra A M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower A B L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K L]
    [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) [Fact p.Prime] [CharZero K]
    [CharP (IsLocalRing.ResidueField A) p]
    [ExpChar (IsLocalRing.ResidueField B) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (πA : A) (hπA : Irreducible πA)
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    [Module.Finite L M]
    (hfinite : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P)
    (l : ℚ)
    (hlevel : ∃ (π : B) (e₁ : ℕ) (he₁ : 0 < e₁)
        (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P π).Nonempty),
        Irreducible π ∧ Associated (wElt f) (π ^ e₁) ∧
          l = Stacks.DegreePExtensionLevel.extensionLevel B L M P π e₁ he₁ hne)
    (hl : 0 < l) :
    MixedLevelStepOutcome A B C K L M p f P l ∨
      ∃ s : Finset (IsLocalRing.ResidueField B),
        (∀ x ∈ s, x ∈ perfectCore (IsLocalRing.ResidueField B) p) ∧
          (¬∀ x ∈ s, x ∈
            (algebraMap (IsLocalRing.ResidueField A)
              (IsLocalRing.ResidueField B)).fieldRange) ∧
          MixedLevelPreparation B L M p f P l (algebraMap A B πA) s ∧
          MixedLevelStepReentry B C L M p f P l (algebraMap A B πA) s := by
  classical
  let ρ := algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  let : CharP (IsLocalRing.ResidueField B) p :=
    CharP.of_ringHom_of_ne_zero ρ p (Fact.out : p.Prime).ne_zero
  have hmapmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by
    simpa only [show IsDiscreteValuationRing.ramificationIndex A B = 1 from hweak, pow_one] using
      (IsDiscreteValuationRing.ramificationIndex_characterization A B).2.1
  obtain ⟨π₀, e, he, hne₀, hπ₀, hw₀, rfl⟩ := hlevel
  let π := algebraMap A B πA
  have hπ : Irreducible π := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr
    rw [← hmapmax, hπA.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hπassoc : Associated π₀ π :=
    IsDiscreteValuationRing.associated_of_irreducible B hπ₀ hπ
  have hnumEq := extensionLevelNumerators_eq_of_associated (K := L) (L := M) P hπassoc
  have hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P π).Nonempty := hnumEq ▸
    hne₀
  have hw : Associated (wElt f) (π ^ e) := hw₀.trans (hπassoc.pow_pow (n := e))
  have hlevelEq : Stacks.DegreePExtensionLevel.extensionLevel B L M P π₀ e he hne₀ =
      Stacks.DegreePExtensionLevel.extensionLevel B L M P π e he hne := by
    simp only [Stacks.DegreePExtensionLevel.extensionLevel, hnumEq]
  rw [hlevelEq] at hl ⊢
  let n := sInf (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P π)
  have hnmem : n ∈ Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P π := Nat.sInf_mem
    hne
  have hnpos : 0 < n := by
    by_contra hzero
    have hnzero : n = 0 := by omega
    change 0 < (n : ℚ) / e at hl
    simp [hnzero] at hl
  have hnbound : n < p * e := by
    obtain ⟨_, ξ, z, hz, hPz, a, ha, heq⟩ := hfinite
    have hπL : algebraMap B L π ≠ 0 := (map_ne_zero_iff _
      (IsFractionRing.injective B L)).mpr hπ.ne_zero
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    obtain ⟨b, hb⟩ := mul_pow_sub_one_mul_mem_range π (wElt f) hπL p e
      (Nat.mul_pos (Fact.out : p.Prime).pos he) hw ξ a ha heq
    have hcandidate : p * e - 1 ∈ Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P π :=
      ⟨ξ, z, hz, hPz, b, hb⟩
    exact lt_of_le_of_lt (Nat.sInf_le hcandidate)
      (Nat.sub_lt (Nat.mul_pos (Fact.out : p.Prime).pos he) (by decide))
  let m := min n (min e (p * e - n))
  obtain ⟨hmpos, hmle, hme, hbound⟩ := level_decrement_bounds n e p hnpos he hnbound
  have hpmB : (p : B) ∈ IsLocalRing.maximalIdeal B ^ m :=
    natCast_mem_maximalIdeal_pow_of_cyclotomic f P hP.1 π hπ e m hw hme
  let : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hcomap : (IsLocalRing.maximalIdeal B ^ m).comap (algebraMap A B) =
      IsLocalRing.maximalIdeal A ^ m := by
    rw [← hmapmax, ← Ideal.map_pow, Ideal.comap_map_eq_self_of_faithfullyFlat]
  have hpmA : (p : A) ∈ IsLocalRing.maximalIdeal A ^ m := by
    rw [← hcomap]
    show algebraMap A B (p : A) ∈ IsLocalRing.maximalIdeal B ^ m
    simpa only [map_natCast] using hpmB
  obtain ⟨ξ, z, a, hz, hPz, hau, ha⟩ :=
    exists_unit_of_isLeast_extensionLevelNumerator P π hπ n hnpos
      ⟨hnmem, fun _ hk => Nat.sInf_le hk⟩
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨hfinGal, hgal, _⟩ :=
    isGalois_and_ramification_cases_of_adjoin_root_cyclotomic_quotient B L M p f P hP
      ξ z (by simpa only [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] using hPz)
      hz π hπ
  let : IsGalois L M := hgal
  have hwne : wElt f ≠ 0 := hw.ne_zero_iff.mpr (pow_ne_zero _ hπ.ne_zero)
  let QB := B ⧸ IsLocalRing.maximalIdeal B ^ m
  let : Nontrivial QB := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top
      (Ideal.pow_le_self hmpos.ne'))
  let qB : B →+* QB := Ideal.Quotient.mk _
  let : IsLocalRing QB := IsLocalRing.of_surjective' qB Ideal.Quotient.mk_surjective
  let : IsLocalHom qB := IsLocalHom.of_surjective qB Ideal.Quotient.mk_surjective
  let rQB : QB →+* IsLocalRing.ResidueField B :=
    Ideal.Quotient.lift _ (IsLocalRing.residue B) (by
      intro b hb
      exact (IsLocalRing.residue_eq_zero_iff b).mpr ((Ideal.pow_le_self hmpos.ne') hb))
  obtain ⟨σq, hσq⟩ := exists_residueField_section_quotient_pow B m p hpmB
  obtain ⟨σ, σbar, hσ, hσbar⟩ :=
    exists_lift_residueField_section qB Ideal.Quotient.mk_surjective σq hσq
  let : CharP QB p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (by simpa only [map_natCast] using (Ideal.Quotient.eq_zero_iff_mem.mpr hpmB))
  let QA := A ⧸ IsLocalRing.maximalIdeal A ^ m
  let : Nontrivial QA := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (Ideal.pow_le_self hmpos.ne'))
  let qA : A →+* QA := Ideal.Quotient.mk _
  let : IsLocalRing QA := IsLocalRing.of_surjective' qA Ideal.Quotient.mk_surjective
  let : IsLocalHom qA := IsLocalHom.of_surjective qA Ideal.Quotient.mk_surjective
  obtain ⟨τq, hτq⟩ := exists_residueField_section_quotient_pow A m p hpmA
  obtain ⟨τ, τbar, hτ, hτbar⟩ :=
    exists_lift_residueField_section qA Ideal.Quotient.mk_surjective τq hτq
  let qAB : QA →+* QB := Ideal.quotientMap _ (algebraMap A B) (by rw [hcomap])
  have hcompatible : qAB.comp τbar = σbar.comp ρ := by
    apply ringHom_eq_of_sub_mem_nilpotent_of_perfect p (IsLocalRing.maximalIdeal QB)
      (isNilpotent_maximalIdeal_quotient_pow B m)
    intro x
    have hdiff : algebraMap A B (τ x) - σ (ρ x) ∈ IsLocalRing.maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hσ]
      show IsLocalRing.residue B (algebraMap A B (τ x)) - ρ x = 0
      rw [← IsLocalRing.ResidueField.map_residue, hτ]
      exact sub_self (ρ x)
    have hdiffQ := map_nonunit qB _ hdiff
    show qAB (τbar x) - σbar (ρ x) ∈ IsLocalRing.maximalIdeal QB
    rw [← hτbar, ← hσbar]
    show qB (algebraMap A B (τ x)) - qB (σ (ρ x)) ∈ IsLocalRing.maximalIdeal QB
    simpa only [map_sub] using hdiffQ
  obtain ⟨cfs, b, hab⟩ := exists_eq_sum_pow_add_pow_mul π hπ.maximalIdeal_eq σ hσ a m
  have hLaurent : ξ =
      ((∑ i ∈ Finset.range m, algebraMap B L (σ (cfs i)) * algebraMap B L π ^ i) +
        algebraMap B L π ^ m * algebraMap B L b) / algebraMap B L π ^ n := by
    have hπL : algebraMap B L π ≠ 0 := (map_ne_zero_iff _
      (IsFractionRing.injective B L)).mpr hπ.ne_zero
    apply (eq_div_iff (pow_ne_zero n hπL)).mpr
    rw [mul_comm, ← map_pow, ← ha, hab]
    simp only [map_add, map_sum, map_mul, map_pow]
  have hdescend : (∀ i ∈ Finset.range m, cfs i ∈ Set.range ρ) →
      ∃ aA : A, qB a = qB (algebraMap A B aA) := by
    intro hcfs
    have hex : ∀ i : ℕ, ∃ x : IsLocalRing.ResidueField A, i < m → ρ x = cfs i := by
      intro i
      by_cases hi : i < m
      · obtain ⟨x, hx⟩ := hcfs i (Finset.mem_range.mpr hi)
        exact ⟨x, fun _ => hx⟩
      · exact ⟨0, fun h => (hi h).elim⟩
    choose cA hcA using hex
    refine ⟨∑ i ∈ Finset.range m, τ (cA i) * πA ^ i, ?_⟩
    have hπm : qB π ^ m = 0 := by
      rw [← map_pow]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    rw [hab]
    simp only [map_add, map_sum, map_mul, map_pow, hπm, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hci := hcA i (Finset.mem_range.mp hi)
    have hcomp := DFunLike.congr_fun hcompatible (cA i)
    change qAB (τbar (cA i)) = σbar (ρ (cA i)) at hcomp
    rw [hci, ← hτbar, ← hσbar] at hcomp
    change qB (algebraMap A B (τ (cA i))) = qB (σ (cfs i)) at hcomp
    rw [← hcomp]
  have hnotdvd : (∀ i ∈ Finset.range m, cfs i ∈ Set.range ρ) → ¬p ∣ n := by
    intro hcfs hpn
    obtain ⟨aA, haA⟩ := hdescend hcfs
    have hadiff : a - algebraMap A B aA ∈ IsLocalRing.maximalIdeal B ^ m :=
      Ideal.Quotient.eq_zero_iff_mem.mp (by
        show qB (a - algebraMap A B aA) = 0
        rw [map_sub, haA, sub_self])
    have hresA : IsLocalRing.residue B a = ρ (IsLocalRing.residue A aA) := by
      have hzero := (IsLocalRing.residue_eq_zero_iff _).mpr
        (Ideal.pow_le_self hmpos.ne' hadiff)
      rw [map_sub, ← IsLocalRing.ResidueField.map_residue] at hzero
      exact sub_eq_zero.mp hzero
    obtain ⟨c, hc⟩ :=
      (PerfectRing.bijective_frobenius (R := IsLocalRing.ResidueField A) (p := p)).2
        (IsLocalRing.residue A aA)
    apply not_isPow_residue_of_isLeast_extensionLevelNumerator
      p f P hP.1 hP.2.2.2 π hπ e n hw hnpos hnbound
      ⟨hnmem, fun _ hk => Nat.sInf_le hk⟩ hpn ξ z a hz
      (by simpa only [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] using hPz)
      (by simpa only [map_pow] using ha)
    refine ⟨ρ c, ?_⟩
    rw [hresA, ← map_pow]
    exact congrArg ρ hc.symm
  by_cases hcfs : ∀ i ∈ Finset.range m, cfs i ∈ Set.range ρ
  · obtain ⟨aA, haA⟩ := hdescend hcfs
    have haAu : IsUnit aA := by
      apply (isUnit_map_iff (algebraMap A B) aA).mp
      apply (isUnit_map_iff qB (algebraMap A B aA)).mp
      rw [← haA]
      exact hau.map qB
    obtain ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfinK₁, hsepK₁, htot, hdeg, y, hygen, hy⟩ :=
      exists_totallyRamified_root_pow_sub A K p (Fact.out : p.Prime).one_lt πA (-aA)
        hπA haAu.neg n hnpos ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (hnotdvd hcfs))
    refine Or.inl ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfinK₁, hsepK₁, htot, ?_⟩
    obtain ⟨hL₁, hA₁, hBdom, hB₁, hinj, hmap, hCdom, hC₁, hfrac, eB, heB, hinj', hmap'⟩ :=
      IsDiscreteValuationRing.isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified
        A B K L K₁ hmapmax htot
    by_cases hM₁ : IsField (M ⊗[K] K₁)
    · right
      let := hL₁.toField
      let := hM₁.toField
      have hadiff : π ^ m ∣ a - algebraMap A B aA := by
        rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq,
          ← Ideal.Quotient.eq_zero_iff_mem]
        show qB (a - algebraMap A B aA) = 0
        rw [map_sub, haA, sub_self]
      obtain ⟨b₁, hb₁⟩ := hadiff
      have hξA : algebraMap B L π ^ n * ξ - algebraMap B L (algebraMap A B aA) =
          algebraMap B L π ^ m * algebraMap B L b₁ := by
        rw [← map_pow, ← ha, ← map_sub, hb₁, map_mul, map_pow]
      have hyT := artinSchreier_eq_tensor_includeRight πA aA
        ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hπA.ne_zero) n p y hy hL₁
      have hyB : algebraMap B (L ⊗[K] K₁) π ^ n *
          (((1 : L) ⊗ₜ[K] y) ^ p - (1 : L) ⊗ₜ[K] y) =
            -algebraMap B (L ⊗[K] K₁) (algebraMap A B aA) := by
        simpa only [π, ← IsScalarTower.algebraMap_apply A B (L ⊗[K] K₁)] using hyT
      obtain ⟨hfin, hfl, π₁, e₁, he₁, hne₁, hπ₁, hw₁, hle⟩ :=
        finiteLevel_tensorProduct_of_artinSchreier_shift p f P hP hfinite.1 π hπ e n m
          he hw hnbound hme hmle (by dsimp [m]; omega) z hz ξ
          (by simpa only [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] using hPz)
          (algebraMap A B aA) b₁ hξA hL₁ hM₁ hC₁ hfrac (1 ⊗ₜ[K] y) hyB
      exact ⟨hL₁, hM₁, hC₁, hfrac, hfin, hfl, π₁, e₁, he₁, hne₁, hπ₁, hw₁,
        hle.trans_eq hbound⟩
    · left
      let := hL₁.toField
      obtain ⟨φ⟩ := nonempty_algHom_of_cyclotomic_tensor_not_isField p f P hP.1 hwne
        hfinite.1 ξ z hz
        (by simpa only [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] using hPz) hL₁ hM₁
      exact exists_isWeakSolution_of_tensor_embedding (A := A) (B := B) (C := C) z hz
        hL₁ hA₁ hC₁ hfrac (eB.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
        hmap' heB φ
  · let F : Polynomial B := ∑ i ∈ Finset.range m,
        Polynomial.monomial (n - i) (σ (cfs i))
    let F₀ : Polynomial (IsLocalRing.ResidueField B) := ∑ i ∈ Finset.range m,
        Polynomial.monomial (n - i) (cfs i)
    have hFd : F.natDegree ≤ n := Polynomial.natDegree_sum_le_of_forall_le _ _
      fun _ _ => (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le _ _)
    have hF₀d : F₀.natDegree ≤ n := Polynomial.natDegree_sum_le_of_forall_le _ _
      fun _ _ => (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le _ _)
    have hF : F.map qB = F₀.map σbar := by
      simp only [F, F₀, Polynomial.map_sum, Polynomial.map_monomial, hσbar]
    have hF₀zero : F₀.coeff 0 ∈ perfectCore (IsLocalRing.ResidueField B) p := by
      have hzero : F₀.coeff 0 = 0 := by
        rw [Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro i hi
        rw [Polynomial.coeff_monomial, ite_eq_right (by
          have := Finset.mem_range.mp hi
          omega)]
      rw [hzero]
      exact (perfectCore (IsLocalRing.ResidueField B) p).zero_mem
    have hπL : algebraMap B L π ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective B L).ne hπ.ne_zero
    have hFnorm : algebraMap B L π ^ n * Polynomial.aeval (algebraMap B L π)⁻¹ F =
        ∑ i ∈ Finset.range m, algebraMap B L (σ (cfs i)) * algebraMap B L π ^ i := by
      simp only [F, map_sum, Polynomial.aeval_monomial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
      have hpow : algebraMap B L π ^ n * (algebraMap B L π)⁻¹ ^ (n - i) =
          algebraMap B L π ^ i := by
        rw [inv_pow, ← pow_sub₀ _ hπL (Nat.sub_le n i),
          Nat.sub_sub_self hin]
      calc
        algebraMap B L π ^ n *
            (algebraMap B L (σ (cfs i)) * (algebraMap B L π)⁻¹ ^ (n - i)) =
          algebraMap B L (σ (cfs i)) *
            (algebraMap B L π ^ n * (algebraMap B L π)⁻¹ ^ (n - i)) := by ring
        _ = _ := by rw [hpow]
    have hξF : ∃ a : B, algebraMap B L π ^ n *
          (ξ - Polynomial.aeval (algebraMap B L π)⁻¹ F) = algebraMap B L (π ^ m * a) := by
      refine ⟨b, ?_⟩
      have ha' := ha
      rw [hab] at ha'
      simp only [map_add, map_sum, map_mul, map_pow] at ha'
      rw [mul_sub, hFnorm, map_mul, map_pow]
      linear_combination -ha'
    have hker : ∀ a : B, qB a = 0 ↔ π ^ m ∣ a := by
      intro a
      show Ideal.Quotient.mk _ a = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, hπ.maximalIdeal_eq,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨ξ', z', H, H₀, hz', hPz', hHd, hH, hH₀zero, hnone, hξ'⟩ :=
      exists_generator_no_pow_related_coefficients p f P hP.1 hP.2.2.1 hP.2.2.2
        π hπ e n m hw hnbound hme (by dsimp [m]; omega)
        qB Ideal.Quotient.mk_surjective hker σbar
        (perfectCore (IsLocalRing.ResidueField B) p).toSubring
        F F₀ hF hFd hF₀d hF₀zero ξ z hz
        (by simpa only [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] using hPz) hξF
    have hH₀d : H₀.natDegree ≤ n := by
      rw [← Polynomial.natDegree_map σbar, ← hH]
      exact Polynomial.natDegree_map_le.trans hHd
    by_cases hbad : ∃ i, H₀.coeff i ∉ perfectCore (IsLocalRing.ResidueField B) p
    · obtain ⟨h, μ, N, j, hj, hμ, hjmax⟩ := exists_root_heights_and_unique_max
        p n (Fact.out : p.Prime).one_lt
        (perfectCore (IsLocalRing.ResidueField B) p).toSubring
        (fun x => mem_perfectCore_iff_forall_one_le) H₀ hH₀zero hnone hbad
      have hNpos : 0 < N := by have := (hμ j hj).2.2.1; omega
      have hroots : ∀ i : ℕ, ∃ ν : IsLocalRing.ResidueField B,
          if H₀.coeff i ∈ perfectCore (IsLocalRing.ResidueField B) p then
            ν ^ (p ^ N) = H₀.coeff i else ν = μ i := by
        intro i
        by_cases hi : H₀.coeff i ∈ perfectCore (IsLocalRing.ResidueField B) p
        · obtain ⟨ν, hν⟩ := mem_perfectCore_iff_forall_one_le.mp hi N hNpos
          exact ⟨ν, by simpa only [ite_eq_left hi] using hν⟩
        · exact ⟨μ i, by simp only [ite_eq_right hi]⟩
      choose ν hν using hroots
      let h' : ℕ → ℕ := fun i =>
        if H₀.coeff i ∈ perfectCore (IsLocalRing.ResidueField B) p then N else h i
      have hh' : ∀ i ∈ H₀.support, h' i ≤ N := by
        intro i _
        dsimp only [h']
        split_ifs with hi
        · exact le_rfl
        · have := (hμ i hi).2.2.1
          omega
      have hνpow : ∀ i ∈ H₀.support, ν i ^ (p ^ h' i) = H₀.coeff i := by
        intro i _
        by_cases hi : H₀.coeff i ∈ perfectCore (IsLocalRing.ResidueField B) p
        · simpa only [h', ite_eq_left hi] using hν i
        · have hνi : ν i = μ i := by simpa only [ite_eq_right hi] using hν i
          simpa only [h', ite_eq_right hi, hνi] using (hμ i hi).1
      obtain ⟨G₀, hG₀d, htransform⟩ :=
        exists_comp_X_pow_add_pow_sub p H₀ N hNpos h' ν hh' hνpow
      let D₀ : Polynomial (IsLocalRing.ResidueField B) :=
        ∑ i ∈ H₀.support, Polynomial.monomial (i * p ^ (N - h' i)) (ν i)
      have hjmem : j ∈ H₀.support := Polynomial.mem_support_iff.mpr
        (fun heq => hj (heq ▸ (perfectCore (IsLocalRing.ResidueField B) p).zero_mem))
      have hjCore : H₀.coeff j ∉ perfectCore (IsLocalRing.ResidueField B) p := by
        intro hmem
        exact hj hmem
      have hhj : h' j = h j := by simp only [h', ite_eq_right hjCore]
      have hνj : ν j = μ j := by simpa only [ite_eq_right hjCore] using hν j
      have hνjne : ν j ≠ 0 := by
        intro hz
        apply (hμ j hj).2.1
        refine ⟨0, ?_⟩
        rw [zero_pow (Fact.out : p.Prime).ne_zero, ← hνj, hz]
      have hmax : ∀ i ∈ H₀.support, i ≠ j →
          i * p ^ (N - h' i) < j * p ^ (N - h' j) := by
        intro i hi hij
        rw [hhj]
        by_cases hiS : H₀.coeff i ∈ perfectCore (IsLocalRing.ResidueField B) p
        · simp only [h', ite_eq_left hiS, Nat.sub_self, pow_zero, mul_one]
          exact ((Polynomial.le_natDegree_of_mem_supp i hi).trans hH₀d).trans_lt
            (hμ j hj).2.2.2
        · simpa only [h', ite_eq_right hiS] using hjmax i hiS hij
      obtain ⟨hDdegree, hDcoeff⟩ := natDegree_and_coeff_sum_monomial_of_unique_max
        H₀.support (fun i => i * p ^ (N - h' i)) ν j hjmem hνjne hmax
      have hDnotpow : ¬∃ x : IsLocalRing.ResidueField B,
          x ^ p = D₀.coeff D₀.natDegree := by
        rw [hDdegree, hDcoeff, hνj]
        exact (hμ j hj).2.1
      have hDdiv : p ∣ D₀.natDegree := by
        rw [hDdegree, hhj]
        exact dvd_mul_of_dvd_right
          (dvd_pow_self p (show N - h j ≠ 0 by have := (hμ j hj).2.2.1; omega)) j
      obtain ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfinK₁, hsepK₁, htot, hdeg, t, ht, htint⟩ :=
        exists_totallyRamified_root_uniformizer A K πA hπA (p ^ N)
          (Nat.pow_pos (Fact.out : p.Prime).pos)
      refine Or.inl ⟨K₁, hK₁, hKK₁, hAK₁, htower, hfinK₁, hsepK₁, htot, ?_⟩
      obtain ⟨hL₁, hA₁, hBdom, hB₁, hinj, hmap, hCdom, hC₁, hfrac, eB, heB, hinj', hmap'⟩ :=
        IsDiscreteValuationRing.isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified
          A B K L K₁ hmapmax htot
      by_cases hM₁ : IsField (M ⊗[K] K₁)
      · let := hL₁.toField
        let := hM₁.toField
        let A₁ := integralClosure A K₁
        let B₁ := integralClosure B (L ⊗[K] K₁)
        let : CommRing B₁ := inferInstance
        let := hA₁
        let := hC₁
        let := hfrac
        let ι : L ⊗[K] K₁ →ₐ[K] M ⊗[K] K₁ :=
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K K₁)
        let : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) := ι.toRingHom.toAlgebra
        have hι (x : L) (a : K₁) : ι (x ⊗ₜ[K] a) = algebraMap L M x ⊗ₜ[K] a :=
          Algebra.TensorProduct.map_tmul (IsScalarTower.toAlgHom K L M) (AlgHom.id K K₁) x a
        have : IsScalarTower L (L ⊗[K] K₁) (M ⊗[K] K₁) :=
          IsScalarTower.of_algebraMap_eq fun x => (hι x 1).symm
        have : IsScalarTower B (L ⊗[K] K₁) (M ⊗[K] K₁) :=
          IsScalarTower.of_algebraMap_eq fun b => by
            rw [IsScalarTower.algebraMap_apply B L (M ⊗[K] K₁),
              IsScalarTower.algebraMap_apply L (L ⊗[K] K₁) (M ⊗[K] K₁),
              ← IsScalarTower.algebraMap_apply B L (L ⊗[K] K₁)]
        let q := p ^ N
        have hqpos : 0 < q := Nat.pow_pos (Fact.out : p.Prime).pos
        let tA : A₁ := ⟨t, htint⟩
        have htA : Irreducible tA := irreducible_root_of_totallyRamified htot q hqpos hdeg πA hπA
          t ht htint
        let f' : A₁ →+* B₁ := eB.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
        let tB : B₁ := f' tA
        have htB : Irreducible tB := by
          apply (IsDiscreteValuationRing.irreducible_iff_uniformizer tB).mpr
          rw [← hmap', htA.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
        have htBval : (tB : L ⊗[K] K₁) = (1 : L) ⊗ₜ[K] t := heB tA
        have htBpow : tB ^ q = algebraMap B B₁ π := by
          apply Subtype.val_injective
          show (tB : L ⊗[K] K₁) ^ q = algebraMap B (L ⊗[K] K₁) π
          rw [htBval]
          show ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) t) ^ q = _
          rw [← map_pow (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁), ht]
          simp only [π, IsScalarTower.algebraMap_apply A K K₁,
            AlgHom.commutes, ← IsScalarTower.algebraMap_apply A K (L ⊗[K] K₁),
            ← IsScalarTower.algebraMap_apply A B (L ⊗[K] K₁)]
        obtain ⟨erA⟩ :=
          IsDiscreteValuationRing.exists_residueField_algEquiv_of_totallyRamified A K K₁ htot
        obtain ⟨erB⟩ :=
          IsDiscreteValuationRing.exists_residueField_algEquiv_of_tensorProduct A B A₁ B₁
            hmapmax erA eB (by simpa only [Ideal.map_map] using hmap')
        let er : IsLocalRing.ResidueField B₁ ≃+* IsLocalRing.ResidueField B := erB.toRingEquiv
        have herB (b : B) : er (IsLocalRing.residue B₁ (algebraMap B B₁ b)) =
            IsLocalRing.residue B b := erB.commutes b
        let Q₁ := B₁ ⧸ IsLocalRing.maximalIdeal B₁ ^ (m * q)
        let : CommRing Q₁ := inferInstance
        let q₁ : B₁ →+* Q₁ := Ideal.Quotient.mk _
        have hker₁ (b : B₁) : q₁ b = 0 ↔ tB ^ (m * q) ∣ b := by
          rw [Ideal.Quotient.eq_zero_iff_mem, htB.maximalIdeal_eq, Ideal.span_singleton_pow,
            Ideal.mem_span_singleton]
        let ψ : QB →+* Q₁ := Ideal.Quotient.lift _ (q₁.comp (algebraMap B B₁)) (by
          intro b hb
          show q₁ (algebraMap B B₁ b) = 0
          apply (hker₁ _).mpr
          have hdiv : π ^ m ∣ b := by
            rwa [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
          have h := map_dvd (algebraMap B B₁) hdiv
          simpa only [map_pow, ← htBpow, ← pow_mul, Nat.mul_comm q m] using h)
        have hψ (b : B) : ψ (qB b) = q₁ (algebraMap B B₁ b) := rfl
        let σ₁ := ψ.comp σbar
        have hmq : 0 < m * q := Nat.mul_pos hmpos hqpos
        let : Nontrivial Q₁ := Ideal.Quotient.nontrivial_iff.mpr
          (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B₁).ne_top
            (Ideal.pow_le_self hmq.ne'))
        let r₁ : Q₁ →+* IsLocalRing.ResidueField B₁ := Ideal.Quotient.lift _
          (IsLocalRing.residue B₁) (by
            intro b hb
            exact (IsLocalRing.residue_eq_zero_iff b).mpr ((Ideal.pow_le_self hmq.ne') hb))
        have hσ₁ (x : IsLocalRing.ResidueField B) : er (r₁ (σ₁ x)) = x := by
          show er (r₁ (ψ (σbar x))) = x
          rw [← hσbar x, hψ]
          show er (IsLocalRing.residue B₁ (algebraMap B B₁ (σ x))) = x
          rw [herB, hσ]
        let P₁ := P.map (algebraMap B B₁)
        let f₁ := (algebraMap B B₁).comp f
        have hP₁ := cyclotomic_properties_map f P hP (algebraMap B B₁)
        have hw₁ : Associated (wElt f₁) (tB ^ (e * q)) := by
          have h := hw.map (algebraMap B B₁)
          simpa only [f₁, wElt_comp, map_pow, ← htBpow, ← pow_mul, Nat.mul_comm q e] using h
        have htBL : algebraMap B₁ (L ⊗[K] K₁) tB ≠ 0 :=
          (IsFractionRing.injective B₁ (L ⊗[K] K₁)).ne htB.ne_zero
        obtain ⟨hfin₁, hdim₁, hgen₁⟩ := finite_finrank_adjoin_tensorProduct_of_isField hL₁ z' hz'
        let := hfin₁
        have heval₁ : Polynomial.aeval (z' ⊗ₜ[K] (1 : K₁)) P₁ =
            algebraMap (L ⊗[K] K₁) (M ⊗[K] K₁) (ξ' ⊗ₜ[K] (1 : K₁)) := by
          rw [Polynomial.aeval_map_algebraMap]
          show Polynomial.eval₂ ((Algebra.TensorProduct.includeLeftRingHom : M →+* M ⊗[K] K₁).comp
            (algebraMap B M)) (z' ⊗ₜ[K] (1 : K₁)) P = _
          rw [eval₂_tensor_includeLeft]
          show Polynomial.aeval z' P ⊗ₜ[K] (1 : K₁) = _
          rw [hPz']
          exact (hι ξ' 1).symm
        obtain ⟨G, hG, hGd⟩ := exists_map_eq_natDegree_le (R := B₁) (S := Q₁) q₁
          Ideal.Quotient.mk_surjective (G₀.map σ₁)
        let F₁ := (H.map (algebraMap B B₁)).comp (Polynomial.X ^ q)
        have hF₁d : F₁.natDegree ≤ n * q := Polynomial.natDegree_comp_le.trans (by
          rw [Polynomial.natDegree_X_pow]
          exact Nat.mul_le_mul_right q (Polynomial.natDegree_map_le.trans hHd))
        have hGd₁ : G.natDegree * p ≤ n * q :=
          (Nat.mul_le_mul_right p (hGd.trans Polynomial.natDegree_map_le)).trans
            (hG₀d.trans (Nat.mul_le_mul_right q hH₀d))
        have hF₁map : F₁.map q₁ = (H₀.comp (Polynomial.X ^ q)).map σ₁ := by
          have hh := congrArg (Polynomial.map ψ) hH
          simp only [Polynomial.map_map] at hh
          have hmaps : q₁.comp (algebraMap B B₁) = ψ.comp qB := by ext; rfl
          simp only [F₁, Polynomial.map_comp, Polynomial.map_map, hmaps, hh,
            Polynomial.map_pow, Polynomial.map_X]
          rfl
        have hF₁eval : Polynomial.aeval (algebraMap B₁ (L ⊗[K] K₁) tB)⁻¹ F₁ =
            algebraMap L (L ⊗[K] K₁) (Polynomial.aeval (algebraMap B L π)⁻¹ H) := by
          rw [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X, inv_pow,
            ← map_pow, htBpow, ← IsScalarTower.algebraMap_apply B B₁ (L ⊗[K] K₁),
            Polynomial.aeval_map_algebraMap, IsScalarTower.algebraMap_apply B L (L ⊗[K] K₁),
            ← map_inv₀, Polynomial.aeval_algebraMap_apply]
        have hξ₁ : ∃ a : B₁, algebraMap B₁ (L ⊗[K] K₁) tB ^ (n * q) *
            ((ξ' ⊗ₜ[K] (1 : K₁)) - Polynomial.aeval (algebraMap B₁ (L ⊗[K] K₁) tB)⁻¹ F₁) =
            algebraMap B₁ (L ⊗[K] K₁) (tB ^ (m * q) * a) := by
          obtain ⟨b, hb⟩ := hξ'
          refine ⟨algebraMap B B₁ b, ?_⟩
          rw [hF₁eval]
          have hpow (k : ℕ) : tB ^ (k * q) = algebraMap B B₁ (π ^ k) := by
            rw [Nat.mul_comm k q, pow_mul, htBpow, map_pow]
          simp only [← map_pow, hpow, ← IsScalarTower.algebraMap_apply B B₁ (L ⊗[K] K₁),
            IsScalarTower.algebraMap_apply B L (L ⊗[K] K₁), ← map_mul, ← hb]
          simp only [map_mul, map_sub]
          rfl
        obtain ⟨ξ₂, z₂, H₁, hz₂, hPz₂, hH₁d, hH₁map, hξ₂⟩ :=
          exists_generator_cyclotomic_add_polynomial (A := B₁) (K := L ⊗[K] K₁)
            (L := M ⊗[K] K₁) (R := Q₁) p f₁ P₁ hP₁.1 hP₁.2.2.1 hP₁.2.2.2
            tB htB (e * q) (n * q) (m * q) hw₁
            (by simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_right hnbound hqpos)
            (Nat.mul_le_mul_right q hme)
            (by have hh : n + m ≤ p * e := by dsimp [m]; omega
                simpa only [Nat.add_mul, Nat.mul_assoc] using Nat.mul_le_mul_right q hh)
            q₁ hker₁ F₁ G hF₁d hGd₁ (ξ' ⊗ₜ[K] (1 : K₁))
            (z' ⊗ₜ[K] (1 : K₁)) hgen₁ heval₁ hξ₁
        have hH₁map' : H₁.map q₁ = D₀.map σ₁ := by
          rw [hH₁map, hF₁map, hG, ← Polynomial.map_pow, ← Polynomial.map_sub, ← Polynomial.map_add]
          exact congrArg (Polynomial.map σ₁) htransform
        obtain ⟨D, hD, hDd⟩ := exists_map_eq_natDegree_le (R := B₁) (S := Q₁) q₁
          Ideal.Quotient.mk_surjective (D₀.map σ₁)
        have hDd' : D.natDegree = D₀.natDegree := by
          apply le_antisymm (hDd.trans Polynomial.natDegree_map_le)
          have hd := Polynomial.natDegree_map_le (p := D) (f := q₁)
          rw [hD, Polynomial.natDegree_map] at hd
          exact hd
        have hD₀d : D₀.natDegree ≤ n * q := by
          rw [← Polynomial.natDegree_map σ₁, ← hH₁map']
          exact Polynomial.natDegree_map_le.trans hH₁d
        have hHD := hH₁map'.trans hD.symm
        have hDnd := hDd'.trans_le hD₀d
        obtain ⟨b₂, hb₂⟩ := exists_aeval_inv_sub_eq_of_map_eq (A := B₁) (K := L ⊗[K] K₁) (R := Q₁)
          q₁ tB htBL (m * q) (n * q)
          hker₁ H₁ D hH₁d hDnd hHD
        obtain ⟨b₁, hb₁⟩ := hξ₂
        have hξD : algebraMap B₁ (L ⊗[K] K₁) tB ^ (n * q) *
            (ξ₂ - Polynomial.aeval (algebraMap B₁ (L ⊗[K] K₁) tB)⁻¹ D) =
              algebraMap B₁ (L ⊗[K] K₁) (tB ^ (m * q) * (b₁ + b₂)) := by
          simp only [map_mul, map_add, map_pow] at hb₁ hb₂ ⊢
          linear_combination hb₁ + hb₂
        have hlc : er (IsLocalRing.residue B₁ D.leadingCoeff) = D₀.coeff D₀.natDegree := by
          have hh := congrArg (fun F : Polynomial Q₁ => F.coeff D₀.natDegree) hD
          simp only [Polynomial.coeff_map, ← hDd', Polynomial.coeff_natDegree] at hh
          have hh' := congrArg (fun x => er (r₁ x)) hh
          rw [hσ₁] at hh'
          change er (IsLocalRing.residue B₁ D.leadingCoeff) = D₀.coeff D.natDegree at hh'
          simpa only [hDd'] using hh'
        have hlcne : IsLocalRing.residue B₁ D.leadingCoeff ≠ 0 := by
          intro hzero
          apply hDnotpow
          refine ⟨0, ?_⟩
          rw [← hlc, hzero, map_zero, zero_pow (Fact.out : p.Prime).ne_zero]
        have htBres : IsLocalRing.residue B₁ tB = 0 := by
          rw [IsLocalRing.residue_eq_zero_iff, htB.maximalIdeal_eq]
          exact Ideal.mem_span_singleton_self tB
        by_cases hdsmall : D₀.natDegree ≤ (n - m) * q
        · right
          obtain ⟨a₂, ha₂, _⟩ := exists_scaled_laurent_parameter (A := B₁) (K := L ⊗[K] K₁) tB
            htBL D (n * q) (m * q)
            ((n - m) * q) (Nat.mul_le_mul_right q hmle) (hDd'.trans_le hdsmall)
            (by rw [Nat.sub_mul]) ξ₂ (b₁ + b₂) hξD
          have ha₂' : algebraMap B₁ (L ⊗[K] K₁) a₂ =
              algebraMap B₁ (L ⊗[K] K₁) ((algebraMap B B₁ π) ^ (n - m)) * ξ₂ := by
            rw [← htBpow, ← pow_mul, Nat.mul_comm q (n - m), map_pow]
            exact ha₂
          obtain ⟨hfl, π₁, e₁, he₁, hne₁, hπ₁, hw₁, hle⟩ :=
            isDegreePExtensionOfFiniteLevel_and_extensionLevel_le_of_associated_pow
              B₁ (L ⊗[K] K₁) (M ⊗[K] K₁) p f₁ P₁
              (algebraMap B B₁ π) tB htB q e (n - m) hqpos he
              (Associated.of_eq htBpow.symm)
              (by
                simpa only [f₁, wElt_comp, map_pow] using hw.map (algebraMap B B₁))
              (hdim₁.trans hfinite.1) ξ₂ z₂ hz₂
              (by simpa only
                [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B₁ (L ⊗[K] K₁) (M ⊗[K] K₁)] using
                  hPz₂)
              a₂ ha₂' ((Nat.sub_le n m).trans_lt hnbound)
          exact ⟨hL₁, hM₁, hC₁, hfrac, hfin₁, hfl, π₁, e₁, he₁, hne₁, hπ₁, hw₁,
            hle.trans_eq hbound⟩
        · left
          have hdlarge : n * q - m * q < D.natDegree := by rw [hDd', ← Nat.sub_mul]; omega
          obtain ⟨a₂, ha₂, ha₂def⟩ := exists_scaled_laurent_parameter (A := B₁) (K := L ⊗[K] K₁)
            tB htBL D
            (n * q) (m * q) D.natDegree (Nat.mul_le_mul_right q hmle) le_rfl hdlarge.le
            ξ₂ (b₁ + b₂) hξD
          have ha₂res : IsLocalRing.residue B₁ a₂ = IsLocalRing.residue B₁ D.leadingCoeff := by
            rw [ha₂def, Nat.sub_self, pow_zero, one_mul, map_add, map_mul, map_pow,
              htBres, zero_pow (by omega : D.natDegree - (n * q - m * q) ≠ 0), zero_mul,
              add_zero, residue_eval_scaleRoots_one D tB htBres hlcne]
          have ha₂notpow : ¬∃ b : IsLocalRing.ResidueField B₁, IsLocalRing.residue B₁ a₂ = b ^ p
            := by
            rintro ⟨b, hb⟩
            apply hDnotpow
            refine ⟨er b, ?_⟩
            rw [← map_pow, ← hb, ha₂res, hlc]
          let : CharZero (L ⊗[K] K₁) := charZero_of_injective_algebraMap (algebraMap L
            (L ⊗[K] K₁)).injective
          let : CharP (IsLocalRing.ResidueField B₁) p :=
            er.toRingHom.charP er.injective p
          obtain ⟨hfin₂, _, _, _, _, hcase⟩ :=
            isGalois_and_ramification_cases_of_adjoin_root_cyclotomic_quotient
              B₁ (L ⊗[K] K₁) (M ⊗[K] K₁) p f₁ P₁ hP₁ ξ₂ z₂ hPz₂ hz₂ tB htB
          obtain ⟨hR, hover, hram, hrest⟩ := hcase D.natDegree a₂ (by omega) (hDd'.symm ▸ hDdiv)
            ha₂notpow (by rw
              [ha₂, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ htBL), one_mul])
          let := hR
          let := hover
          let R := integralClosure B₁ (M ⊗[K] K₁)
          have : IsDiscreteValuationRing.IsExtension B₁ R :=
            isExtension_integralClosure (by
              rw [IsScalarTower.algebraMap_eq B₁ (L ⊗[K] K₁) (M ⊗[K] K₁)]
              exact (algebraMap (L ⊗[K] K₁) (M ⊗[K] K₁)).injective.comp
                (IsFractionRing.injective B₁ (L ⊗[K] K₁)))
          let : Module.IsTorsionFree B₁ R := Module.isTorsionFree_iff_algebraMap_injective.mpr
            (FaithfulSMul.algebraMap_injective B₁ R)
          have hBR : (IsLocalRing.maximalIdeal B₁).map (algebraMap B₁ R) =
            IsLocalRing.maximalIdeal R := by
            have hr : IsDiscreteValuationRing.ramificationIndex B₁ R = 1 := hram
            simpa only [hr, pow_one] using
              (IsDiscreteValuationRing.ramificationIndex_characterization B₁ R).2.1
          exact exists_isWeakSolution_of_unramified_normalization (A := A) (B := B) (C := C)
            (K := K) (L := L) (M := M) (E := K₁)
            z' hz' hL₁ hM₁ hA₁ hC₁ hfrac f' hmap' heB hR hBR
      · left
        let := hL₁.toField
        obtain ⟨φ⟩ := nonempty_algHom_of_cyclotomic_tensor_not_isField p f P hP.1 hwne
          hfinite.1 ξ' z' hz' hPz' hL₁ hM₁
        exact exists_isWeakSolution_of_tensor_embedding (A := A) (B := B) (C := C) z' hz'
          hL₁ hA₁ hC₁ hfrac (eB.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
          hmap' heB φ
    · have hallcore : ∀ i,
          H₀.coeff i ∈ perfectCore (IsLocalRing.ResidueField B) p := by
        simpa only [not_exists, not_not] using hbad
      have finish : MixedLevelStepReentry B C L M p f P
          (Stacks.DegreePExtensionLevel.extensionLevel B L M P π e he hne) π
          (H₀.support.image (fun i => H₀.coeff i)) := by
        intro A' K'
        intros
        rename_i hweak' πA' hπA' hπeq hsupport
        let ρ' := algebraMap (IsLocalRing.ResidueField A') (IsLocalRing.ResidueField B)
        have hall' : ∀ i, H₀.coeff i ∈ ρ'.range := by
          intro i
          by_cases hi : i ∈ H₀.support
          · exact hsupport (H₀.coeff i) (Finset.mem_image_of_mem _ hi)
          · have hzero : H₀.coeff i = 0 := by
              simpa only [Polynomial.mem_support_iff, not_not] using hi
            rw [hzero]
            exact ρ'.range.zero_mem
        have hmapmax' : (IsLocalRing.maximalIdeal A').map (algebraMap A' B) =
            IsLocalRing.maximalIdeal B := by
          simpa only
              [show IsDiscreteValuationRing.ramificationIndex A' B = 1 from hweak', pow_one] using
            (IsDiscreteValuationRing.ramificationIndex_characterization A' B).2.1
        let : Module.FaithfullyFlat A' B := Module.FaithfullyFlat.of_flat_of_isLocalHom
        have hcomap' : (IsLocalRing.maximalIdeal B ^ m).comap (algebraMap A' B) =
            IsLocalRing.maximalIdeal A' ^ m := by
          rw [← hmapmax', ← Ideal.map_pow, Ideal.comap_map_eq_self_of_faithfullyFlat]
        have hpmA' : (p : A') ∈ IsLocalRing.maximalIdeal A' ^ m := by
          rw [← hcomap']
          show algebraMap A' B (p : A') ∈ IsLocalRing.maximalIdeal B ^ m
          simpa only [map_natCast] using hpmB
        let QA' := A' ⧸ IsLocalRing.maximalIdeal A' ^ m
        let : Nontrivial QA' := Ideal.Quotient.nontrivial_iff.mpr
          (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A').ne_top
            (Ideal.pow_le_self hmpos.ne'))
        let qA' : A' →+* QA' := Ideal.Quotient.mk _
        let : IsLocalRing QA' :=
          IsLocalRing.of_surjective' qA' Ideal.Quotient.mk_surjective
        let : IsLocalHom qA' := IsLocalHom.of_surjective qA' Ideal.Quotient.mk_surjective
        obtain ⟨τq', hτq'⟩ := exists_residueField_section_quotient_pow A' m p hpmA'
        obtain ⟨τ', τbar', hτ', hτbar'⟩ :=
          exists_lift_residueField_section qA' Ideal.Quotient.mk_surjective τq' hτq'
        let qA'B : QA' →+* QB := Ideal.quotientMap _ (algebraMap A' B) (by rw [hcomap'])
        have hcompatible' : qA'B.comp τbar' = σbar.comp ρ' := by
          apply ringHom_eq_of_sub_mem_nilpotent_of_perfect p (IsLocalRing.maximalIdeal QB)
            (isNilpotent_maximalIdeal_quotient_pow B m)
          intro x
          have hdiff : algebraMap A' B (τ' x) - σ (ρ' x) ∈
              IsLocalRing.maximalIdeal B := by
            rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hσ]
            show IsLocalRing.residue B (algebraMap A' B (τ' x)) - ρ' x = 0
            rw [← IsLocalRing.ResidueField.map_residue, hτ']
            exact sub_self (ρ' x)
          have hdiffQ := map_nonunit qB _ hdiff
          show qA'B (τbar' x) - σbar (ρ' x) ∈ IsLocalRing.maximalIdeal QB
          rw [← hτbar', ← hσbar]
          show qB (algebraMap A' B (τ' x)) - qB (σ (ρ' x)) ∈
            IsLocalRing.maximalIdeal QB
          simpa only [map_sub] using hdiffQ
        have hπA'L : algebraMap A' L πA' ≠ 0 := by
          rw [IsScalarTower.algebraMap_apply A' B L, hπeq]
          exact hπL
        have hqA'B : qA'B.comp qA' = qB.comp (algebraMap A' B) := by ext; rfl
        have hker' : ∀ b : B, qB b = 0 ↔ (algebraMap A' B πA') ^ m ∣ b := by
          intro b
          rw [hπeq]
          exact hker b
        obtain ⟨aA, bA, haA⟩ := exists_scaled_parameter_eq_of_coefficients_descend
          qA' Ideal.Quotient.mk_surjective qB qA'B hqA'B ρ' τbar' σbar hcompatible'
          πA' hπA'L m n hker' H H₀ hH hHd hH₀d hall' ξ'
          (by rw [IsScalarTower.algebraMap_apply A' B L, hπeq]; exact hξ')
        let a' : B := algebraMap A' B aA + π ^ m * bA
        have ha' : algebraMap B L a' = algebraMap B L (π ^ n) * ξ' := by
          simpa only [a', map_add, map_mul, map_pow, IsScalarTower.algebraMap_apply A' B L,
            hπeq] using haA.symm
        have hau' : IsUnit a' := isUnit_of_isLeast_extensionLevelNumerator
          P π hπ n hnpos ⟨hnmem, fun _ hk => Nat.sInf_le hk⟩ ξ' z' a' hz'
          (by simpa only [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] using hPz') ha'
        have hres' : IsLocalRing.residue B a' = ρ' (IsLocalRing.residue A' aA) := by
          have hπres : IsLocalRing.residue B π = 0 := by
            rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq]
            exact Ideal.mem_span_singleton_self π
          dsimp only [a']
          rw [map_add, map_mul, map_pow, hπres, zero_pow (show m ≠ 0 from hmpos.ne'),
            zero_mul, add_zero, ← IsLocalRing.ResidueField.map_residue]
          rfl
        have haAu : IsUnit aA := by
          apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
          intro hzA
          have hzB := (IsLocalRing.residue_ne_zero_iff_isUnit a').mpr hau'
          exact hzB (by rw [hres', hzA, map_zero])
        have hpn : ¬p ∣ n := by
          intro hpn
          apply not_isPow_residue_of_isLeast_extensionLevelNumerator
            p f P hP.1 hP.2.2.2 π hπ e n hw hnpos hnbound
            ⟨hnmem, fun _ hk => Nat.sInf_le hk⟩ hpn ξ' z' a' hz' hPz'
            (by simpa only [map_pow] using ha')
          obtain ⟨c, hc⟩ :=
            (PerfectRing.bijective_frobenius (R := IsLocalRing.ResidueField A') (p := p)).2
              (IsLocalRing.residue A' aA)
          refine ⟨ρ' c, ?_⟩
          rw [hres', ← map_pow]
          exact congrArg ρ' hc.symm
        obtain ⟨K₁, hK₁, hK'K₁, hA'K₁, htower, hfinK₁, hsepK₁, htot, hdeg,
            y, hygen, hy⟩ :=
          exists_totallyRamified_root_pow_sub A' K' p (Fact.out : p.Prime).one_lt πA' (-aA)
            hπA' haAu.neg n hnpos ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpn)
        refine ⟨K₁, hK₁, hK'K₁, hA'K₁, htower, hfinK₁, hsepK₁, htot, ?_⟩
        obtain ⟨hL₁, hA₁, hBdom, hB₁, hinj, hmap, hCdom, hC₁, hfrac, eB, heB,
            hinj', hmap'⟩ :=
          IsDiscreteValuationRing.isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified
            A' B K' L K₁ hmapmax' htot
        by_cases hM₁ : IsField (M ⊗[K'] K₁)
        · right
          let := hL₁.toField
          let := hM₁.toField
          have hξA : algebraMap B L π ^ n * ξ' - algebraMap B L (algebraMap A' B aA) =
              algebraMap B L π ^ m * algebraMap B L bA := by
            have haA' := haA
            simp only [map_mul, map_pow, IsScalarTower.algebraMap_apply A' B L, hπeq] at haA'
            linear_combination haA'
          have hyT := artinSchreier_eq_tensor_includeRight πA' aA
            ((map_ne_zero_iff _ (IsFractionRing.injective A' K')).mpr hπA'.ne_zero)
            n p y hy hL₁
          have hyB : algebraMap B (L ⊗[K'] K₁) π ^ n *
              (((1 : L) ⊗ₜ[K'] y) ^ p - (1 : L) ⊗ₜ[K'] y) =
                -algebraMap B (L ⊗[K'] K₁) (algebraMap A' B aA) := by
            rw [← hπeq]
            calc
              algebraMap B (L ⊗[K'] K₁) (algebraMap A' B πA') ^ n *
                  (((1 : L) ⊗ₜ[K'] y) ^ p - (1 : L) ⊗ₜ[K'] y) =
                  algebraMap A' (L ⊗[K'] K₁) πA' ^ n *
                    (((1 : L) ⊗ₜ[K'] y) ^ p - (1 : L) ⊗ₜ[K'] y) := by
                    rw [IsScalarTower.algebraMap_apply A' B (L ⊗[K'] K₁)]
              _ = -algebraMap A' (L ⊗[K'] K₁) aA := hyT
              _ = -algebraMap B (L ⊗[K'] K₁) (algebraMap A' B aA) := by
                    rw [IsScalarTower.algebraMap_apply A' B (L ⊗[K'] K₁)]
          obtain ⟨hfin, hfl, π₁, e₁, he₁, hne₁, hπ₁, hw₁, hle⟩ :=
            finiteLevel_tensorProduct_of_artinSchreier_shift p f P hP hfinite.1 π hπ e n m
              he hw hnbound hme hmle (by dsimp [m]; omega) z' hz' ξ' hPz'
              (algebraMap A' B aA) bA hξA hL₁ hM₁ hC₁ hfrac (1 ⊗ₜ[K'] y) hyB
          exact ⟨hL₁, hM₁, hC₁, hfrac, hfin, hfl, π₁, e₁, he₁, hne₁, hπ₁, hw₁,
            hle.trans_eq hbound⟩
        · left
          let := hL₁.toField
          obtain ⟨φ⟩ := nonempty_algHom_of_cyclotomic_tensor_not_isField p f P hP.1 hwne
            hfinite.1 ξ' z' hz' hPz' hL₁ hM₁
          exact exists_isWeakSolution_of_tensor_embedding (A := A') (B := B) (C := C) z' hz'
            hL₁ hA₁ hC₁ hfrac
            (eB.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) hmap' heB φ
      by_cases hsupp : ∀ x ∈ H₀.support.image (fun i => H₀.coeff i), x ∈
          (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).fieldRange
      · exact Or.inl (finish A K hweak πA hπA rfl hsupp)
      · refine Or.inr ⟨H₀.support.image (fun i => H₀.coeff i), ?_, hsupp, ?_, finish⟩
        · intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          exact hallcore i
        · refine ⟨e, he, hne, hπ, hw, rfl, n, m, ξ', z', H, H₀, σbar, rQB,
            rfl, hnmem, ?_, hnpos, hnbound, rfl, hmpos, hmle, hme, ?_, hpmB, hbound,
            hz', hPz', hHd, hH₀d, ?_, ?_, ?_, rfl, hallcore, hξ'⟩
          · intro k hk
            exact Nat.sInf_le hk
          · dsimp only [m]
            omega
          · simpa only [qB] using hH
          · intro x
            rw [← hσbar x]
            exact hσ x
          · intro b
            rfl

/-- The traditional Tag 09F5 interface.  The global residue-field hypothesis identifies the
perfect core with the image of the base residue field, so the finite-support alternative in
`exists_totallyRamified_isWeakSolution_or_extensionLevel_le_or_finiteSupport_of_uniformizer` is
impossible. -/
@[stacks 09F5]
theorem exists_totallyRamified_isWeakSolution_or_extensionLevel_le
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra A M] [Algebra B M]
    [IsScalarTower A B C] [IsScalarTower A B L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K L]
    [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) [Fact p.Prime] [CharZero K]
    [CharP (IsLocalRing.ResidueField A) p]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    [Module.Finite L M]
    (hfinite : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P)
    (l : ℚ)
    (hlevel : ∃ (π : B) (e₁ : ℕ) (he₁ : 0 < e₁)
        (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B L M P π).Nonempty),
        Irreducible π ∧ Associated (wElt f) (π ^ e₁) ∧
          l = Stacks.DegreePExtensionLevel.extensionLevel B L M P π e₁ he₁ hne)
    (hl : 0 < l)
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁)
      (_ : Algebra.IsSeparable K K₁),
      IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K₁ ∧
        ((∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
            A C K M K₁, D.IsWeakSolution) ∨
          let L₁ := L ⊗[K] K₁
          let M₁ := M ⊗[K] K₁
          ∃ (hL₁ : IsField L₁) (hM₁ : IsField M₁),
            letI := hL₁.toField
            letI := hM₁.toField
            let ι : L₁ →ₐ[K] M₁ :=
              Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K K₁)
            letI : Algebra L₁ M₁ := ι.toRingHom.toAlgebra
            let B₁ := integralClosure B L₁
            ∃ (hB₁ : IsDiscreteValuationRing B₁) (hfrac : IsFractionRing B₁ L₁)
              (hfin : Module.Finite L₁ M₁),
              letI := hB₁
              letI := hfrac
              letI := hfin
              let f₁ := (algebraMap B B₁).comp f
              let P₁ := P.map (algebraMap B B₁)
              Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B₁ L₁ M₁ p f₁ P₁ ∧
                ∃ (π₁ : B₁) (e₁ : ℕ) (he₁ : 0 < e₁)
                  (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B₁ L₁ M₁ P₁
                    π₁).Nonempty),
                  Irreducible π₁ ∧ Associated (wElt f₁) (π₁ ^ e₁) ∧
                    Stacks.DegreePExtensionLevel.extensionLevel B₁ L₁ M₁ P₁ π₁ e₁ he₁ hne ≤
                      max 0 (max (l - 1) (2 * l - (p : ℚ)))) := by
  let ρ := algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  let : CharP (IsLocalRing.ResidueField B) p :=
    CharP.of_ringHom_of_ne_zero ρ p (Fact.out : p.Prime).ne_zero
  let : PerfectRing (IsLocalRing.ResidueField A) p :=
    perfectRing_of_range_eq_iInter_pow p ρ ρ.injective hresidue
  let : PerfectField (IsLocalRing.ResidueField A) :=
    PerfectRing.toPerfectField _ p
  obtain ⟨πA, hπA⟩ := IsDiscreteValuationRing.exists_irreducible A
  rcases exists_totallyRamified_isWeakSolution_or_extensionLevel_le_or_finiteSupport_of_uniformizer
      A B C K L M p hweak πA hπA f P hP hfinite l hlevel hl with
    h | ⟨s, hs, hmissing, _hprep, _hreentry⟩
  · simpa only [MixedLevelStepOutcome] using h
  · exfalso
    exact hmissing fun x hx ↦ (hresidue x).mpr (mem_perfectCore_iff_forall_one_le.mp (hs x hx))

end Stacks.DiscreteValuationRing.EppLevelInduction
