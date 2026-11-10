module

public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.LocalRing.ResidueSection
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.ScaledParameter

open Stacks.DiscreteValuationRing.AdjoinPthRoot

/-!
# Coefficient descent and Artin–Schreier shifts

Prepared coefficient descent across a weakly unramified square of discrete valuation rings,
finite level after an Artin–Schreier shift, and splitting of tensor products along embeddings.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u uA uK uL

open Polynomial

namespace Stacks.DiscreteValuationRing.EppLevelInduction

/-- Along a weakly unramified extension of DVRs, the maximal ideal extends to the maximal ideal. -/
private theorem map_maximalIdeal_eq_of_isWeaklyUnramified
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
    [IsDiscreteValuationRing.IsExtension A B] (h : IsDiscreteValuationRing.IsWeaklyUnramified A B) :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
  simpa only [show IsDiscreteValuationRing.ramificationIndex A B = 1 from h, pow_one] using
    (IsDiscreteValuationRing.ramificationIndex_characterization A B).2.1

/-- Along a weakly unramified extension of DVRs, powers of the maximal ideal contract back. -/
private theorem comap_maximalIdeal_pow_eq_of_isWeaklyUnramified
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
    [IsDiscreteValuationRing.IsExtension A B] (h : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (m : ℕ) :
    (IsLocalRing.maximalIdeal B ^ m).comap (algebraMap A B) = IsLocalRing.maximalIdeal A ^ m := by
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← map_maximalIdeal_eq_of_isWeaklyUnramified h, ← Ideal.map_pow,
    Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- The quotient of a local ring by a positive power of its maximal ideal is nontrivial. -/
private theorem nontrivial_quotient_maximalIdeal_pow
    (R : Type*) [CommRing R] [IsLocalRing R] {m : ℕ} (hm : 0 < m) :
    Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ m) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (Ideal.pow_le_self hm.ne'))

/-- **Prepared coefficient descent across a weakly-unramified DVR square.**

The source residue field may be imperfect, so its chosen lift into the truncated quotient need
not commute globally with base change.  It does commute on the perfect core: two lifts with the
same residue agree there by nilpotent uniqueness.  Consequently, after the finite support of the
prepared residue polynomial has been absorbed into the new base residue field, every mapped
quotient coefficient comes from the new base quotient.  The scaled parameter therefore descends
to the new base. -/
theorem exists_scaled_parameter_eq_of_mapped_dvr_preparation
    (A B0 B L : Type*)
    [CommRing A] [CommRing B0] [CommRing B]
    [IsDomain A] [IsDomain B0] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B0]
    [IsDiscreteValuationRing B] [Field L]
    [Algebra B0 B] [Algebra A B] [Algebra B L] [Algebra A L]
    [IsScalarTower A B L]
    [IsDiscreteValuationRing.IsExtension B0 B]
    [IsDiscreteValuationRing.IsExtension A B]
    [IsFractionRing B L]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField A) p]
    [ExpChar (IsLocalRing.ResidueField B0) p]
    [ExpChar (IsLocalRing.ResidueField B) p]
    [PerfectField (IsLocalRing.ResidueField A)]
    (hweak0 : IsDiscreteValuationRing.IsWeaklyUnramified B0 B)
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (pi : A) (hpi : Irreducible pi) (m n : ℕ) (hmpos : 0 < m)
    (hpm0 : (p : B0) ∈ IsLocalRing.maximalIdeal B0 ^ m)
    (H : Polynomial B0) (H0 : Polynomial (IsLocalRing.ResidueField B0))
    (sigma0 : IsLocalRing.ResidueField B0 →+*
      B0 ⧸ IsLocalRing.maximalIdeal B0 ^ m)
    (r0 : (B0 ⧸ IsLocalRing.maximalIdeal B0 ^ m) →+*
      IsLocalRing.ResidueField B0)
    (hr0sigma : ∀ x, r0 (sigma0 x) = x)
    (hr0q : ∀ b, r0 (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B0 ^ m) b) =
      IsLocalRing.residue B0 b)
    (hH : H.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B0 ^ m)) =
      H0.map sigma0)
    (hHd : H.natDegree ≤ n)
    (hcore : ∀ i, H0.coeff i ∈ perfectCore (IsLocalRing.ResidueField B0) p)
    (habs : ∀ x ∈ @Finset.image ℕ (IsLocalRing.ResidueField B0) (Classical.decEq _)
      (fun i => H0.coeff i) H0.support,
      IsLocalRing.ResidueField.map (algebraMap B0 B) x ∈
        (algebraMap (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B)).fieldRange)
    (xi : L)
    (hxi : ∃ b : B, algebraMap B L (algebraMap A B pi) ^ n *
        (xi - Polynomial.aeval (algebraMap B L (algebraMap A B pi))⁻¹
          (H.map (algebraMap B0 B))) =
      algebraMap B L ((algebraMap A B pi) ^ m * b)) :
    ∃ (a : A) (b : B), algebraMap A L pi ^ n * xi =
      algebraMap A L a + algebraMap B L ((algebraMap A B pi) ^ m * b) := by
  classical
  let g := algebraMap B0 B
  let r := IsLocalRing.ResidueField.map g
  let rho := algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  have hmap0 := map_maximalIdeal_eq_of_isWeaklyUnramified hweak0
  have hmap := map_maximalIdeal_eq_of_isWeaklyUnramified hweak
  have hcomap0 := comap_maximalIdeal_pow_eq_of_isWeaklyUnramified hweak0 m
  have hcomap := comap_maximalIdeal_pow_eq_of_isWeaklyUnramified hweak m
  have hpmB : (p : B) ∈ IsLocalRing.maximalIdeal B ^ m := by
    have hpmap := Ideal.mem_map_of_mem g hpm0
    rw [Ideal.map_pow, hmap0] at hpmap
    simpa only [map_natCast] using hpmap
  have hpmA : (p : A) ∈ IsLocalRing.maximalIdeal A ^ m := by
    rw [← hcomap]
    change algebraMap A B (p : A) ∈ IsLocalRing.maximalIdeal B ^ m
    simpa only [map_natCast] using hpmB
  let Q0 := B0 ⧸ IsLocalRing.maximalIdeal B0 ^ m
  let QA := A ⧸ IsLocalRing.maximalIdeal A ^ m
  let QB := B ⧸ IsLocalRing.maximalIdeal B ^ m
  let q0 : B0 →+* Q0 := Ideal.Quotient.mk _
  let qA : A →+* QA := Ideal.Quotient.mk _
  let qB : B →+* QB := Ideal.Quotient.mk _
  let : Nontrivial QA := nontrivial_quotient_maximalIdeal_pow A hmpos
  let : Nontrivial QB := nontrivial_quotient_maximalIdeal_pow B hmpos
  let : IsLocalRing QA := IsLocalRing.of_surjective' qA Ideal.Quotient.mk_surjective
  let : IsLocalRing QB := IsLocalRing.of_surjective' qB Ideal.Quotient.mk_surjective
  let : IsLocalHom qA := IsLocalHom.of_surjective qA Ideal.Quotient.mk_surjective
  let : IsLocalHom qB := IsLocalHom.of_surjective qB Ideal.Quotient.mk_surjective
  let psi : Q0 →+* QB := Ideal.quotientMap _ g (by rw [hcomap0])
  let iota : QA →+* QB := Ideal.quotientMap _ (algebraMap A B) (by rw [hcomap])
  have hq0 (b : B0) : psi (q0 b) = qB (g b) := rfl
  have hq (a : A) : iota (qA a) = qB (algebraMap A B a) := rfl
  let rQB : QB →+* IsLocalRing.ResidueField B :=
    Ideal.Quotient.lift _ (IsLocalRing.residue B) (by
      intro b hb
      exact (IsLocalRing.residue_eq_zero_iff b).mpr ((Ideal.pow_le_self hmpos.ne') hb))
  have hrQBq (b : B) : rQB (qB b) = IsLocalRing.residue B b := rfl
  have hrSquare : rQB.comp psi = r.comp r0 := by
    ext b
    change rQB (psi (q0 b)) = r (r0 (q0 b))
    rw [hq0, hrQBq, hr0q]
    exact (IsLocalRing.ResidueField.map_residue g b).symm
  let : CharP QB p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (by simpa only [map_natCast] using (Ideal.Quotient.eq_zero_iff_mem.mpr hpmB))
  obtain ⟨sigmaQ, hsigmaQ⟩ := exists_residueField_section_quotient_pow B m p hpmB
  obtain ⟨sigma, sigmabar, hsigma, hsigmabar⟩ :=
    exists_lift_residueField_section qB Ideal.Quotient.mk_surjective sigmaQ hsigmaQ
  obtain ⟨tauQ, htauQ⟩ := exists_residueField_section_quotient_pow A m p hpmA
  obtain ⟨tau, taubar, htau, htaubar⟩ :=
    exists_lift_residueField_section qA Ideal.Quotient.mk_surjective tauQ htauQ
  have hdiffQ (b c : B) (h : IsLocalRing.residue B b = IsLocalRing.residue B c) :
      qB b - qB c ∈ IsLocalRing.maximalIdeal QB := by
    have := map_nonunit qB _ ((IsLocalRing.residue_eq_zero_iff (b - c)).mp
      (by rw [map_sub, h, sub_self]))
    rwa [map_sub] at this
  have hsourceDiff : ∀ x,
      (sigmabar.comp r) x - (psi.comp sigma0) x ∈ IsLocalRing.maximalIdeal QB := by
    intro x
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((psi.comp sigma0) x)
    have hresb : IsLocalRing.residue B b = r x := by
      have hb' := congrArg rQB hb
      change IsLocalRing.residue B b = rQB (psi (sigma0 x)) at hb'
      have hs := DFunLike.congr_fun hrSquare (sigma0 x)
      change rQB (psi (sigma0 x)) = r (r0 (sigma0 x)) at hs
      rw [hr0sigma] at hs
      exact hb'.trans hs
    change sigmabar (r x) - psi (sigma0 x) ∈ IsLocalRing.maximalIdeal QB
    change qB b = psi (sigma0 x) at hb
    rw [← hsigmabar, ← hb]
    exact hdiffQ _ _ (by rw [hsigma, hresb])
  have hbaseDiff : ∀ x,
      (iota.comp taubar) x - (sigmabar.comp rho) x ∈
        IsLocalRing.maximalIdeal QB := by
    intro x
    change iota (taubar x) - sigmabar (rho x) ∈ IsLocalRing.maximalIdeal QB
    rw [← htaubar, ← hsigmabar, hq]
    refine hdiffQ _ _ ?_
    rw [hsigma, ← IsLocalRing.ResidueField.map_residue, htau]
    rfl
  have hsource (x : IsLocalRing.ResidueField B0)
      (hx : x ∈ perfectCore (IsLocalRing.ResidueField B0) p) :
      sigmabar (r x) = psi (sigma0 x) :=
    ringHom_eq_on_perfectCore_of_sub_mem_nilpotent p
      (IsLocalRing.maximalIdeal QB) (isNilpotent_maximalIdeal_quotient_pow B m)
      (sigmabar.comp r) (psi.comp sigma0) hsourceDiff hx
  have hbase (x : IsLocalRing.ResidueField A) :
      iota (taubar x) = sigmabar (rho x) :=
    ringHom_eq_on_perfectCore_of_sub_mem_nilpotent p
      (IsLocalRing.maximalIdeal QB) (isNilpotent_maximalIdeal_quotient_pow B m)
      (iota.comp taubar) (sigmabar.comp rho) hbaseDiff
      (mem_perfectCore_of_perfectRing (RingHom.id _) x)
  have hrel : (H.map g).map qB = H0.map (psi.comp sigma0) := by
    rw [Polynomial.map_map]
    rw [show qB.comp g = psi.comp q0 by ext b; rfl, ← Polynomial.map_map, hH,
      Polynomial.map_map]
  have hcoeff : ∀ i, ((H.map g).map qB).coeff i ∈ Set.range iota := by
    intro i
    rw [hrel, Polynomial.coeff_map]
    by_cases hi : i ∈ H0.support
    · obtain ⟨a, ha⟩ := habs (H0.coeff i) (Finset.mem_image_of_mem _ hi)
      refine ⟨taubar a, ?_⟩
      change iota (taubar a) = psi (sigma0 (H0.coeff i))
      rw [hbase, ha, hsource (H0.coeff i) (hcore i)]
    · have hzero : H0.coeff i = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hi
      rw [hzero, map_zero]
      exact ⟨0, map_zero iota⟩
  have hker (b : B) : qB b = 0 ↔ (algebraMap A B pi) ^ m ∣ b := by
    have hpimap : Irreducible (algebraMap A B pi) := by
      apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
      have h := hmap
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi,
        Ideal.map_span, Set.image_singleton] at h
      exact h.symm
    rw [Ideal.Quotient.eq_zero_iff_mem, hpimap.maximalIdeal_eq,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hpiL : algebraMap A L pi ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B L]
    simpa only [map_zero] using (IsFractionRing.injective B L).ne
      ((FaithfulSMul.algebraMap_injective A B).ne hpi.ne_zero)
  apply exists_scaled_parameter_eq_of_quotient_coefficients_descend
    qA Ideal.Quotient.mk_surjective qB iota (by ext a; rfl)
    pi hpiL m n hker (H.map g) (Polynomial.natDegree_map_le.trans hHd)
    hcoeff xi
  simpa only [IsScalarTower.algebraMap_apply A B L] using hxi

theorem irreducible_of_pow_eq_uniformizer_of_ramificationIndex
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B]
    (π : A) (hπ : Irreducible π) (t : B) (q : ℕ) (hq : 0 < q)
    (ht : t ^ q = algebraMap A B π) (he : IsDiscreteValuationRing.ramificationIndex A B = q) :
    Irreducible t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨v, hv⟩ := (IsDiscreteValuationRing.ramificationIndex_characterization A B).2.2.2 π hπ ϖ hϖ
  rw [he] at hv
  have ht0 : t ≠ 0 := by
    intro ht0
    have hπ0 : algebraMap A B π ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr hπ.ne_zero
    exact hπ0 (by rw [← ht, ht0, zero_pow hq.ne'])
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible ht0 hϖ
  have htk : IsDiscreteValuationRing.addVal B t = (k : ℕ∞) := by
    rw [← hϖ.addVal_pow k]
    exact (IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr hk
  have hqk : (q * k : ℕ) = q := by
    have hval : (q * k : ℕ∞) = (q : ℕ∞) := by
      calc
        (q * k : ℕ∞) = IsDiscreteValuationRing.addVal B (t ^ q) := by
          rw [IsDiscreteValuationRing.addVal_pow, htk, nsmul_eq_mul]
        _ = q := by rw [ht, hv]; exact IsDiscreteValuationRing.addVal_def' v hϖ q
    exact_mod_cast hval
  have hk1 : k = 1 := by nlinarith
  have hassoc : Associated t ϖ := by simpa only [hk1, pow_one] using hk
  exact hassoc.symm.irreducible hϖ

theorem intProp_map
    {A B : Type*} [CommRing A] [CommRing B]
    {p : ℕ} [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* A)
    (P : Polynomial A) (hP : intProp f P) (q : A →+* B) :
    intProp (q.comp f) (P.map q) := by
  have hw : wElt (q.comp f) = q (wElt f) := by
    simp only [wElt, zetaA, RingHom.comp_apply, map_sub, map_one]
  refine ⟨?_, Polynomial.natDegree_map_le.trans hP.2.1, ?_, ?_⟩
  · have h := congrArg (Polynomial.map q) hP.1
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
      Polynomial.map_add, Polynomial.map_one, Polynomial.map_C, Polynomial.map_X, hw] using h
  · rw [Polynomial.coeff_map, hP.2.2.1, map_zero]
  · intro i hi hip
    have h := congrArg q (hP.2.2.2 i hi hip)
    simpa only [map_mul, map_pow, map_natCast, Polynomial.coeff_map, hw] using h

theorem finite_finrank_adjoin_tensorProduct_of_isField
    {K L M K₁ : Type*} [Field K] [Field L] [Field M] [Field K₁]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] [Algebra K K₁]
    [Module.Finite L M]
    (hL₁ : IsField (L ⊗[K] K₁)) (z : M) (hz : Algebra.adjoin L {z} = ⊤) :
    letI := hL₁.toField
    let ι : L ⊗[K] K₁ →ₐ[K] M ⊗[K] K₁ :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K K₁)
    letI : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) := ι.toRingHom.toAlgebra
    Module.Finite (L ⊗[K] K₁) (M ⊗[K] K₁) ∧
      Module.finrank (L ⊗[K] K₁) (M ⊗[K] K₁) = Module.finrank L M ∧
      Algebra.adjoin (L ⊗[K] K₁) {z ⊗ₜ[K] (1 : K₁)} = ⊤ := by
  let := hL₁.toField
  intro ι
  let : Algebra (L ⊗[K] K₁) (M ⊗[K] K₁) := ι.toRingHom.toAlgebra
  let L₁ := L ⊗[K] K₁
  let M₁ := M ⊗[K] K₁
  have : IsScalarTower L L₁ M₁ := IsScalarTower.of_algebraMap_eq fun l => by
    change algebraMap L M l ⊗ₜ[K] (1 : K₁) = ι (algebraMap L L l ⊗ₜ[K] (1 : K₁))
    simp [ι]
  let e : L₁ ⊗[L] M ≃ₐ[L] M₁ :=
    (Algebra.TensorProduct.comm L L₁ M).trans
      (Algebra.TensorProduct.cancelBaseChange K L L M K₁)
  have he1 : ∀ m : M, e (1 ⊗ₜ m) = m ⊗ₜ[K] (1 : K₁) := by
    intro m
    change Algebra.TensorProduct.cancelBaseChange K L L M K₁ (m ⊗ₜ[L] (1 ⊗ₜ[K] 1)) = _
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  have he2 : ∀ x : L₁, e (x ⊗ₜ 1) = ι x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul l k =>
      change Algebra.TensorProduct.cancelBaseChange K L L M K₁ (1 ⊗ₜ[L] (l ⊗ₜ[K] k)) = _
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy => rw [TensorProduct.add_tmul, map_add, hx, hy, map_add]
  let eL : L₁ ⊗[L] M ≃ₗ[L₁] M₁ :=
    { e.toLinearEquiv with
      map_smul' := by
        intro x y
        change e (x • y) = ι x * e y
        rw [show x • y = (x ⊗ₜ[L] (1 : M)) * y by
          induction y using TensorProduct.inductionOn with
          | tmul a m =>
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul',
              smul_eq_mul]
          | add a b ha hb => rw [smul_add, mul_add, ha, hb]]
        rw [map_mul, he2] }
  have hbc : IsBaseChange L₁ (IsScalarTower.toAlgHom L M M₁).toLinearMap :=
    IsBaseChange.of_equiv eL fun m => he1 m
  have hrank : Module.finrank L₁ M₁ = Module.finrank L M := hbc.finrank_eq
  have hfin : Module.Finite L₁ M₁ :=
    Module.finite_of_finrank_pos (by rw [hrank]; exact Module.finrank_pos)
  refine ⟨hfin, hrank, ?_⟩
  let S := Algebra.adjoin L₁ ({z ⊗ₜ[K] (1 : K₁)} : Set M₁)
  have hM : ∀ m : M, m ⊗ₜ[K] (1 : K₁) ∈ S := by
    intro m
    have hm : m ∈ Algebra.adjoin L ({z} : Set M) := hz ▸ Algebra.mem_top
    induction hm using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap l =>
      have : algebraMap L M l ⊗ₜ[K] (1 : K₁) = algebraMap L₁ M₁ (l ⊗ₜ[K] (1 : K₁)) := by
        change _ = ι _
        simp [ι]
      rw [this]
      exact S.algebraMap_mem _
    | add x y _ _ hx hy =>
      rw [TensorProduct.add_tmul]
      exact S.add_mem hx hy
    | mul x y _ _ hx hy =>
      have : (x * y) ⊗ₜ[K] (1 : K₁) = (x ⊗ₜ[K] (1 : K₁)) * (y ⊗ₜ[K] (1 : K₁)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [this]
      exact S.mul_mem hx hy
  apply top_unique
  intro x _
  clear * - hM
  induction x using TensorProduct.inductionOn with
  | tmul m k =>
    have hk : m ⊗ₜ[K] k = algebraMap L₁ M₁ ((1 : L) ⊗ₜ[K] k) * (m ⊗ₜ[K] (1 : K₁)) := by
      change _ = ι _ * _
      simp [ι, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hk]
    exact S.mul_mem (S.algebraMap_mem _) (hM m)
  | add x y hx hy => exact S.add_mem hx hy

private theorem isField_iff_irreducible_minpoly_of_adjoin_eq_top
    {F R : Type*} [Field F] [CommRing R] [Algebra F R] (x : R)
    (hx : Algebra.adjoin F ({x} : Set R) = ⊤) :
    IsField R ↔ Irreducible (minpoly F x) := by
  let e : R ≃ₐ[F] AdjoinRoot (minpoly F x) :=
    (Subalgebra.topEquiv.symm.trans (Subalgebra.equivOfEq _ _ hx.symm)).trans
      (AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly F x)
  rw [← AdjoinRoot.isField_iff_irreducible]
  exact ⟨fun h => MulEquiv.isField h e.toMulEquiv.symm,
    fun h => MulEquiv.isField h e.toMulEquiv⟩

private theorem valuation_mul_pow_cyclotomic_add_le
    {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    (π w c ξ y E : F) (p e n m : ℕ)
    (hπ : v π ≤ 1) (hπ0 : v π ≠ 0) (hwv : v w = v π ^ e) (he : 0 < e) (hπ1 : v π < 1)
    (hme : m ≤ e) (hmn : m ≤ n) (hnm : n + m ≤ p * e)
    (hc : v c ≤ 1) (hξ : v (π ^ n * ξ - c) ≤ v π ^ m)
    (hy : π ^ n * (y ^ p - y) = -c)
    (hE : v (E - (y ^ p - y)) ≤ v w * max 1 (v E)) :
    v (π ^ (n - m) * (ξ + E + w ^ p * ξ * E)) ≤ 1 := by
  have hw1 : v w < 1 := by
    rw [hwv]; exact pow_lt_one₀ zero_le hπ1 he.ne'
  have hπn0 : v π ^ n ≠ 0 := pow_ne_zero _ hπ0
  have hT : v π ^ n * v (y ^ p - y) ≤ 1 := by
    have := congrArg v hy
    rw [map_mul, map_pow, Valuation.map_neg] at this
    rw [this]; exact hc
  have hEn : v π ^ n * v E ≤ 1 := by
    by_cases hV : v E ≤ 1
    · calc v π ^ n * v E ≤ 1 * 1 := mul_le_mul' (pow_le_one₀ zero_le hπ) hV
        _ = 1 := one_mul 1
    · have hV1 : 1 < v E := lt_of_not_ge hV
      have hmax : max 1 (v E) = v E := max_eq_right hV1.le
      rw [hmax] at hE
      have hlt : v w * v E < v E := by
        calc v w * v E < 1 * v E := by
              apply mul_lt_mul_of_pos_right hw1 (zero_lt_one.trans hV1)
          _ = v E := one_mul _
      have hle : v E ≤ v (y ^ p - y) := by
        have h1 : E = (E - (y ^ p - y)) + (y ^ p - y) := by ring
        by_contra hcon
        have hlt2 : v (y ^ p - y) < v E := lt_of_not_ge hcon
        have := v.map_add (E - (y ^ p - y)) (y ^ p - y)
        rw [← h1] at this
        have hEle : v E ≤ max (v w * v E) (v (y ^ p - y)) :=
          this.trans (max_le_max hE le_rfl)
        rcases le_max_iff.mp hEle with h | h
        · exact absurd h (not_le.mpr hlt)
        · exact absurd h (not_le.mpr hlt2)
      exact (mul_le_mul_right hle _).trans hT
  have hξn : v (π ^ n * ξ) ≤ 1 := by
    have h1 : π ^ n * ξ = (π ^ n * ξ - c) + c := by ring
    rw [h1]
    exact (v.map_add _ _).trans (max_le (hξ.trans (pow_le_one₀ zero_le hπ)) hc)
  have hX : v (π ^ n * (ξ + E + w ^ p * ξ * E)) ≤ v π ^ m := by
    have hsplit : π ^ n * (ξ + E + w ^ p * ξ * E) =
        (π ^ n * ξ - c) + (π ^ n * (E - (y ^ p - y)) + w ^ p * (π ^ n * ξ) * E) := by
      linear_combination (1 : F) * hy
    rw [hsplit]
    refine (v.map_add _ _).trans (max_le hξ ((v.map_add _ _).trans (max_le ?_ ?_)))
    · rw [map_mul, map_pow]
      calc v π ^ n * v (E - (y ^ p - y)) ≤ v π ^ n * (v w * max 1 (v E)) :=
            mul_le_mul_right hE _
        _ = v w * max (v π ^ n) (v π ^ n * v E) := by
            rw [mul_left_comm, mul_max, mul_one]
        _ ≤ v w * 1 := mul_le_mul_right (max_le (pow_le_one₀ zero_le hπ) hEn) _
        _ = v π ^ e := by rw [mul_one, hwv]
        _ ≤ v π ^ m := pow_le_pow_right_of_le_one' hπ hme
    · rw [map_mul, map_mul, map_pow, hwv, ← pow_mul]
      have hsplit2 : v π ^ (e * p) = v π ^ (e * p - n) * v π ^ n := by
        rw [← pow_add]; congr 1; rw [Nat.mul_comm]; omega
      rw [hsplit2]
      calc v π ^ (e * p - n) * v π ^ n * v (π ^ n * ξ) * v E
          = v π ^ (e * p - n) * v (π ^ n * ξ) * (v π ^ n * v E) := by rw [mul_right_comm _
            (v π ^ n), mul_assoc _ (v π ^ n), mul_comm (v π ^ n) (v E), ← mul_assoc, mul_assoc _ (v
              E), mul_comm (v E)]
        _ ≤ v π ^ (e * p - n) * 1 * 1 := by
            gcongr
        _ ≤ v π ^ m := by
            rw [mul_one, mul_one]
            exact pow_le_pow_right_of_le_one' hπ (by rw [Nat.mul_comm]; omega)
  have hsplit3 : π ^ n = π ^ m * π ^ (n - m) := by rw [← pow_add]; congr 1; omega
  rw [hsplit3, mul_assoc, map_mul, map_pow] at hX
  have hπm : v π ^ m ≠ 0 := pow_ne_zero _ hπ0
  have := (mul_le_mul_iff_right₀ (show 0 < v π ^ m from zero_lt_iff.mpr hπm)).mp
    (hX.trans_eq (mul_one _).symm)
  exact this

theorem wElt_comp {A B : Type*} [CommRing A] [CommRing B] {p : ℕ} [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* A) (q : A →+* B) : wElt (q.comp f) = q (wElt f) := by
  simp only [wElt, zetaA, RingHom.comp_apply, map_sub, map_one]

theorem eval₂_tensor_includeLeft
    {R K M E : Type*} [CommRing R] [Field K] [CommRing M] [CommRing E]
    [Algebra K M] [Algebra K E] (P : Polynomial R) (f : R →+* M) (z : M) :
    Polynomial.eval₂ (Algebra.TensorProduct.includeLeftRingHom.comp f)
      (z ⊗ₜ[K] (1 : E)) P =
        Polynomial.eval₂ f z P ⊗ₜ[K] (1 : E) :=
  (Polynomial.hom_eval₂ P f Algebra.TensorProduct.includeLeftRingHom z).symm
private theorem not_isUnit_integralClosure_algebraMap
    {B L E : Type*} [CommRing B] [IsDomain B]
    [Field L] [CommRing E] [Nontrivial E]
    [Algebra B L] [IsFractionRing B L] [Algebra L E]
    [Algebra B E] [IsScalarTower B L E] (π : B) (hπ : ¬IsUnit π) :
    ¬IsUnit (algebraMap B (integralClosure B E) π) := by
  let : FaithfulSMul B E := (faithfulSMul_iff_algebraMap_injective B E).mpr (by
    rw [IsScalarTower.algebraMap_eq B L E]
    exact (algebraMap L E).injective.comp (IsFractionRing.injective B L))
  let : FaithfulSMul B (integralClosure B E) :=
    (faithfulSMul_iff_algebraMap_injective B (integralClosure B E)).mpr (by
      apply Function.Injective.of_comp (f := algebraMap (integralClosure B E) E)
      rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq B (integralClosure B E) E]
      exact FaithfulSMul.algebraMap_injective B E)
  let : Algebra.IsIntegral B (integralClosure B E) := IsIntegralClosure.isIntegral_algebra B E
  exact fun h => hπ ((isUnit_map_iff (algebraMap B (integralClosure B E)) π).mp h)

private theorem surjective_algebraMap_of_isLocalHom_of_valuationRing
    {R S E : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [Field E] [Algebra R S] [Algebra R E] [Algebra S E]
    [IsScalarTower R S E] [IsFractionRing R E] [IsLocalHom (algebraMap R S)]
    (hS : Function.Injective (algebraMap S E)) :
    Function.Surjective (algebraMap R S) := by
  intro s
  let v := ValuationRing.valuation R E
  by_cases hs : v (algebraMap S E s) ≤ 1
  · obtain ⟨r, hr⟩ := (ValuationRing.mem_integer_iff R E _).mp hs
    exact ⟨r, hS (by rw [← IsScalarTower.algebraMap_apply R S E, hr])⟩
  · have hpos : 1 < v (algebraMap S E s) := lt_of_not_ge hs
    have hs0 : algebraMap S E s ≠ 0 := by
      intro h0
      simp only [h0, map_zero] at hpos
      exact (not_lt_of_ge zero_le) hpos
    have hinv : v ((algebraMap S E s)⁻¹) ≤ 1 := by
      rw [map_inv₀]
      exact (inv_le_one₀ (zero_lt_one.trans hpos)).mpr hpos.le
    obtain ⟨r, hr⟩ := (ValuationRing.mem_integer_iff R E _).mp hinv
    have hmul : algebraMap R S r * s = 1 := hS (by
      rw [map_mul, ← IsScalarTower.algebraMap_apply R S E, hr,
        inv_mul_cancel₀ hs0, map_one])
    obtain ⟨u, hu⟩ := (isUnit_map_iff (algebraMap R S) r).mp
      (IsUnit.of_mul_eq_one s hmul)
    refine ⟨↑u⁻¹, ?_⟩
    apply hS
    rw [← IsScalarTower.algebraMap_apply R S E]
    rw [map_units_inv, hu, hr, inv_inv]

theorem isIntegral_of_isDiscreteValuationRing_integralClosure
    {B C M E : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C]
    [Field M] [Field E] [Algebra B C] [FaithfulSMul B C] [IsLocalHom (algebraMap B C)]
    [Algebra C M] [IsFractionRing C M] [Algebra M E]
    [Algebra C E] [IsScalarTower C M E] [Algebra B E] [IsScalarTower B C E]
    [IsDiscreteValuationRing (integralClosure B E)]
    [IsFractionRing (integralClosure B E) E] : Algebra.IsIntegral B C := by
  have hCE : Function.Injective (algebraMap C E) := by
    rw [IsScalarTower.algebraMap_eq C M E]
    exact (algebraMap M E).injective.comp (IsFractionRing.injective C M)
  have hBE : Function.Injective (algebraMap B E) := by
    rw [IsScalarTower.algebraMap_eq B C E]
    exact hCE.comp (FaithfulSMul.algebraMap_injective B C)
  let R := integralClosure B E
  let T := integralClosure C E
  let φ : R →+* T :=
    { toFun := fun x => ⟨x.1, x.2.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Algebra R T := φ.toAlgebra
  have : IsScalarTower R T E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπC : ¬IsUnit (algebraMap B C π) :=
    fun h => hπ.not_isUnit ((isUnit_map_iff (algebraMap B C) π).mp h)
  have hπT : ¬IsUnit (algebraMap C T (algebraMap B C π)) :=
    not_isUnit_integralClosure_algebraMap (L := M) _ hπC
  have hπR0 : algebraMap B R π ≠ 0 := by
    intro h0
    have h0' : algebraMap B E π = 0 := congrArg Subtype.val h0
    exact ((map_ne_zero_iff _ hBE).mpr hπ.ne_zero) h0'
  have hsquare (b : B) : φ (algebraMap B R b) = algebraMap C T (algebraMap B C b) :=
    Subtype.ext (IsScalarTower.algebraMap_apply B C E b)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨d, hd⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπR0 hϖ
  have hϖT : ¬IsUnit (φ ϖ) := by
    intro hunit
    apply hπT
    rw [← hsquare π]
    exact ((hd.map φ).isUnit_iff).mpr (by simpa only [map_pow] using hunit.pow d)
  have : IsLocalHom φ := ⟨fun x hx => by
    by_contra hnot
    have hdiv : ϖ ∣ x := by
      rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
      exact hnot
    exact hϖT (isUnit_of_dvd_unit (map_dvd φ hdiv) hx)⟩
  have hsurj : Function.Surjective φ :=
    surjective_algebraMap_of_isLocalHom_of_valuationRing
      (R := R) (S := T) (E := E) Subtype.val_injective
  refine ⟨fun c => ?_⟩
  obtain ⟨r, hr⟩ := hsurj (algebraMap C T c)
  have hr' : (r : E) = algebraMap C E c := congrArg Subtype.val hr
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom B C E) hCE).mp (hr' ▸ r.2)

private theorem finiteLevel_of_artinSchreier_shift
    {B B₁ L₁ M₁ : Type u} [CommRing B] [IsDomain B] [CommRing B₁] [IsDomain B₁]
    [IsDiscreteValuationRing B₁] [Field L₁] [Field M₁]
    [Algebra B B₁] [Algebra B₁ L₁] [Algebra B L₁] [IsScalarTower B B₁ L₁]
    [IsFractionRing B₁ L₁] [Algebra L₁ M₁] [Module.Finite L₁ M₁]
    (p : ℕ) [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (hdeg : Module.finrank L₁ M₁ = p)
    (π : B) (e n m : ℕ) (he : 0 < e) (hw : Associated (wElt f) (π ^ e))
    (hπu : ¬IsUnit (algebraMap B B₁ π)) (hπ0 : algebraMap B B₁ π ≠ 0)
    (hn : n < p * e) (hme : m ≤ e) (hmn : m ≤ n) (hnm : n + m ≤ p * e)
    (Z : M₁) (hZ : Algebra.adjoin L₁ ({Z} : Set M₁) = ⊤) (ξ : L₁)
    (hPZ : Polynomial.eval₂ ((algebraMap L₁ M₁).comp (algebraMap B L₁)) Z P =
      algebraMap L₁ M₁ ξ)
    (c b : B₁)
    (hξ : algebraMap B L₁ π ^ n * ξ - algebraMap B₁ L₁ c =
      algebraMap B L₁ π ^ m * algebraMap B₁ L₁ b)
    (y : L₁) (hy : algebraMap B L₁ π ^ n * (y ^ p - y) = -algebraMap B₁ L₁ c) :
    Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B₁ L₁ M₁ p ((algebraMap B B₁).comp
      f)
        (P.map (algebraMap B B₁)) ∧
      ∃ (π₁ : B₁) (e₁ : ℕ) (he₁ : 0 < e₁)
        (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B₁ L₁ M₁
          (P.map (algebraMap B B₁)) π₁).Nonempty),
        Irreducible π₁ ∧ Associated (wElt ((algebraMap B B₁).comp f)) (π₁ ^ e₁) ∧
          Stacks.DegreePExtensionLevel.extensionLevel B₁ L₁ M₁ (P.map (algebraMap B B₁)) π₁ e₁ he₁
            hne ≤
            ((n - m : ℕ) : ℚ) / e := by
  classical
  let v := ValuationRing.valuation B₁ L₁
  have hvB₁ : ∀ x : B₁, v (algebraMap B₁ L₁ x) ≤ 1 := fun x =>
    (ValuationRing.mem_integer_iff B₁ L₁ _).mpr ⟨x, rfl⟩
  have hvB : ∀ x : B, v (algebraMap B L₁ x) ≤ 1 := fun x => by
    rw [IsScalarTower.algebraMap_apply B B₁ L₁]; exact hvB₁ _
  set πL := algebraMap B L₁ π with hπL
  have hπLeq : πL = algebraMap B₁ L₁ (algebraMap B B₁ π) :=
    IsScalarTower.algebraMap_apply B B₁ L₁ π
  have hvπ0 : v πL ≠ 0 := by
    rw [Valuation.ne_zero_iff, hπLeq]
    exact (map_ne_zero_iff _ (IsFractionRing.injective B₁ L₁)).mpr hπ0
  have hvπ1 : v πL < 1 := by
    rw [hπLeq]
    refine lt_of_le_of_ne (hvB₁ _) (fun h1 => hπu ?_)
    set x := algebraMap B B₁ π
    have hx0 : algebraMap B₁ L₁ x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective B₁ L₁)).mpr hπ0
    have hinv : v (algebraMap B₁ L₁ x)⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
    obtain ⟨b, hb⟩ := (ValuationRing.mem_integer_iff B₁ L₁ _).mp hinv
    refine IsUnit.of_mul_eq_one (b := b) (IsFractionRing.injective B₁ L₁ ?_)
    rw [map_mul, hb, mul_inv_cancel₀ hx0, map_one]
  obtain ⟨u, hu⟩ := hw
  have hvu : v (algebraMap B L₁ (u : B)) = 1 := by
    have h1 := hvB (u : B)
    have h2 := hvB ((u⁻¹ : Bˣ) : B)
    have h3 : v (algebraMap B L₁ (u : B)) * v (algebraMap B L₁ ((u⁻¹ : Bˣ) : B)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    by_contra hne
    have hlt := lt_of_le_of_ne h1 hne
    have : v (algebraMap B L₁ (u : B)) * v (algebraMap B L₁ ((u⁻¹ : Bˣ) : B)) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    exact this.ne h3
  set wL := algebraMap B L₁ (wElt f) with hwL
  have hwv : v wL = v πL ^ e := by
    have : wL * algebraMap B L₁ (u : B) = πL ^ e := by
      rw [hwL, hπL, ← map_mul, hu, map_pow]
    have := congrArg v this
    rwa [map_mul, hvu, mul_one, map_pow] at this
  let : Algebra B M₁ := ((algebraMap L₁ M₁).comp (algebraMap B L₁)).toAlgebra
  have : IsScalarTower B L₁ M₁ := IsScalarTower.of_algebraMap_eq' rfl
  set E := Polynomial.aeval y P with hEdef
  have hE := valuation_aeval_cyclotomic_error v hvB f P hP.1 hP.2.2.1 y
  have hc : v (algebraMap B₁ L₁ c) ≤ 1 := hvB₁ c
  have hξv : v (πL ^ n * ξ - algebraMap B₁ L₁ c) ≤ v πL ^ m := by
    rw [hξ, map_mul, map_pow]
    exact (mul_le_mul_right (hvB₁ b) _).trans_eq (mul_one _)
  have hmain := valuation_mul_pow_cyclotomic_add_le v πL wL (algebraMap B₁ L₁ c) ξ y E p e n m
    (le_of_lt hvπ1) hvπ0 hwv he hvπ1 hme hmn hnm hc hξv hy hE
  obtain ⟨b', hb'⟩ := (ValuationRing.mem_integer_iff B₁ L₁ _).mp hmain
  have hwy : 1 + wL * y ≠ 0 := by
    intro h0
    have hy' : y = -wL⁻¹ := by
      have hw0 : wL ≠ 0 := by
        intro hw0; rw [hw0, zero_mul, add_zero] at h0; exact one_ne_zero h0
      field_simp; linear_combination h0
    have hvy : v y = (v πL ^ e)⁻¹ := by rw [hy', Valuation.map_neg, map_inv₀, hwv]
    have hvπe : v πL ^ e < 1 := pow_lt_one₀ zero_le hvπ1 he.ne'
    have hvy1 : 1 < v y := by rw [hvy]; exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr (pow_ne_zero _
      hvπ0), hvπe⟩
    have hvyp : v (y ^ p - y) = v y ^ p := by
      rw [Valuation.map_sub_eq_of_lt_left, map_pow]
      rw [map_pow]
      calc v y = v y ^ 1 := (pow_one _).symm
        _ < v y ^ p := pow_lt_pow_right₀ hvy1 (Fact.out : p.Prime).one_lt
    have hcv := congrArg v hy
    rw [Valuation.map_neg, map_mul, map_pow, hvyp, hvy, inv_pow, ← pow_mul] at hcv
    have hlt : 1 < v πL ^ n * (v πL ^ (e * p))⁻¹ := by
      have hsp : v πL ^ (e * p) = v πL ^ n * v πL ^ (e * p - n) := by
        rw [← pow_add]; congr 1; rw [Nat.mul_comm]; omega
      rw [hsp, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hvπ0), one_mul]
      exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr (pow_ne_zero _ hvπ0),
        pow_lt_one₀ zero_le hvπ1 (by rw [Nat.mul_comm]; omega)⟩
    rw [hcv] at hlt
    exact absurd hc (not_le.mpr hlt)
  set Y := algebraMap L₁ M₁ y
  set Z' := algebraMap L₁ M₁ (1 + wL * y) * Z + algebraMap L₁ M₁ y
  have hZ' : Algebra.adjoin L₁ ({Z'} : Set M₁) = ⊤ := adjoin_affine_eq_top _ _ hwy Z hZ
  have hZ'eq : Z' = Z + Y + algebraMap B M₁ (wElt f) * Z * Y := by
    simp only [Z', Y, map_add, map_one, map_mul, IsScalarTower.algebraMap_apply B L₁ M₁, wL]
    ring
  have hPZ' : Polynomial.aeval Z' P = algebraMap L₁ M₁ (ξ + E + wL ^ p * ξ * E) := by
    rw [hZ'eq, aeval_cyclotomic_add f P hP.2.2.2]
    have h1 : Polynomial.aeval Z P = algebraMap L₁ M₁ ξ := hPZ
    have h2 : Polynomial.aeval Y P = algebraMap L₁ M₁ E := by
      simp only [Y, E, Polynomial.aeval_algebraMap_apply]
    rw [h1, h2]
    simp only [map_add, map_mul, map_pow, IsScalarTower.algebraMap_apply B L₁ M₁, wL]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B₁
  obtain ⟨d, hd⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hϖ
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, pow_zero] at hd; exact absurd (associated_one_iff_isUnit.mp hd) hπu
    · exact h0
  have hwB₁ : Associated (wElt ((algebraMap B B₁).comp f)) ((algebraMap B B₁ π) ^ e) := by
    rw [wElt_comp, ← map_pow]; exact ⟨Units.map (algebraMap B B₁).toMonoidHom u, by
      simp [← map_mul, hu]⟩
  have hPmap : Polynomial.eval₂ ((algebraMap L₁ M₁).comp (algebraMap B₁ L₁)) Z'
      (P.map (algebraMap B B₁)) = algebraMap L₁ M₁ (ξ + E + wL ^ p * ξ * E) := by
    rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq B B₁ L₁,
      ← hPZ', Polynomial.aeval_def]
    rfl
  have hb'' : algebraMap B₁ L₁ b' =
      algebraMap B₁ L₁ ((algebraMap B B₁ π) ^ (n - m)) * (ξ + E + wL ^ p * ξ * E) := by
    rw [hb', map_pow, ← hπLeq]
  obtain ⟨hfin, π₁, e₁, he₁, hne, hπ₁, hw₁, hle⟩ :=
    isDegreePExtensionOfFiniteLevel_and_extensionLevel_le_of_associated_pow B₁ L₁ M₁ p
      ((algebraMap B B₁).comp f) (P.map (algebraMap B B₁)) (algebraMap B B₁ π) ϖ hϖ d e (n - m)
      hdpos he hd hwB₁ hdeg _ Z' hZ' hPmap b' hb'' (by omega)
  exact ⟨hfin, π₁, e₁, he₁, hne, hπ₁, hw₁, hle⟩

theorem finiteLevel_tensorProduct_of_artinSchreier_shift
    {B K L M E : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Algebra K E] [Algebra B L] [IsFractionRing B L]
    [Algebra B M] [IsScalarTower B L M] [Module.Finite L M]
    (p : ℕ) [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    (hdeg : Module.finrank L M = p)
    (π : B) (hπ : Irreducible π) (e n m : ℕ)
    (he : 0 < e) (hw : Associated (wElt f) (π ^ e))
    (hn : n < p * e) (hme : m ≤ e) (hmn : m ≤ n) (hnm : n + m ≤ p * e)
    (z : M) (hz : Algebra.adjoin L {z} = ⊤) (ξ : L)
    (hPz : Polynomial.aeval z P = algebraMap L M ξ)
    (a b : B) (hξ : algebraMap B L π ^ n * ξ - algebraMap B L a =
      algebraMap B L π ^ m * algebraMap B L b)
    (hL : IsField (L ⊗[K] E)) (hM : IsField (M ⊗[K] E)) :
    letI := hL.toField
    letI := hM.toField
    let ι : L ⊗[K] E →ₐ[K] M ⊗[K] E :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K E)
    letI : Algebra (L ⊗[K] E) (M ⊗[K] E) := ι.toRingHom.toAlgebra
    let B₁ := integralClosure B (L ⊗[K] E)
    ∀ (hB : IsDiscreteValuationRing B₁) (hfrac : IsFractionRing B₁ (L ⊗[K] E)),
      letI := hB
      letI := hfrac
      ∀ y : L ⊗[K] E,
        algebraMap B (L ⊗[K] E) π ^ n * (y ^ p - y) =
          -algebraMap B (L ⊗[K] E) a →
        ∃ hfin : Module.Finite (L ⊗[K] E) (M ⊗[K] E),
          letI := hfin
          Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B₁ (L ⊗[K] E) (M ⊗[K] E) p
            ((algebraMap B B₁).comp f) (P.map (algebraMap B B₁)) ∧
          ∃ (π₁ : B₁) (e₁ : ℕ) (he₁ : 0 < e₁)
            (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators B₁ (L ⊗[K] E) (M ⊗[K] E)
              (P.map (algebraMap B B₁)) π₁).Nonempty),
            Irreducible π₁ ∧ Associated (wElt ((algebraMap B B₁).comp f)) (π₁ ^ e₁) ∧
              Stacks.DegreePExtensionLevel.extensionLevel B₁ (L ⊗[K] E) (M ⊗[K] E)
                (P.map (algebraMap B B₁)) π₁ e₁ he₁ hne ≤ ((n - m : ℕ) : ℚ) / e := by
  let := hL.toField
  let := hM.toField
  intro ι
  let : Algebra (L ⊗[K] E) (M ⊗[K] E) := ι.toRingHom.toAlgebra
  intro B₁ hB hfrac
  let := hB
  let := hfrac
  intro y hy
  obtain ⟨hfin, hdim, hgen⟩ := finite_finrank_adjoin_tensorProduct_of_isField hL z hz
  let := hfin
  let iL : L →+* L ⊗[K] E := Algebra.TensorProduct.includeLeftRingHom
  let iM : M →+* M ⊗[K] E := Algebra.TensorProduct.includeLeftRingHom
  have hsquare : (algebraMap (L ⊗[K] E) (M ⊗[K] E)).comp iL =
      iM.comp (algebraMap L M) := by
    ext x
    change ι (x ⊗ₜ[K] (1 : E)) = algebraMap L M x ⊗ₜ[K] (1 : E)
    simp [ι]
  have hcoeff : (algebraMap (L ⊗[K] E) (M ⊗[K] E)).comp
      (algebraMap B (L ⊗[K] E)) = iM.comp (algebraMap B M) := by
    rw [IsScalarTower.algebraMap_eq B L (L ⊗[K] E),
      show algebraMap L (L ⊗[K] E) = iL from rfl, ← RingHom.comp_assoc, hsquare,
        RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq B L M]
  have hPZ : Polynomial.eval₂ ((algebraMap (L ⊗[K] E) (M ⊗[K] E)).comp
      (algebraMap B (L ⊗[K] E))) (z ⊗ₜ[K] (1 : E)) P =
        algebraMap (L ⊗[K] E) (M ⊗[K] E) (iL ξ) := by
    rw [hcoeff, eval₂_tensor_includeLeft]
    change iM (Polynomial.aeval z P) = _
    rw [hPz]
    exact (DFunLike.congr_fun hsquare ξ).symm
  have hξ' : algebraMap B (L ⊗[K] E) π ^ n * iL ξ -
      algebraMap B₁ (L ⊗[K] E) (algebraMap B B₁ a) =
      algebraMap B (L ⊗[K] E) π ^ m *
        algebraMap B₁ (L ⊗[K] E) (algebraMap B B₁ b) := by
    simpa only [← IsScalarTower.algebraMap_apply B B₁ (L ⊗[K] E), map_sub, map_mul,
      map_pow, show iL = algebraMap L (L ⊗[K] E) from rfl,
      ← IsScalarTower.algebraMap_apply B L (L ⊗[K] E)] using congrArg iL hξ
  have hπu : ¬IsUnit (algebraMap B B₁ π) :=
    not_isUnit_integralClosure_algebraMap (L := L) π hπ.not_isUnit
  have hπ0 : algebraMap B B₁ π ≠ 0 := by
    intro h0
    have h0' := congrArg (algebraMap B₁ (L ⊗[K] E)) h0
    rw [map_zero, ← IsScalarTower.algebraMap_apply B B₁ (L ⊗[K] E),
      IsScalarTower.algebraMap_apply B L (L ⊗[K] E)] at h0'
    exact hπ.ne_zero (IsFractionRing.injective B L ((algebraMap L (L ⊗[K] E)).injective
      (by simpa only [map_zero] using h0')))
  refine ⟨hfin, ?_⟩
  exact finiteLevel_of_artinSchreier_shift p f P hP (hdim.trans hdeg) π e n m he hw
    hπu hπ0 hn hme hmn hnm _ hgen (iL ξ) hPZ (algebraMap B B₁ a)
    (algebraMap B B₁ b) hξ' y (by
      simpa only [← IsScalarTower.algebraMap_apply B B₁ (L ⊗[K] E)] using hy)

theorem artinSchreier_eq_tensor_includeRight
    {A K L E : Type*} [CommRing A] [Field K] [Field L] [Field E]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    (π a : A) (hπ : algebraMap A K π ≠ 0) (n p : ℕ) (y : E)
    (hy : y ^ p - y = algebraMap K E
      ((algebraMap A K π)⁻¹ ^ n * algebraMap A K (-a)))
    (hL : IsField (L ⊗[K] E)) :
    letI := hL.toField
    algebraMap A (L ⊗[K] E) π ^ n *
      (((1 : L) ⊗ₜ[K] y) ^ p - (1 : L) ⊗ₜ[K] y) =
        -algebraMap A (L ⊗[K] E) a := by
  let := hL.toField
  let iR : E →ₐ[K] L ⊗[K] E := Algebra.TensorProduct.includeRight
  have hπ' : algebraMap A (L ⊗[K] E) π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K (L ⊗[K] E)]
    simpa only [map_zero] using (algebraMap K (L ⊗[K] E)).injective.ne hπ
  have hy' := congrArg iR hy
  simp only [map_sub, map_pow, AlgHom.commutes, map_mul, map_inv₀,
    ← IsScalarTower.algebraMap_apply A K (L ⊗[K] E), map_neg] at hy'
  change algebraMap A (L ⊗[K] E) π ^ n * ((iR y) ^ p - iR y) = _
  rw [hy', ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hπ', one_pow, one_mul]

theorem exists_tensorProduct_pi_algEquiv_of_embedding
    {K L M E : Type u} [Field K] [Field L] [Field M] [Field E]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Algebra K E] [Module.Finite L M] [IsGalois L M]
    (z : M) (hz : Algebra.adjoin L {z} = ⊤) (hL : IsField (L ⊗[K] E)) :
    letI := hL.toField
    ∀ φ : M →ₐ[L] L ⊗[K] E,
    let ι : L ⊗[K] E →ₐ[K] M ⊗[K] E :=
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M) (AlgHom.id K E)
    letI : Algebra (L ⊗[K] E) (M ⊗[K] E) := ι.toRingHom.toAlgebra
    ∃ e : M ⊗[K] E ≃ₐ[L ⊗[K] E] ((M ≃ₐ[L] M) → L ⊗[K] E),
      ∀ (m : M) (a : E) (σ : M ≃ₐ[L] M), e (m ⊗ₜ[K] a) σ = φ (σ m) * (1 ⊗ₜ[K] a) := by
  classical
  let := hL.toField
  intro φ ι
  let : Algebra (L ⊗[K] E) (M ⊗[K] E) := ι.toRingHom.toAlgebra
  let F := L ⊗[K] E
  let T := M ⊗[K] E
  let I := M ≃ₐ[L] M
  let := Fintype.ofFinite I
  let H : T →ₐ[K] (I → F) := Algebra.TensorProduct.lift
    (AlgHom.pi fun σ : I => (φ.comp σ.toAlgHom).restrictScalars K)
    (AlgHom.pi fun _ : I => (Algebra.TensorProduct.includeRight : E →ₐ[K] F))
    (fun _ _ => Commute.all _ _)
  have htmul (m : M) (a : E) (σ : I) :
      H (m ⊗ₜ[K] a) σ = φ (σ m) * (1 ⊗ₜ[K] a) := by
    rfl
  let H' : T →ₐ[F] (I → F) :=
    { H.toRingHom with
      commutes' := by
        intro x
        change H (ι x) = _
        induction x using TensorProduct.inductionOn with
        | tmul l a =>
          ext σ
          simp only [ι, Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom',
            AlgHom.id_apply, htmul]
          rw [show σ (algebraMap L M l) = algebraMap L M l from σ.commutes l, φ.commutes l]
          change (l ⊗ₜ[K] (1 : E)) * (1 ⊗ₜ[K] a) = l ⊗ₜ[K] a
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        | add x y hx hy => simp only [map_add, hx, hy] }
  have hsurj : Function.Surjective H' := by
    have hind : LinearIndependent F (fun σ : I => fun m : M => φ (σ m)) :=
      (linearIndependent_monoidHom M F).comp
        (fun σ : I => φ.toMonoidHom.comp σ.toMonoidHom)
        (fun σ τ h => AlgEquiv.ext fun m => φ.injective (congrArg
          (fun g : M →* F => g m) h))
    have hspan := span_flip_eq_top_iff_linearIndependent.mpr hind
    apply (LinearMap.range_eq_top (f := H'.toLinearMap)).mp
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro values ⟨m, rfl⟩
    refine ⟨m ⊗ₜ[K] (1 : E), ?_⟩
    ext σ
    change H (m ⊗ₜ[K] (1 : E)) σ = _
    rw [htmul, Algebra.TensorProduct.one_def.symm, mul_one]
    rfl
  obtain ⟨hfin, hdim, _⟩ := finite_finrank_adjoin_tensorProduct_of_isField hL z hz
  let := hfin
  have hdim' : Module.finrank F T = Module.finrank F (I → F) := by
    rw [Module.finrank_fintype_fun_eq_card, hdim]
    exact (IsGalois.card_aut_eq_finrank L M).symm.trans Nat.card_eq_fintype_card
  let e := AlgEquiv.ofBijective H'
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim' (f := H'.toLinearMap)).mpr
      hsurj, hsurj⟩
  exact ⟨e, htmul⟩

end Stacks.DiscreteValuationRing.EppLevelInduction
