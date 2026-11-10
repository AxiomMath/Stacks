module

public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.LocalRing.ResidueSection
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.LevelNumerator

open Stacks.DiscreteValuationRing.AdjoinPthRoot

/-!
# Generators with no `p`-th power related coefficients and scaled parameters

Rewriting generators of a degree-`p` extension so that no coefficients are related by `p`-th
powers, bounding the level from a numerator, and descending scaled parameters along coefficients.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u uA uK uL

open Polynomial

namespace Stacks.DiscreteValuationRing.EppLevelInduction

private theorem exists_add_pow_sub_no_pow_related_coefficients
    {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (S : Subring R) (P : Polynomial R) (hzero : P.coeff 0 ∈ S) :
    ∃ G : Polynomial R, G.natDegree * p ≤ P.natDegree ∧
      let Q := P + (G ^ p - G)
      (∀ i, P.coeff i ∈ S → Q.coeff i = P.coeff i) ∧
      ∀ i j : ℕ, Q.coeff i ∉ S → Q.coeff j ∉ S →
        ∀ r : ℕ, 0 < r → j ≠ p ^ r * i := by
  classical
  let bad (F : Polynomial R) := F.support.filter (fun i => F.coeff i ∉ S)
  have hmem : ∀ F i, i ∈ bad F ↔ F.coeff i ∉ S := by
    intro F i
    simp only [bad, Finset.mem_filter, Polynomial.mem_support_iff]
    exact and_iff_right_of_imp (fun hi heq => hi (heq ▸ S.zero_mem))
  generalize hcard : (bad P).card = c
  induction c using Nat.strong_induction_on generalizing P with
  | h c ih =>
    by_cases hnone : ∀ i j : ℕ, P.coeff i ∉ S → P.coeff j ∉ S →
        ∀ r : ℕ, 0 < r → j ≠ p ^ r * i
    · refine ⟨0, by simp, ?_⟩
      simp only [zero_pow (Fact.out : p.Prime).ne_zero, sub_self, add_zero]
      exact ⟨fun _ _ => trivial, hnone⟩
    push Not at hnone
    obtain ⟨i, j, hi, hj, r, hr, hjr⟩ := hnone
    have hi0 : 0 < i := by
      by_contra hi0
      exact hi (show P.coeff i ∈ S by simpa [show i = 0 by omega] using hzero)
    have hij : i < j := by
      rw [hjr]
      have := one_lt_pow₀ (Fact.out : p.Prime).one_lt hr.ne'
      nlinarith
    let T : Polynomial R := ∑ k ∈ Finset.range r, (Polynomial.monomial i (P.coeff i)) ^ (p ^ k)
    let Q := P - Polynomial.monomial i (P.coeff i) +
      Polynomial.monomial j ((P.coeff i) ^ (p ^ r))
    have hQT : Q = P + (T ^ p - T) := by
      rw [sum_frobenius_sub]
      simp only [Q, Polynomial.monomial_pow, Nat.mul_comm i (p ^ r), ← hjr]
      ring
    have hQcoeff : ∀ k, Q.coeff k = P.coeff k -
        (if i = k then P.coeff i else 0) +
          (if j = k then P.coeff i ^ (p ^ r) else 0) := by
      intro k
      simp only [Q, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_monomial]
    have hQsame : ∀ k, P.coeff k ∈ S → Q.coeff k = P.coeff k := by
      intro k hk
      have hik : i ≠ k := by rintro rfl; exact hi hk
      have hjk : j ≠ k := by rintro rfl; exact hj hk
      rw [hQcoeff, ite_eq_right hik, ite_eq_right hjk, sub_zero, add_zero]
    have hQzero : Q.coeff 0 ∈ S := by rw [hQsame 0 hzero]; exact hzero
    have hQbad : bad Q ⊆ (bad P).erase i := by
      intro k hk
      have hkQ := (hmem Q k).mp hk
      have hik : k ≠ i := by
        rintro rfl
        apply hkQ
        rw [hQcoeff, ite_eq_left rfl, ite_eq_right hij.ne', sub_self, add_zero]
        exact S.zero_mem
      refine Finset.mem_erase.mpr ⟨hik, (hmem P k).mpr ?_⟩
      intro hkP
      exact hkQ (hQsame k hkP ▸ hkP)
    have hcardQ : (bad Q).card < c := by
      have hle := Finset.card_le_card hQbad
      have herase := Finset.card_erase_lt_of_mem ((hmem P i).mpr hi)
      omega
    have hbadDeg : ∀ k, P.coeff k ∉ S → k ≤ P.natDegree := fun k hk =>
      Polynomial.le_natDegree_of_ne_zero fun h => hk (h ▸ S.zero_mem)
    have hQdeg : Q.natDegree ≤ P.natDegree := by
      have hiDeg := hbadDeg i hi
      have hjDeg := hbadDeg j hj
      exact (Polynomial.natDegree_add_le _ _).trans (max_le
        ((Polynomial.natDegree_sub_le _ _).trans (max_le le_rfl
          ((Polynomial.natDegree_monomial_le _).trans hiDeg)))
        ((Polynomial.natDegree_monomial_le _).trans hjDeg))
    have hTdeg : T.natDegree * p ≤ P.natDegree := by
      have hle : T.natDegree ≤ i * p ^ (r - 1) := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro k hk
        calc
          ((Polynomial.monomial i (P.coeff i)) ^ (p ^ k)).natDegree ≤
              i * p ^ k := by
            rw [Nat.mul_comm i (p ^ k)]
            exact Polynomial.natDegree_pow_le.trans
              (Nat.mul_le_mul_left _ (Polynomial.natDegree_monomial_le _))
          _ ≤ i * p ^ (r - 1) := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by
              have := Finset.mem_range.mp hk; omega))
      have heq : (i * p ^ (r - 1)) * p = j := by
        rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hr, hjr, mul_comm]
      exact (Nat.mul_le_mul_right p hle).trans (heq ▸ hbadDeg j hj)
    obtain ⟨G, hGdeg, hGsame, hGnone⟩ := ih (bad Q).card hcardQ Q hQzero rfl
    refine ⟨T + G, ?_, ?_⟩
    · calc
        (T + G).natDegree * p ≤ max T.natDegree G.natDegree * p :=
          Nat.mul_le_mul_right _ (Polynomial.natDegree_add_le _ _)
        _ ≤ P.natDegree := by
          rw [max_mul_of_nonneg _ _ (Nat.zero_le p)]
          exact max_le hTdeg (hGdeg.trans hQdeg)
    · have heq : P + ((T + G) ^ p - (T + G)) = Q + (G ^ p - G) := by
        rw [add_pow_char, hQT]
        ring
      rw [heq]
      refine ⟨?_, hGnone⟩
      intro k hk
      rw [hGsame k (hQsame k hk ▸ hk), hQsame k hk]

private theorem exists_map_eq_of_coeff_mem_range
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : Polynomial S)
    (hP : ∀ i, P.coeff i ∈ Set.range f) :
    ∃ Q : Polynomial R, Q.map f = P ∧ Q.natDegree ≤ P.natDegree := by
  classical
  choose c hc using hP
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.monomial i (c i), ?_, ?_⟩
  · simp only [Polynomial.map_sum, Polynomial.map_monomial, hc]
    exact (Polynomial.as_sum_range P).symm
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans (by
      have := Finset.mem_range.mp hi
      omega)

theorem exists_map_eq_natDegree_le
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (P : Polynomial S) :
    ∃ Q : Polynomial R, Q.map f = P ∧ Q.natDegree ≤ P.natDegree :=
  exists_map_eq_of_coeff_mem_range f P fun i => hf (P.coeff i)

theorem exists_mul_pow_aeval_inv_eq
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (π : A) (hπ : algebraMap A K π ≠ 0) (P : Polynomial A)
    (n : ℕ) (hn : P.natDegree ≤ n) :
    ∃ a : A, algebraMap A K a =
      algebraMap A K π ^ n * Polynomial.aeval (algebraMap A K π)⁻¹ P := by
  refine ⟨π ^ (n - P.natDegree) * (P.scaleRoots π).eval 1, ?_⟩
  rw [map_mul, map_eval_scaleRoots_inv_mul P π 1 hπ, map_one, mul_one,
    map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]

theorem exists_aeval_inv_sub_eq_of_map_eq
    {A K R : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [CommRing R] (f : A →+* R) (π : A) (hπ : algebraMap A K π ≠ 0)
    (m n : ℕ) (hker : ∀ a : A, f a = 0 ↔ π ^ m ∣ a)
    (P Q : Polynomial A) (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (hPQ : P.map f = Q.map f) :
    ∃ a : A, algebraMap A K π ^ n *
        (Polynomial.aeval (algebraMap A K π)⁻¹ P -
          Polynomial.aeval (algebraMap A K π)⁻¹ Q) =
      algebraMap A K (π ^ m * a) := by
  have hdiff : (P - Q).map f = 0 := by rw [Polynomial.map_sub, hPQ, sub_self]
  by_cases heq : P - Q = 0
  · refine ⟨0, ?_⟩
    rw [sub_eq_zero.mp heq, sub_self, mul_zero, mul_zero, map_zero]
  have hdiv : Polynomial.C (π ^ m) ∣ P - Q := by
    apply (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    apply (hker _).mp
    have h := congrArg (fun F : Polynomial R => F.coeff i) hdiff
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using h
  obtain ⟨T, hT⟩ := hdiv
  have hdT : T.natDegree ≤ n :=
    (Polynomial.natDegree_le_of_dvd ⟨Polynomial.C (π ^ m), by rw [mul_comm, ← hT]⟩ heq).trans
      (Polynomial.natDegree_sub_le _ _ |>.trans (max_le hP hQ))
  obtain ⟨a, ha⟩ := exists_mul_pow_aeval_inv_eq π hπ T n hdT
  refine ⟨a, ?_⟩
  rw [← map_sub, hT, map_mul, Polynomial.aeval_C, map_mul, ha]
  ring

/-- A power of a uniformizer associated to `w` factors `w` through the maximal ideal. -/
private theorem exists_mem_maximalIdeal_mul_eq_of_irreducible
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {π w : A} (hπ : Irreducible π) {e k : ℕ} (hw : Associated w (π ^ e)) (hk : k < e) :
    ∃ c : A, c ∈ IsLocalRing.maximalIdeal A ∧ w = π ^ k * c :=
  exists_mem_maximalIdeal_mul_eq_of_associated π w
    ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit) e k hw hk

/-- Raising `w ~ π ^ e` to the `p`-th power gives `w ^ p ~ π ^ (p * e)`. -/
private theorem associated_pow_mul_of_associated_pow
    {A : Type*} [CommMonoid A] {π w : A} {e : ℕ} (hw : Associated w (π ^ e)) (p : ℕ) :
    Associated (w ^ p) (π ^ (p * e)) := by
  simpa only [← pow_mul, Nat.mul_comm e p] using hw.pow_pow (n := p)

private theorem map_cyclotomic_quotient_of_w_eq_zero
    {A R : Type*} [CommRing A] [CommRing R]
    {p : ℕ} [Fact p.Prime] (f : CyclotomicRing p ℤ ℚ →+* A)
    (P : Polynomial A) (hP : shapeProp f P) (q : A →+* R)
    (hw : q (wElt f) = 0) : P.map q = Polynomial.X ^ p - Polynomial.X := by
  classical
  obtain ⟨c, hc, hP⟩ := hP
  rw [hP]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  have hczero : ∀ i ∈ Finset.Ioo 0 p, q (c i) = 0 := by
    intro i hi
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
      (hc i (Finset.mem_Ioo.mp hi).1 (Finset.mem_Ioo.mp hi).2)
    rw [hb, map_mul, hw, zero_mul]
  have hsum : (∑ i ∈ Finset.Ioo 0 p,
      Polynomial.C (q (c i)) * Polynomial.X ^ i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hczero i hi, Polynomial.C_0, zero_mul]
  rw [hsum, add_zero]

theorem exists_generator_cyclotomic_add_polynomial
    {A K L R : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [IsFractionRing A K] [CommRing R]
    (p : ℕ) [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* A) (P : Polynomial A)
    (hP : intProp f P) (hshape : shapeProp f P) (hfun : funcEq f P)
    (π : A) (hπ : Irreducible π) (e n m : ℕ)
    (hw : Associated (wElt f) (π ^ e)) (hne : n < p * e)
    (hm : m ≤ e) (hnm : n + m ≤ p * e)
    (q : A →+* R) (hker : ∀ a : A, q a = 0 ↔ π ^ m ∣ a)
    (F G : Polynomial A) (hFd : F.natDegree ≤ n) (hGd : G.natDegree * p ≤ n)
    (ξ : K) (z : L) (hz : Algebra.adjoin K {z} = ⊤)
    (heval : Polynomial.aeval z P = algebraMap K L ξ)
    (hξ : ∃ a : A, algebraMap A K π ^ n *
        (ξ - Polynomial.aeval (algebraMap A K π)⁻¹ F) = algebraMap A K (π ^ m * a)) :
    ∃ (ξ' : K) (z' : L) (H : Polynomial A),
      Algebra.adjoin K {z'} = ⊤ ∧ Polynomial.aeval z' P = algebraMap K L ξ' ∧
        H.natDegree ≤ n ∧ H.map q = F.map q + ((G.map q) ^ p - G.map q) ∧
          ∃ a : A, algebraMap A K π ^ n *
              (ξ' - Polynomial.aeval (algebraMap A K π)⁻¹ H) =
            algebraMap A K (π ^ m * a) := by
  have hπK : algebraMap A K π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hπ.ne_zero
  let x := Polynomial.aeval (algebraMap A K π)⁻¹ G
  let H := F + P.comp G
  obtain ⟨hmonic, hdeg⟩ := monic_natDegree_cyclotomic_quotient f P hP
  have hcompdeg : (P.comp G).natDegree ≤ n :=
    Polynomial.natDegree_comp_le.trans (by simpa only [hdeg, Nat.mul_comm p] using hGd)
  have hHdeg : H.natDegree ≤ n :=
    Polynomial.natDegree_add_le_of_degree_le hFd hcompdeg
  have hqP : P.map q = Polynomial.X ^ p - Polynomial.X :=
    map_cyclotomic_quotient_of_w_eq_zero f P hshape q
      ((hker _).mpr ((pow_dvd_pow π hm).trans hw.symm.dvd))
  have hHq : H.map q = F.map q + ((G.map q) ^ p - G.map q) := by
    simp only [H, Polynomial.map_add, Polynomial.map_comp, hqP,
      Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp]
  obtain ⟨b, hb⟩ := exists_mul_pow_aeval_inv_eq π hπK G G.natDegree le_rfl
  have hxb : x = (algebraMap A K (π ^ G.natDegree))⁻¹ * algebraMap A K b := by
    rw [hb, map_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hπK), one_mul]
  have hGde : G.natDegree < e := by nlinarith [(Fact.out : p.Prime).pos]
  obtain ⟨c, hc, hwc⟩ :=
    exists_mem_maximalIdeal_mul_eq_of_irreducible hπ hw hGde
  have hcoeff : 1 + algebraMap A K (wElt f) * x = algebraMap A K (1 + c * b) := by
    rw [hxb, hwc]
    simp only [map_mul, map_add, map_one, map_pow]
    field_simp
  have hunit : IsUnit (1 + c * b) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_add, map_one, map_mul, (IsLocalRing.residue_eq_zero_iff c).mpr hc,
      zero_mul, add_zero]
    exact one_ne_zero
  have hcoeffne : 1 + algebraMap A K (wElt f) * x ≠ 0 := by
    rw [hcoeff]
    exact (hunit.map (algebraMap A K)).ne_zero
  let z' := z + algebraMap K L x + algebraMap A L (wElt f) * z * algebraMap K L x
  have hz' : Algebra.adjoin K {z'} = ⊤ := by
    convert adjoin_affine_eq_top (1 + algebraMap A K (wElt f) * x) x hcoeffne z hz using 1
    dsimp [z']
    congr 2
    simp only [map_add, map_one, map_mul, ← IsScalarTower.algebraMap_apply A K L]
    ring
  let ξ' := ξ + Polynomial.aeval x P +
    algebraMap A K (wElt f) ^ p * ξ * Polynomial.aeval x P
  have heval' : Polynomial.aeval z' P = algebraMap K L ξ' := by
    rw [aeval_cyclotomic_add f P hfun z (algebraMap K L x), heval,
      Polynomial.aeval_algebraMap_apply]
    simp only [ξ', map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply A K L]
  obtain ⟨a, ha⟩ := hξ
  obtain ⟨aF, haF⟩ := exists_mul_pow_aeval_inv_eq π hπK F n hFd
  have haξ : algebraMap A K (aF + π ^ m * a) = algebraMap A K π ^ n * ξ := by
    rw [map_add, haF, ← ha]
    ring
  obtain ⟨aP, haP⟩ := exists_mul_pow_aeval_inv_eq π hπK (P.comp G) n hcompdeg
  have hcomp : Polynomial.aeval (algebraMap A K π)⁻¹ (P.comp G) = Polynomial.aeval x P := by
    rw [Polynomial.aeval_comp]
  rw [hcomp] at haP
  have hdiv : π ^ (n + m) ∣ wElt f ^ p :=
    (pow_dvd_pow π hnm).trans (associated_pow_mul_of_associated_pow hw p).symm.dvd
  obtain ⟨d, hd⟩ := hdiv
  have hcross : algebraMap A K π ^ n *
      (algebraMap A K (wElt f) ^ p * ξ * Polynomial.aeval x P) =
        algebraMap A K (π ^ m * (d * (aF + π ^ m * a) * aP)) := by
    have hdK := congrArg (algebraMap A K) hd
    simp only [map_mul, map_pow, pow_add] at hdK
    rw [map_mul, map_mul, map_mul, haξ, haP, map_pow, hdK]
    ring
  refine ⟨ξ', z', H, hz', heval', hHdeg, hHq,
    a + d * (aF + π ^ m * a) * aP, ?_⟩
  have hH : Polynomial.aeval (algebraMap A K π)⁻¹ H =
      Polynomial.aeval (algebraMap A K π)⁻¹ F + Polynomial.aeval x P := by
    rw [map_add, hcomp]
  rw [hH, mul_add, map_add, ← ha, ← hcross]
  dsimp only [ξ']
  ring

theorem exists_generator_no_pow_related_coefficients
    {A K L R k : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [IsFractionRing A K]
    [CommRing R] [CommRing k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : CyclotomicRing p ℤ ℚ →+* A) (P : Polynomial A)
    (hP : intProp f P) (hshape : shapeProp f P) (hfun : funcEq f P)
    (π : A) (hπ : Irreducible π) (e n m : ℕ)
    (hw : Associated (wElt f) (π ^ e)) (hne : n < p * e)
    (hm : m ≤ e) (hnm : n + m ≤ p * e)
    (q : A →+* R) (hq : Function.Surjective q)
    (hker : ∀ a : A, q a = 0 ↔ π ^ m ∣ a)
    (σ : k →+* R) (S : Subring k)
    (F : Polynomial A) (F₀ : Polynomial k)
    (hF : F.map q = F₀.map σ) (hFd : F.natDegree ≤ n) (hF₀d : F₀.natDegree ≤ n)
    (hzero : F₀.coeff 0 ∈ S)
    (ξ : K) (z : L) (hz : Algebra.adjoin K {z} = ⊤)
    (heval : Polynomial.aeval z P = algebraMap K L ξ)
    (hξ : ∃ a : A, algebraMap A K π ^ n *
        (ξ - Polynomial.aeval (algebraMap A K π)⁻¹ F) = algebraMap A K (π ^ m * a)) :
    ∃ (ξ' : K) (z' : L) (H : Polynomial A) (H₀ : Polynomial k),
      Algebra.adjoin K {z'} = ⊤ ∧ Polynomial.aeval z' P = algebraMap K L ξ' ∧
        H.natDegree ≤ n ∧ H.map q = H₀.map σ ∧ H₀.coeff 0 ∈ S ∧
          (∀ i j : ℕ, H₀.coeff i ∉ S → H₀.coeff j ∉ S →
            ∀ r : ℕ, 0 < r → j ≠ p ^ r * i) ∧
          ∃ a : A, algebraMap A K π ^ n *
              (ξ' - Polynomial.aeval (algebraMap A K π)⁻¹ H) =
            algebraMap A K (π ^ m * a) := by
  obtain ⟨G₀, hG₀d, hG₀same, hG₀none⟩ :=
    exists_add_pow_sub_no_pow_related_coefficients p S F₀ hzero
  obtain ⟨G, hG, hGd⟩ := exists_map_eq_natDegree_le q hq (G₀.map σ)
  have hGd' : G.natDegree * p ≤ n :=
    (Nat.mul_le_mul_right p (hGd.trans (Polynomial.natDegree_map_le))).trans
      (hG₀d.trans hF₀d)
  obtain ⟨ξ', z', H, hz', heval', hHd, hH, hξ'⟩ :=
    exists_generator_cyclotomic_add_polynomial p f P hP hshape hfun π hπ e n m
      hw hne hm hnm q hker F G hFd hGd' ξ z hz heval hξ
  refine ⟨ξ', z', H, F₀ + (G₀ ^ p - G₀), hz', heval', hHd, ?_, ?_, hG₀none, hξ'⟩
  · rw [hH, hF, hG]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow]
  · rw [hG₀same 0 hzero]
    exact hzero

private theorem injOn_mul_pow_sub_of_no_pow_relation
    (p : ℕ) (hp : 0 < p) (s : Finset ℕ) (h : ℕ → ℕ) (N : ℕ)
    (hN : ∀ i ∈ s, h i ≤ N)
    (hrel : ∀ i ∈ s, ∀ j ∈ s, ∀ r : ℕ, 0 < r → j ≠ p ^ r * i) :
    Set.InjOn (fun i => i * p ^ (N - h i)) s := by
  have hcompare : ∀ i ∈ s, ∀ j ∈ s, h i ≤ h j →
      i * p ^ (N - h i) = j * p ^ (N - h j) → i = j := by
    intro i hi j hj hij heq
    have hexp : N - h i = (N - h j) + (h j - h i) := by
      have := hN i hi
      have := hN j hj
      omega
    rw [hexp, pow_add] at heq
    have hmul : p ^ (h j - h i) * i = j := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hp)
      convert heq using 1 ; ring
    by_cases hh : h i = h j
    · simpa only [hh, Nat.sub_self, pow_zero, one_mul] using hmul
    · exact (hrel i hi j hj (h j - h i) (by omega) hmul.symm).elim
  intro i hi j hj hij
  rcases le_total (h i) (h j) with hle | hle
  · exact hcompare i hi j hj hle hij
  · exact (hcompare j hj i hi hle hij.symm).symm

private theorem exists_unique_max_mul_pow_sub
    (p n : ℕ) (hp : 1 < p) (s : Finset ℕ) (hs : s.Nonempty)
    (hpos : ∀ i ∈ s, 0 < i) (h : ℕ → ℕ)
    (hrel : ∀ i ∈ s, ∀ j ∈ s, ∀ r : ℕ, 0 < r → j ≠ p ^ r * i) :
    ∃ N : ℕ, (∀ i ∈ s, h i + 1 < N ∧ n < i * p ^ (N - h i)) ∧
      ∃ j ∈ s, ∀ i ∈ s, i ≠ j → i * p ^ (N - h i) < j * p ^ (N - h j) := by
  let N := s.sup h + n + 2
  have hN : ∀ i ∈ s, h i + 1 < N := by
    intro i hi
    have := Finset.le_sup hi (f := h)
    dsimp [N]
    omega
  refine ⟨N, ?_, ?_⟩
  · intro i hi
    refine ⟨hN i hi, ?_⟩
    have hsup := Finset.le_sup hi (f := h)
    have hpower : n < p ^ (N - h i) :=
      (Nat.lt_pow_self hp).trans_le (Nat.pow_le_pow_right (by omega) (by dsimp [N]; omega))
    exact hpower.trans_le (Nat.le_mul_of_pos_left _ (hpos i hi))
  · obtain ⟨j, hj, hjmax⟩ := s.exists_max_image (fun i => i * p ^ (N - h i)) hs
    refine ⟨j, hj, ?_⟩
    intro i hi hij
    apply lt_of_le_of_ne (hjmax i hi)
    intro heq
    exact hij (injOn_mul_pow_sub_of_no_pow_relation p (by omega) s h N
      (fun i hi => by have := hN i hi; omega) hrel hi hj heq)

theorem exists_root_heights_and_unique_max
    {R : Type*} [CommRing R] (p n : ℕ) (hp : 1 < p)
    (S : Subring R)
    (hS : ∀ x : R, x ∈ S ↔ ∀ r : ℕ, 1 ≤ r → ∃ y : R, y ^ (p ^ r) = x)
    (P : Polynomial R) (hzero : P.coeff 0 ∈ S)
    (hrel : ∀ i j : ℕ, P.coeff i ∉ S → P.coeff j ∉ S →
      ∀ r : ℕ, 0 < r → j ≠ p ^ r * i)
    (hbad : ∃ i, P.coeff i ∉ S) :
    ∃ (h : ℕ → ℕ) (μ : ℕ → R) (N j : ℕ), P.coeff j ∉ S ∧
      (∀ i, P.coeff i ∉ S →
        μ i ^ (p ^ h i) = P.coeff i ∧ (¬∃ x : R, x ^ p = μ i) ∧
          h i + 1 < N ∧ n < i * p ^ (N - h i)) ∧
      ∀ i, P.coeff i ∉ S → i ≠ j →
        i * p ^ (N - h i) < j * p ^ (N - h j) := by
  classical
  let J := P.support.filter (fun i => P.coeff i ∉ S)
  have hmem : ∀ i, i ∈ J ↔ P.coeff i ∉ S := by
    intro i
    simp only [J, Finset.mem_filter, Polynomial.mem_support_iff]
    exact and_iff_right_of_imp (fun hi heq => hi (heq ▸ S.zero_mem))
  have hJ : J.Nonempty := by
    obtain ⟨i, hi⟩ := hbad
    exact ⟨i, (hmem i).mpr hi⟩
  have hJpos : ∀ i ∈ J, 0 < i := by
    intro i hi
    by_contra hpos
    have hi0 : i = 0 := by omega
    exact (hmem i).mp hi (hi0 ▸ hzero)
  have hex : ∀ i : ℕ, ∃ (r : ℕ) (μ : R),
      P.coeff i ∉ S → μ ^ (p ^ r) = P.coeff i ∧ ¬∃ x : R, x ^ p = μ := by
    intro i
    by_cases hi : P.coeff i ∈ S
    · exact ⟨0, 0, fun h => (h hi).elim⟩
    · have hout : ¬∀ r : ℕ, 1 ≤ r → ∃ y : R, y ^ (p ^ r) = P.coeff i :=
        fun hall => hi ((hS (P.coeff i)).mpr hall)
      push Not at hout
      obtain ⟨r, hr, hroot⟩ := hout
      obtain ⟨r', μ, hμ, hμroot⟩ := exists_pow_eq_and_not_isPow p (P.coeff i) ⟨r, fun ⟨y, hy⟩ =>
        hroot y hy⟩
      exact ⟨r', μ, fun _ => ⟨hμ, hμroot⟩⟩
  choose h μ hμ using hex
  obtain ⟨N, hN, j, hj, hjmax⟩ := exists_unique_max_mul_pow_sub p n hp J hJ hJpos h
    (fun i hi j hj r hr => hrel i j ((hmem i).mp hi) ((hmem j).mp hj) r hr)
  refine ⟨h, μ, N, j, (hmem j).mp hj, ?_, ?_⟩
  · intro i hi
    exact ⟨(hμ i hi).1, (hμ i hi).2, hN i ((hmem i).mpr hi)⟩
  · intro i hi hij
    exact hjmax i ((hmem i).mpr hi) hij

theorem exists_comp_X_pow_add_pow_sub
    {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (P : Polynomial R) (N : ℕ) (hNpos : 0 < N)
    (h : ℕ → ℕ) (μ : ℕ → R)
    (hN : ∀ i ∈ P.support, h i ≤ N)
    (hμ : ∀ i ∈ P.support, μ i ^ (p ^ h i) = P.coeff i) :
    ∃ G : Polynomial R, G.natDegree * p ≤ P.natDegree * p ^ N ∧
      P.comp (Polynomial.X ^ (p ^ N)) + (G ^ p - G) =
        ∑ i ∈ P.support, Polynomial.monomial (i * p ^ (N - h i)) (μ i) := by
  classical
  let T (i : ℕ) : Polynomial R :=
    Polynomial.monomial (i * p ^ (N - h i)) (μ i)
  let U (i : ℕ) : Polynomial R := ∑ k ∈ Finset.range (h i), T i ^ (p ^ k)
  let G : Polynomial R := -∑ i ∈ P.support, U i
  have hU : ∀ i, U i ^ p - U i = T i ^ (p ^ h i) - T i :=
    fun i => sum_frobenius_sub p (T i) (h i)
  have hT : ∀ i ∈ P.support,
      T i ^ (p ^ h i) = (Polynomial.monomial i (P.coeff i)).comp (Polynomial.X ^ (p ^ N)) := by
    intro i hi
    have hexp : (i * p ^ (N - h i)) * p ^ h i = p ^ N * i := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (hN i hi), mul_comm]
    dsimp only [T]
    rw [Polynomial.monomial_pow, hμ i hi, Polynomial.monomial_comp,
      ← pow_mul, hexp, Polynomial.C_mul_X_pow_eq_monomial]
  have hdegU : ∀ i ∈ P.support, (U i).natDegree ≤ P.natDegree * p ^ (N - 1) := by
    intro i hi
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    have hkexp : N - h i + k ≤ N - 1 := by
      have := Finset.mem_range.mp hk
      have := hN i hi
      omega
    calc
      (T i ^ (p ^ k)).natDegree ≤ p ^ k * (i * p ^ (N - h i)) :=
        Polynomial.natDegree_pow_le.trans
          (Nat.mul_le_mul_left _ (Polynomial.natDegree_monomial_le _))
      _ = i * p ^ (N - h i + k) := by rw [pow_add]; ring
      _ ≤ P.natDegree * p ^ (N - 1) := Nat.mul_le_mul
        (Polynomial.le_natDegree_of_mem_supp i hi)
        (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hkexp)
  refine ⟨G, ?_, ?_⟩
  · have hdG : G.natDegree ≤ P.natDegree * p ^ (N - 1) := by
      rw [Polynomial.natDegree_neg]
      exact Polynomial.natDegree_sum_le_of_forall_le _ _ hdegU
    have hpow : (P.natDegree * p ^ (N - 1)) * p = P.natDegree * p ^ N := by
      rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hNpos]
    exact hpow ▸ Nat.mul_le_mul_right p hdG
  · have hG : G ^ p - G = -∑ i ∈ P.support, (U i ^ p - U i) := by
      change (-∑ i ∈ P.support, U i) ^ p - (-∑ i ∈ P.support, U i) = _
      rw [← frobenius_def, map_neg, map_sum]
      simp only [frobenius_def, Finset.sum_sub_distrib]
      ring
    rw [hG]
    have hsum : (∑ i ∈ P.support, (U i ^ p - U i)) =
        P.comp (Polynomial.X ^ (p ^ N)) - ∑ i ∈ P.support, T i := by
      simp only [hU, Finset.sum_sub_distrib]
      congr 1
      calc
        (∑ i ∈ P.support, T i ^ (p ^ h i)) =
            ∑ i ∈ P.support,
              (Polynomial.monomial i (P.coeff i)).comp (Polynomial.X ^ (p ^ N)) :=
          Finset.sum_congr rfl hT
        _ = P.comp (Polynomial.X ^ (p ^ N)) := by
          rw [← Polynomial.sum_comp, ← Polynomial.as_sum_support]
    rw [hsum]
    ring

theorem natDegree_and_coeff_sum_monomial_of_unique_max
    {R ι : Type*} [Semiring R] (s : Finset ι) (d : ι → ℕ) (a : ι → R)
    (j : ι) (hj : j ∈ s) (ha : a j ≠ 0)
    (hd : ∀ i ∈ s, i ≠ j → d i < d j) :
    (∑ i ∈ s, Polynomial.monomial (d i) (a i)).natDegree = d j ∧
      (∑ i ∈ s, Polynomial.monomial (d i) (a i)).coeff (d j) = a j := by
  classical
  have hc : (∑ i ∈ s, Polynomial.monomial (d i) (a i)).coeff (d j) = a j := by
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · exact Polynomial.coeff_monomial_same _ _
    · intro i hi hij
      rw [Polynomial.coeff_monomial, ite_eq_right (hd i hi hij).ne]
    · exact fun h => (h hj).elim
  refine ⟨le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero (hc ▸ ha)), hc⟩
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_monomial_le _).trans
    (by
      by_cases hij : i = j
      · simp only [hij, le_refl]
      · exact (hd i hi hij).le)

private theorem isDegreePExtensionOfFiniteLevel_and_extensionLevel_le_of_numerator
    (A K L : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [IsFractionRing A K]
    [Module.Finite K L] (p : ℕ) [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* A) (P : Polynomial A)
    (π : A) (hπ : Irreducible π) (e n : ℕ) (he : 0 < e)
    (hw : Associated (wElt f) (π ^ e)) (hdegree : Module.finrank K L = p)
    (hn : n ∈ Stacks.DegreePExtensionLevel.extensionLevelNumerators A K L P π) (hne : n < p * e) :
    Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel A K L p f P ∧
      ∃ hnonempty : (Stacks.DegreePExtensionLevel.extensionLevelNumerators A K L P π).Nonempty,
        Stacks.DegreePExtensionLevel.extensionLevel A K L P π e he hnonempty ≤ (n : ℚ) / e := by
  have hnonempty : (Stacks.DegreePExtensionLevel.extensionLevelNumerators A K L P π).Nonempty := ⟨n,
    hn⟩
  refine ⟨?_, hnonempty, ?_⟩
  · obtain ⟨ξ, z, hz, hPz, a, ha⟩ := hn
    obtain ⟨c, hc, hwc⟩ := exists_mem_maximalIdeal_mul_eq_of_irreducible hπ
      (associated_pow_mul_of_associated_pow hw p) hne
    refine ⟨hdegree, ξ, z, hz, hPz, c * a,
      (IsLocalRing.maximalIdeal A).mul_mem_right a hc, ?_⟩
    have hwcK := congrArg (algebraMap A K) hwc
    simp only [map_pow, map_mul] at hwcK
    rw [map_mul, ha, map_pow, hwcK]
    ring
  · change ((sInf (Stacks.DegreePExtensionLevel.extensionLevelNumerators A K L P π) : ℕ) : ℚ) / e ≤
    _
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg e)
    exact_mod_cast Nat.sInf_le hn

theorem isDegreePExtensionOfFiniteLevel_and_extensionLevel_le_of_associated_pow
    (A K L : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [IsFractionRing A K]
    [Module.Finite K L] (p : ℕ) [Fact p.Prime]
    (f : CyclotomicRing p ℤ ℚ →+* A) (P : Polynomial A)
    (ϖ π : A) (hπ : Irreducible π) (d e n : ℕ) (hd : 0 < d) (he : 0 < e)
    (hϖ : Associated ϖ (π ^ d))
    (hw : Associated (wElt f) (ϖ ^ e)) (hdegree : Module.finrank K L = p)
    (ξ : K) (z : L) (hz : Algebra.adjoin K ({z} : Set L) = ⊤)
    (hPz : Polynomial.eval₂ ((algebraMap K L).comp (algebraMap A K)) z P = algebraMap K L ξ)
    (b : A) (hb : algebraMap A K b = algebraMap A K (ϖ ^ n) * ξ) (hne : n < p * e) :
    Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel A K L p f P ∧
      ∃ (π₁ : A) (e₁ : ℕ) (he₁ : 0 < e₁)
        (hne : (Stacks.DegreePExtensionLevel.extensionLevelNumerators A K L P π₁).Nonempty),
        Irreducible π₁ ∧ Associated (wElt f) (π₁ ^ e₁) ∧
          Stacks.DegreePExtensionLevel.extensionLevel A K L P π₁ e₁ he₁ hne ≤ (n : ℚ) / e := by
  obtain ⟨u, hu⟩ := hϖ
  have hmem : d * n ∈ Stacks.DegreePExtensionLevel.extensionLevelNumerators A K L P π := by
    refine ⟨ξ, z, hz, hPz, b * (u : A) ^ n, ?_⟩
    have hpow : π ^ (d * n) = ϖ ^ n * (u : A) ^ n := by
      rw [pow_mul, ← hu, mul_pow]
    rw [hpow, map_mul, hb, map_mul]
    ring
  have hde : 0 < d * e := Nat.mul_pos hd he
  have hw' : Associated (wElt f) (π ^ (d * e)) := by
    refine hw.trans ?_
    rw [pow_mul]
    exact Associated.pow_pow ⟨u, hu⟩
  obtain ⟨hfin, hnon, hle⟩ :=
    isDegreePExtensionOfFiniteLevel_and_extensionLevel_le_of_numerator A K L p f P π hπ
      (d * e) (d * n) hde hw' hdegree hmem (by nlinarith)
  refine ⟨hfin, π, d * e, hde, hnon, hπ, hw', hle.trans_eq ?_⟩
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp

/-- Compatible residue-section lifts turn coefficient descent in the residue fields into
coefficient descent in the truncated quotient rings. -/
theorem polynomial_map_coeff_mem_range_of_coefficients_descend
    {B R S kA kB : Type*}
    [CommRing B] [CommRing R] [CommRing S] [CommRing kA] [CommRing kB]
    (qB : B →+* S) (ι : R →+* S) (ρ : kA →+* kB) (τ : kA →+* R) (σ : kB →+* S)
    (hσ : ι.comp τ = σ.comp ρ)
    (H : Polynomial B) (H₀ : Polynomial kB) (hH : H.map qB = H₀.map σ)
    (hcoeff : ∀ i, H₀.coeff i ∈ Set.range ρ) :
    ∀ i, (H.map qB).coeff i ∈ Set.range ι := by
  intro i
  rw [hH, Polynomial.coeff_map]
  obtain ⟨x, hx⟩ := hcoeff i
  refine ⟨τ x, ?_⟩
  have hi := DFunLike.congr_fun hσ x
  change ι (τ x) = σ (ρ x) at hi
  rw [← hx]
  exact hi

/-- The prepared-polynomial relation in truncated quotient rings is preserved by a commuting
base-change square.

This is the purely functorial part of transporting the 09F5 preparation to a conjugate factor:
`H` and its residue polynomial `H₀` are mapped, while the two compatibility equations identify
both resulting quotient polynomials. -/
theorem polynomial_quotient_relation_map
    {B B' S S' k k' : Type*}
    [CommRing B] [CommRing B'] [CommRing S] [CommRing S'] [CommRing k] [CommRing k']
    (g : B →+* B') (q : B →+* S) (q' : B' →+* S') (ψ : S →+* S')
    (r : k →+* k') (σ : k →+* S) (σ' : k' →+* S')
    (hq : q'.comp g = ψ.comp q) (hσ : σ'.comp r = ψ.comp σ)
    (H : Polynomial B) (H₀ : Polynomial k) (hH : H.map q = H₀.map σ) :
    (H.map g).map q' = (H₀.map r).map σ' := by
  rw [Polynomial.map_map, hq, ← Polynomial.map_map, hH,
    Polynomial.map_map, ← hσ, ← Polynomial.map_map]

/-- Absorbing the finite image of a polynomial's support puts every coefficient of the mapped
polynomial in the same field range; coefficients outside the support are zero. -/
theorem polynomial_map_coeff_mem_fieldRange_of_support
    {k k' F : Type*} [Field k] [Field k'] [Field F] [DecidableEq k]
    (r : k →+* k') (g : F →+* k') (H : Polynomial k)
    (h : ∀ x ∈ H.support.image (fun i => H.coeff i),
      r x ∈ g.fieldRange) :
    ∀ i, (H.map r).coeff i ∈ g.fieldRange := by
  classical
  intro i
  rw [Polynomial.coeff_map]
  by_cases hi : i ∈ H.support
  · exact h (H.coeff i) (Finset.mem_image_of_mem _ hi)
  · have hzero : H.coeff i = 0 := by
      simpa only [Polynomial.mem_support_iff, not_not] using hi
    rw [hzero, map_zero]
    exact g.fieldRange.zero_mem

/-- A prepared parameter relation is preserved by a commuting base-change square: both the
parameter and the prepared polynomial are transported, including evaluation at the inverse of the
mapped uniformizer. -/
theorem exists_mapped_scaled_parameter_relation
    {B₀ B L₀ L : Type*}
    [CommRing B₀] [CommRing B] [Field L₀] [Field L]
    [Algebra B₀ L₀] [Algebra B L]
    (g : B₀ →+* B) (e : L₀ →+* L)
    (hcomm : (algebraMap B L).comp g = e.comp (algebraMap B₀ L₀))
    (pi₀ : B₀) (m n : ℕ) (H : Polynomial B₀) (xi₀ : L₀)
    (hxi : ∃ b : B₀, algebraMap B₀ L₀ pi₀ ^ n *
        (xi₀ - Polynomial.aeval (algebraMap B₀ L₀ pi₀)⁻¹ H) =
          algebraMap B₀ L₀ (pi₀ ^ m * b)) :
    ∃ b : B, algebraMap B L (g pi₀) ^ n *
        (e xi₀ - Polynomial.aeval (algebraMap B L (g pi₀))⁻¹ (H.map g)) =
          algebraMap B L ((g pi₀) ^ m * b) := by
  have hbase (x : B₀) : algebraMap B L (g x) = e (algebraMap B₀ L₀ x) :=
    DFunLike.congr_fun hcomm x
  have hroot : (algebraMap B L (g pi₀))⁻¹ = e (algebraMap B₀ L₀ pi₀)⁻¹ := by
    rw [map_inv₀, ← hbase pi₀]
  have haeval : Polynomial.aeval (algebraMap B L (g pi₀))⁻¹ (H.map g) =
      e (Polynomial.aeval (algebraMap B₀ L₀ pi₀)⁻¹ H) := by
    rw [hroot, Polynomial.aeval_def, Polynomial.eval₂_map, hcomm, Polynomial.aeval_def]
    exact (Polynomial.hom_eval₂ H (algebraMap B₀ L₀) e
      (algebraMap B₀ L₀ pi₀)⁻¹).symm
  obtain ⟨b, hb⟩ := hxi
  refine ⟨g b, ?_⟩
  have haeval' : Polynomial.aeval (e (algebraMap B₀ L₀ pi₀))⁻¹ (H.map g) =
      e (Polynomial.aeval (algebraMap B₀ L₀ pi₀)⁻¹ H) := by
    simpa only [hbase] using haeval
  simpa only [map_mul, map_pow, map_sub, hbase, haeval'] using congrArg e hb

/-- If the truncated coefficients of a prepared parameter polynomial already descend through the
base quotient, that is, the coefficients of `H.map qB` lie in the range of the base quotient map,
then the scaled parameter itself descends modulo the prescribed uniformizer power. -/
theorem exists_scaled_parameter_eq_of_quotient_coefficients_descend
    {A B L R S : Type*}
    [CommRing A] [CommRing B] [IsDomain B] [Field L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    [CommRing R] [CommRing S]
    (qA : A →+* R) (hqA : Function.Surjective qA) (qB : B →+* S) (ι : R →+* S)
    (hq : ι.comp qA = qB.comp (algebraMap A B))
    (π : A) (hπ : algebraMap A L π ≠ 0) (m n : ℕ)
    (hker : ∀ b : B, qB b = 0 ↔ (algebraMap A B π) ^ m ∣ b)
    (H : Polynomial B) (hHd : H.natDegree ≤ n)
    (hcoeff : ∀ i, (H.map qB).coeff i ∈ Set.range ι)
    (ξ : L) (hξ : ∃ b : B, algebraMap A L π ^ n *
        (ξ - Polynomial.aeval (algebraMap A L π)⁻¹ H) =
          algebraMap B L ((algebraMap A B π) ^ m * b)) :
    ∃ (a : A) (b : B), algebraMap A L π ^ n * ξ =
      algebraMap A L a + algebraMap B L ((algebraMap A B π) ^ m * b) := by
  obtain ⟨T₀, hT₀, hT₀d⟩ := exists_map_eq_of_coeff_mem_range ι (H.map qB) hcoeff
  obtain ⟨T, hT, hTd⟩ := exists_map_eq_natDegree_le qA hqA T₀
  have hTdn : T.natDegree ≤ n :=
    hTd.trans (hT₀d.trans (Polynomial.natDegree_map_le.trans hHd))
  have hTmap : (T.map (algebraMap A B)).map qB = H.map qB := by
    rw [Polynomial.map_map, ← hq, ← Polynomial.map_map, hT, hT₀]
  have hπB : algebraMap B L (algebraMap A B π) ≠ 0 := by
    rwa [← IsScalarTower.algebraMap_apply A B L]
  obtain ⟨b₀, hb₀⟩ := exists_aeval_inv_sub_eq_of_map_eq qB (algebraMap A B π)
    hπB m n hker H (T.map (algebraMap A B)) hHd
    (Polynomial.natDegree_map_le.trans hTdn) hTmap.symm
  obtain ⟨a, ha⟩ := exists_mul_pow_aeval_inv_eq π hπ T n hTdn
  have hTeval : Polynomial.aeval (algebraMap A L π)⁻¹ (T.map (algebraMap A B)) =
      Polynomial.aeval (algebraMap A L π)⁻¹ T := by
    rw [Polynomial.aeval_map_algebraMap]
  rw [← IsScalarTower.algebraMap_apply A B L, hTeval] at hb₀
  obtain ⟨b, hb⟩ := hξ
  refine ⟨a, b + b₀, ?_⟩
  rw [mul_add, map_add, ha]
  linear_combination hb + hb₀

/-- If the coefficients of a prepared parameter polynomial descend through the residue-field
map, then the parameter itself is a base element modulo the prescribed power of the uniformizer.
-/
theorem exists_scaled_parameter_eq_of_coefficients_descend
    {A B L R S kA kB : Type*}
    [CommRing A] [CommRing B] [IsDomain B] [Field L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    [CommRing R] [CommRing S] [CommRing kA] [CommRing kB]
    (qA : A →+* R) (hqA : Function.Surjective qA) (qB : B →+* S) (ι : R →+* S)
    (hq : ι.comp qA = qB.comp (algebraMap A B))
    (ρ : kA →+* kB) (τ : kA →+* R) (σ : kB →+* S)
    (hσ : ι.comp τ = σ.comp ρ)
    (π : A) (hπ : algebraMap A L π ≠ 0) (m n : ℕ)
    (hker : ∀ b : B, qB b = 0 ↔ (algebraMap A B π) ^ m ∣ b)
    (H : Polynomial B) (H₀ : Polynomial kB)
    (hH : H.map qB = H₀.map σ) (hHd : H.natDegree ≤ n) (_hH₀d : H₀.natDegree ≤ n)
    (hcoeff : ∀ i, H₀.coeff i ∈ Set.range ρ)
    (ξ : L) (hξ : ∃ b : B, algebraMap A L π ^ n *
        (ξ - Polynomial.aeval (algebraMap A L π)⁻¹ H) =
          algebraMap B L ((algebraMap A B π) ^ m * b)) :
    ∃ (a : A) (b : B), algebraMap A L π ^ n * ξ =
      algebraMap A L a + algebraMap B L ((algebraMap A B π) ^ m * b) := by
  exact exists_scaled_parameter_eq_of_quotient_coefficients_descend
    qA hqA qB ι hq π hπ m n hker H hHd
    (polynomial_map_coeff_mem_range_of_coefficients_descend qB ι ρ τ σ hσ H H₀ hH hcoeff) ξ hξ

/-- **Prepared mixed-level descent after passage to a conjugate factor.**

Given a preparation `H.map q₀ = H₀.map σ₀`, three commuting squares relating it to `B`, residue
coefficients of `H₀` whose images lie in the range of `ρ`, and the mapped parameter relation `hξ`,
`π ^ n * ξ` is the sum of the image of an element of `A` and the image of a multiple of
`(algebraMap A B π) ^ m`. -/
theorem exists_scaled_parameter_eq_of_mapped_preparation
    {A B₀ B L Q₀ QA QB k₀ kA kB : Type*}
    [CommRing A] [CommRing B₀] [CommRing B] [IsDomain B] [Field L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    [CommRing Q₀] [CommRing QA] [CommRing QB]
    [Field k₀] [Field kA] [Field kB] [DecidableEq k₀]
    (g : B₀ →+* B)
    (q₀ : B₀ →+* Q₀) (qA : A →+* QA) (hqA : Function.Surjective qA)
    (qB : B →+* QB) (ψ : Q₀ →+* QB) (ι : QA →+* QB)
    (r : k₀ →+* kB) (ρ : kA →+* kB)
    (σ₀ : k₀ →+* Q₀) (τ : kA →+* QA) (σ : kB →+* QB)
    (hqg : qB.comp g = ψ.comp q₀)
    (hσr : σ.comp r = ψ.comp σ₀)
    (hq : ι.comp qA = qB.comp (algebraMap A B))
    (hσ : ι.comp τ = σ.comp ρ)
    (π : A) (hπ : algebraMap A L π ≠ 0) (m n : ℕ)
    (hker : ∀ b : B, qB b = 0 ↔ (algebraMap A B π) ^ m ∣ b)
    (H : Polynomial B₀) (H₀ : Polynomial k₀)
    (hH : H.map q₀ = H₀.map σ₀) (hHd : H.natDegree ≤ n)
    (hH₀d : H₀.natDegree ≤ n)
    (habs : ∀ x ∈ H₀.support.image (fun i => H₀.coeff i),
      r x ∈ ρ.fieldRange)
    (ξ : L) (hξ : ∃ b : B, algebraMap A L π ^ n *
        (ξ - Polynomial.aeval (algebraMap A L π)⁻¹ (H.map g)) =
          algebraMap B L ((algebraMap A B π) ^ m * b)) :
    ∃ (a : A) (b : B), algebraMap A L π ^ n * ξ =
      algebraMap A L a + algebraMap B L ((algebraMap A B π) ^ m * b) := by
  classical
  have hrel : (H.map g).map qB = (H₀.map r).map σ :=
    polynomial_quotient_relation_map g q₀ qB ψ r σ₀ σ hqg hσr H H₀ hH
  have hcoeff : ∀ i, (H₀.map r).coeff i ∈ ρ.fieldRange :=
    polynomial_map_coeff_mem_fieldRange_of_support r ρ H₀ habs
  exact exists_scaled_parameter_eq_of_coefficients_descend
    qA hqA qB ι hq ρ τ σ hσ π hπ m n hker
    (H.map g) (H₀.map r) hrel (Polynomial.natDegree_map_le.trans hHd)
    (Polynomial.natDegree_map_le.trans hH₀d) hcoeff ξ hξ

end Stacks.DiscreteValuationRing.EppLevelInduction
