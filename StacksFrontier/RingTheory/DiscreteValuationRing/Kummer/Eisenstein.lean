module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer.RingOfIntegers

@[expose] public section

/-! # Totally ramified extensions of prime-power degree (Stacks Tag 09EW)

Let `A` be a discrete valuation ring with positive residue characteristic `p` and
uniformizer `π`. For every `n > 1` and every power `q` of `p`, there is a separable
extension of the fraction field of degree `q` whose integral closure is totally
ramified. Its uniformizer may be chosen to satisfy two prescribed congruences.

Total ramification is expressed by `Stacks.KummerExtension.IsTotallyRamified`, and the ring of
integers in the extension is the integral closure supplied by Mathlib.

A uniformizer of a discrete valuation ring is represented by an irreducible element.
The ramification index is stated at the maximal ideals of the two discrete valuation
rings.

The extension is built from the Eisenstein polynomial `x^q - (π^(n + q - 1) x + π)`,
which is the polynomial `y^q - π^(n + q - 1) y = π` obtained from the Artin-Schreier
style equation `z^q - π^n z = π^(1 - q)` by the substitution `y = π z`.

## References

* [Stacks Project, Tag 09EW](https://stacks.math.columbia.edu/tag/09EW)
-/

open Polynomial

universe u v w

namespace Stacks.EisensteinExtension

/-- The Eisenstein polynomial `x^q - (π^(n + q - 1) x + π)` over the base ring `A`. -/
private noncomputable def eisensteinPolyA {A : Type u} [CommRing A]
    (π : A) (n q : ℕ) : A[X] := X ^ q - (C (π ^ (n + q - 1)) * X + C π)

/-- The Eisenstein polynomial `x^q - (π^(n + q - 1) x + π)` over the fraction field `K`. -/
private noncomputable def eisensteinPolyK {A : Type u} {K : Type v} [CommRing A] [Field K]
    [Algebra A K] (π : A) (n q : ℕ) : K[X] :=
  X ^ q - (C (algebraMap A K (π ^ (n + q - 1))) * X + C (algebraMap A K π))

/-- `eisensteinPolyA π n q` is monic once `q ≥ 2`, since the subtracted part has degree
at most one. -/
private lemma eisensteinPolyA_monic {A : Type u} [CommRing A] [Nontrivial A]
    (π : A) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) : (eisensteinPolyA π n q).Monic := by
  rw [eisensteinPolyA]
  apply monic_X_pow_sub
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast (show 1 < q by omega))
  · exact degree_C_le.trans_lt (by exact_mod_cast (show 0 < q by omega))

/-- `eisensteinPolyA π n q` has degree `q` once `q ≥ 2`. -/
private lemma eisensteinPolyA_natDegree {A : Type u} [CommRing A] [Nontrivial A]
    (π : A) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) : (eisensteinPolyA π n q).natDegree = q := by
  rw [eisensteinPolyA, natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · have hle : (C (π ^ (n + q - 1)) * X + C π).natDegree ≤ 1 := by
      calc
        _ ≤ max (C (π ^ (n + q - 1)) * X).natDegree (C π).natDegree := natDegree_add_le _ _
        _ ≤ max ((C (π ^ (n + q - 1))).natDegree + X.natDegree) (C π).natDegree :=
          max_le_max natDegree_mul_le le_rfl
        _ ≤ 1 := by rw [natDegree_C, natDegree_C]; simp
    have hx : (X ^ q : A[X]).natDegree = q := by simp
    rw [hx]
    omega

/-- The polynomial over `K` is the image of the polynomial over `A`. -/
private lemma map_eisensteinPolyA {A : Type u} {K : Type v} [CommRing A] [Field K] [Algebra A K]
    (π : A) (n q : ℕ) : map (algebraMap A K) (eisensteinPolyA π n q) = eisensteinPolyK π n q := by
  simp [eisensteinPolyA, eisensteinPolyK]

/-- `eisensteinPolyA π n q` is Eisenstein at the prime `(π)`: all lower coefficients lie in
`(π)` and the constant term is not in `(π)^2`. -/
private lemma eisensteinPolyA_eisenstein {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ}
    (hq : 2 ≤ q) : (eisensteinPolyA π n q).IsEisensteinAt (Ideal.span {π}) := by
  let P : Ideal A := Ideal.span {π}
  have hP : P.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ.prime
  refine (eisensteinPolyA_monic π n hq).isEisensteinAt_of_mem_of_notMem hP.ne_top ?_ ?_
  · intro i hi
    rw [eisensteinPolyA_natDegree π n hq] at hi
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [eisensteinPolyA, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X,
        coeff_C, show (0 : ℕ) ≠ q by omega, ite_false, zero_ne_one, ite_true, zero_sub]
      rw [Ideal.mem_span_singleton]
      exact ⟨-1, by simp⟩
    rcases eq_or_ne i 1 with rfl | hi1
    · simp only [eisensteinPolyA, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X,
        coeff_C, show (1 : ℕ) ≠ q by omega, ite_false, ite_true, one_ne_zero, zero_sub]
      rw [Ideal.mem_span_singleton]
      refine ⟨-(π ^ (n + q - 2)), ?_⟩
      rw [mul_neg, ← pow_succ']
      have he : n + q - 2 + 1 = n + q - 1 := by omega
      rw [he]
      ring
    · rw [eisensteinPolyA, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X,
        coeff_C, ite_eq_right (ne_of_lt hi), ite_eq_right hi1, ite_eq_right hi0]
      simp
  · simp only [eisensteinPolyA, coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X,
      coeff_C, show (0 : ℕ) ≠ q by omega, ite_false, zero_ne_one, ite_true, zero_sub]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    rw [dvd_neg] at hdvd
    have hcancel : π ∣ 1 := by
      have h2 : π * π ∣ π * 1 := by simpa [pow_two, mul_one] using hdvd
      exact (mul_dvd_mul_iff_left hπ.ne_zero).mp h2
    exact hπ.not_isUnit (isUnit_of_dvd_one hcancel)

/-- Being Eisenstein at `(π)`, the polynomial is irreducible over `A`. -/
private lemma eisensteinPolyA_irreducible {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ}
    (hq : 2 ≤ q) : Irreducible (eisensteinPolyA π n q) :=
  (eisensteinPolyA_eisenstein π hπ n hq).irreducible
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ.prime)
    (eisensteinPolyA_monic π n hq).isPrimitive (by rw [eisensteinPolyA_natDegree π n hq]; omega)

/-- Being Eisenstein at `(π)`, the polynomial is irreducible over the fraction field. -/
private lemma eisensteinPolyK_irreducible {A : Type u} {K : Type v} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    Irreducible (eisensteinPolyK π n q : K[X]) := by
  rw [← map_eisensteinPolyA]
  rw [← (eisensteinPolyA_monic π n hq).irreducible_iff_irreducible_map_fraction_map]
  exact eisensteinPolyA_irreducible π hπ n hq

/-- The degree-`q` extension of `K` cut out by `eisensteinPolyK π n q`. -/
private noncomputable abbrev eisensteinExt {A : Type u} {K : Type v}
    [CommRing A] [Field K] [Algebra A K]
    (π : A) (n q : ℕ) := AdjoinRoot (eisensteinPolyK (K := K) π n q : K[X])

/-- The defining relation `α^q = π + π^(n + q - 1) α` satisfied by the adjoined root. -/
private lemma root_relation {A : Type u} {K : Type v} [CommRing A] [Field K] [Algebra A K]
    (π : A) (n q : ℕ) :
    (AdjoinRoot.root (eisensteinPolyK π n q : K[X])) ^ q =
      algebraMap A (eisensteinExt (K := K) π n q) π +
        algebraMap A (eisensteinExt (K := K) π n q) (π ^ (n + q - 1)) *
          AdjoinRoot.root (eisensteinPolyK π n q : K[X]) := by
  change (AdjoinRoot.root (eisensteinPolyK π n q : K[X])) ^ q =
    AdjoinRoot.of (eisensteinPolyK π n q : K[X]) (algebraMap A K π) +
      AdjoinRoot.of (eisensteinPolyK π n q : K[X])
        (algebraMap A K (π ^ (n + q - 1))) *
        AdjoinRoot.root (eisensteinPolyK π n q : K[X])
  have h := AdjoinRoot.eval₂_root (eisensteinPolyK π n q : K[X])
  rw [eisensteinPolyK, eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_mul,
    eval₂_C, eval₂_C, sub_eq_zero] at h
  rw [eisensteinPolyK]
  simpa only [eval₂_X, add_comm] using h

/-- The adjoined root is a root of `eisensteinPolyA π n q`. -/
private lemma aeval_root_eisensteinPolyA {A : Type u} {K : Type v} [CommRing A] [Field K]
    [Algebra A K] (π : A) (n q : ℕ) :
    aeval (AdjoinRoot.root (eisensteinPolyK π n q : K[X])) (eisensteinPolyA π n q) = 0 := by
  rw [eisensteinPolyA]
  simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]
  rw [root_relation (K := K) π n q, map_pow]
  ring

/-- The polynomial is separable: its derivative `q x^(q-1) - π^(n + q - 1)` is nonzero, since
its value at `0` is the nonzero element `-π^(n + q - 1)`. -/
private lemma eisensteinPolyK_separable {A : Type u} {K : Type v} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    (eisensteinPolyK π n q : K[X]).Separable := by
  rw [separable_iff_derivative_ne_zero (eisensteinPolyK_irreducible π hπ n hq)]
  intro hd
  rw [eisensteinPolyK, derivative_sub, derivative_add, derivative_X_pow, derivative_mul,
    derivative_C, derivative_X, mul_one, zero_mul, zero_add, derivative_C] at hd
  have hc := congrArg (fun f : K[X] ↦ eval 0 f) hd
  have hq0 : q - 1 ≠ 0 := by omega
  simp only [map_natCast, map_pow, add_zero, eval_sub, eval_mul, eval_natCast, eval_pow,
    eval_X, ne_eq, hq0, not_false_eq_true, zero_pow, mul_zero, eval_C, zero_sub, eval_zero,
    neg_eq_zero, pow_eq_zero_iff', FaithfulSMul.algebraMap_eq_zero_iff] at hc
  have hπK : algebraMap A K π ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne hπ.ne_zero
  have hpow : algebraMap A K (π ^ (n + q - 1)) ≠ 0 :=
    by simpa using (IsFractionRing.injective A K).ne (pow_ne_zero _ hπ.ne_zero)
  exact hπ.ne_zero hc.1

/-- The extension has degree `q` over `K`. -/
private lemma finrank_eisensteinExt {A : Type u} {K : Type v} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    Module.finrank K (eisensteinExt (A := A) (K := K) π n q) = q := by
  let : Fact (Irreducible (eisensteinPolyK π n q : K[X])) :=
    ⟨eisensteinPolyK_irreducible π hπ n hq⟩
  rw [(AdjoinRoot.powerBasis (eisensteinPolyK_irreducible π hπ n hq).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim]
  rw [← map_eisensteinPolyA, natDegree_map_eq_of_injective (IsFractionRing.injective A K),
    eisensteinPolyA_natDegree π n hq]

/-- The extension is torsion free over `A`, since `A` embeds in `K`. -/
private lemma isTorsionFree_eisensteinExt {A : Type u} {K : Type v} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    Module.IsTorsionFree A (eisensteinExt (K := K) π n q) := by
  let : Fact (Irreducible (eisensteinPolyK π n q : K[X])) :=
    ⟨eisensteinPolyK_irreducible π hπ n hq⟩
  rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A K,
    RingHom.coe_comp]
  exact (algebraMap K _).injective.comp (IsFractionRing.injective A K)

/-- The extension is separable over `K`, being generated by a separable element. -/
private lemma isSeparable_eisensteinExt {A : Type u} {K : Type v} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    Algebra.IsSeparable K (eisensteinExt (A := A) (K := K) π n q) := by
  let : Fact (Irreducible (eisensteinPolyK π n q : K[X])) :=
    ⟨eisensteinPolyK_irreducible π hπ n hq⟩
  have hirr : Irreducible (eisensteinPolyK π n q : K[X]) :=
    eisensteinPolyK_irreducible π hπ n hq
  have hroot : IsSeparable K (AdjoinRoot.root (eisensteinPolyK π n q : K[X])) := by
    rw [IsSeparable, AdjoinRoot.minpoly_root hirr.ne_zero]
    have hu : IsUnit (C (eisensteinPolyK π n q : K[X]).leadingCoeff⁻¹) :=
      isUnit_C.mpr (IsUnit.inv (isUnit_iff_ne_zero.mpr
        (leadingCoeff_ne_zero.mpr hirr.ne_zero)))
    exact Separable.mul_unit (eisensteinPolyK_separable π hπ n hq) hu
  have hint := hroot.isIntegral
  have hsep : Algebra.IsSeparable K
      (IntermediateField.adjoin K {AdjoinRoot.root (eisensteinPolyK π n q : K[X])}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K
      (AdjoinRoot (eisensteinPolyK π n q : K[X]))).mpr hroot
  have htop : IntermediateField.adjoin K
      {AdjoinRoot.root (eisensteinPolyK π n q : K[X])} = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    rw [IntermediateField.top_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    have h := (AdjoinRoot.powerBasis hirr.ne_zero).adjoin_gen_eq_top
    rwa [AdjoinRoot.powerBasis_gen hirr.ne_zero] at h
  rw [htop] at hsep
  exact Algebra.IsSeparable.of_algHom K _ (IntermediateField.topEquiv.symm.toAlgHom)

/-- The adjoined root is integral over `A`, being a root of the monic polynomial
`eisensteinPolyA π n q`. -/
private lemma root_mem_integralClosure {A : Type u} {K : Type v} [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] (π : A) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    AdjoinRoot.root (eisensteinPolyK π n q : K[X]) ∈
      integralClosure A (eisensteinExt (K := K) π n q) :=
  ⟨eisensteinPolyA π n q, eisensteinPolyA_monic π n hq, by
    rw [← aeval_def]; exact aeval_root_eisensteinPolyA π n q⟩

/-- The adjoined root, as an element of the integral closure, satisfies the defining relation. -/
private lemma root_relation_integralClosure {A : Type u} {K : Type v} [CommRing A]
    [IsDomain A] [Field K] [Algebra A K] (π : A) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    (⟨AdjoinRoot.root (eisensteinPolyK π n q : K[X]), root_mem_integralClosure π n hq⟩ :
        integralClosure A (eisensteinExt (K := K) π n q)) ^ q =
      algebraMap A (integralClosure A (eisensteinExt (K := K) π n q)) π +
        algebraMap A (integralClosure A (eisensteinExt (K := K) π n q)) (π ^ (n + q - 1)) *
          ⟨AdjoinRoot.root (eisensteinPolyK π n q : K[X]),
            root_mem_integralClosure π n hq⟩ :=
  Subtype.ext (root_relation (K := K) π n q)

/-- The integral closure of `A` in the extension is `A[α]`, by the standard Eisenstein
criterion for integral closures. -/
private lemma integralClosure_eq_adjoin {A : Type u} {K : Type v} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    integralClosure A (eisensteinExt (K := K) π n q) =
      Algebra.adjoin A {AdjoinRoot.root (eisensteinPolyK π n q : K[X])} := by
  let : Fact (Irreducible (eisensteinPolyK π n q : K[X])) :=
    ⟨eisensteinPolyK_irreducible π hπ n hq⟩
  let L := eisensteinExt (K := K) π n q
  let α : L := AdjoinRoot.root (eisensteinPolyK π n q : K[X])
  have hαmem : α ∈ integralClosure A L := root_mem_integralClosure π n hq
  have hαint : IsIntegral A α := hαmem
  apply le_antisymm
  · intro z hz
    have hzInt : IsIntegral A z := hz
    let pbK := AdjoinRoot.powerBasis (f := (eisensteinPolyK π n q : K[X]))
      (eisensteinPolyK_irreducible π hπ n hq).ne_zero
    have hgenK : pbK.gen = α := by simp [pbK, α, AdjoinRoot.powerBasis_gen]
    have hmonic : (eisensteinPolyA π n q).Monic := eisensteinPolyA_monic π n hq
    have hKirr : Irreducible (eisensteinPolyA π n q) := eisensteinPolyA_irreducible π hπ n hq
    have hmpEval : (aeval α) (eisensteinPolyA π n q) = 0 := aeval_root_eisensteinPolyA π n q
    have hTF : Module.IsTorsionFree A L := isTorsionFree_eisensteinExt π hπ n hq
    have hmpdvd : minpoly A α ∣ eisensteinPolyA π n q :=
      minpoly.isIntegrallyClosed_dvd hαint hmpEval
    have hminpoly : minpoly A α = eisensteinPolyA π n q := by
      apply eq_of_monic_of_associated (minpoly.monic hαint) hmonic
      obtain ⟨c, hc⟩ := hmpdvd
      rcases hKirr.isUnit_or_isUnit hc with hu | hu
      · exact absurd hu (minpoly.not_isUnit A α)
      · exact ⟨hu.unit, by rw [hc]; rfl⟩
    have hEisMin : (minpoly A pbK.gen).IsEisensteinAt (Ideal.span {π}) := by
      rw [hgenK, hminpoly]
      exact eisensteinPolyA_eisenstein π hπ n hq
    have hclear : ∃ m : ℕ, π ^ m • z ∈ Algebra.adjoin A {α} := by
      obtain ⟨f, _, hfz⟩ := pbK.exists_eq_aeval z
      obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A)
        (Finset.range (f.natDegree + 1)) (fun i ↦ f.coeff i)
      have hbne : (b : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b
      obtain ⟨m, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbne hπ
      refine ⟨m, ?_⟩
      have hbz : (b : A) • z ∈ Algebra.adjoin A {α} := by
        rw [← IsScalarTower.algebraMap_smul K (b : A) z]
        have hsmul : (algebraMap A K (b : A)) • z =
            (aeval α) (Polynomial.C (algebraMap A K (b : A)) * f) := by
          rw [map_mul, aeval_C, hfz, ← hgenK, Algebra.smul_def]
        rw [hsmul]
        let g : K[X] := Polynomial.C (algebraMap A K (b : A)) * f
        have hlift : g ∈ Polynomial.lifts (algebraMap A K) := by
          rw [Polynomial.lifts_iff_coeff_lifts]
          intro i
          rcases le_or_gt (f.natDegree + 1) i with hi | hi
          · refine ⟨0, ?_⟩
            rw [map_zero, show g = Polynomial.C (algebraMap A K (b : A)) * f from rfl,
              coeff_C_mul, f.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
          · obtain ⟨a, ha⟩ := hb i (Finset.mem_range.mpr hi)
            refine ⟨a, ?_⟩
            rw [Algebra.smul_def] at ha
            rw [show g = Polynomial.C (algebraMap A K (b : A)) * f from rfl, coeff_C_mul, ha]
        obtain ⟨gA, hgA⟩ := hlift
        change (aeval α) g ∈ Algebra.adjoin A {α}
        rw [← hgA, Polynomial.coe_mapRingHom, Polynomial.aeval_map_algebraMap]
        exact aeval_mem_adjoin_singleton A _
      have key : (π ^ m : A) • z = ((u⁻¹ : Aˣ) : A) • ((b : A) • z) := by
        rw [smul_smul, hbu]
        congr 1
        rw [← mul_assoc]
        simp
      rw [key]
      exact Subalgebra.smul_mem _ hbz _
    obtain ⟨m, hm⟩ := hclear
    have hzmem := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
      (R := A) (K := K) (L := L) (B := pbK) hπ.prime
      (by rw [hgenK]; exact hαint) hzInt (n := m) (by rw [hgenK]; exact hm) hEisMin
    rw [hgenK] at hzmem
    exact hzmem
  · exact adjoin_le_integralClosure hαint

/-- The integral closure of `A` in the extension is a finite `A`-module. -/
private lemma finite_integralClosure_eisensteinExt {A : Type u} {K : Type v} [CommRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ} (hq : 2 ≤ q) :
    Module.Finite A (integralClosure A (eisensteinExt (K := K) π n q)) := by
  rw [integralClosure_eq_adjoin π hπ n hq]
  exact Algebra.finite_adjoin_simple_of_isIntegral (root_mem_integralClosure π n hq)

/-- The integral closure is a discrete valuation ring whose maximal ideal is generated by the
adjoined root. -/
private lemma integralClosure_dvr_and_irreducible_root {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ} (hq : 2 ≤ q)
    [Fact (Irreducible (eisensteinPolyK π n q : K[X]))] :
    IsDiscreteValuationRing (integralClosure A (eisensteinExt (K := K) π n q)) ∧
      Irreducible (⟨AdjoinRoot.root (eisensteinPolyK π n q : K[X]),
        root_mem_integralClosure π n hq⟩ :
          integralClosure A (eisensteinExt (K := K) π n q)) := by
  let L := eisensteinExt (K := K) π n q
  let B := integralClosure A L
  let α : L := AdjoinRoot.root (eisensteinPolyK π n q : K[X])
  have hαmem : α ∈ B := root_mem_integralClosure π n hq
  let β : B := ⟨α, hαmem⟩
  have hclosure : B = Algebra.adjoin A {α} := integralClosure_eq_adjoin π hπ n hq
  have hrel : β ^ q = algebraMap A B π + algebraMap A B (π ^ (n + q - 1)) * β :=
    root_relation_integralClosure π n hq
  have hπspan : algebraMap A B π ∈ Ideal.span {β} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨β ^ (q - 1) - algebraMap A B (π ^ (n + q - 1)), ?_⟩
    have hq1 : q - 1 + 1 = q := by omega
    rw [mul_sub, ← pow_succ', hq1]
    linear_combination -hrel
  have hconst : ∀ z : B, ∃ a : A,
      z - algebraMap A B a ∈ Ideal.span {β} := by
    intro z
    have hz : (z : L) ∈ Algebra.adjoin A {α} := by
      rw [← hclosure]
      exact z.property
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨f, hf⟩ := hz
    have hdvd : (X : A[X]) ∣ f - C (f.coeff 0) := by
      rw [X_dvd_iff]
      simp
    obtain ⟨g, hg⟩ := hdvd
    have hgmem : (aeval α) g ∈ B := by
      rw [hclosure]
      exact aeval_mem_adjoin_singleton A _
    let t : B := ⟨(aeval α) g, hgmem⟩
    refine ⟨f.coeff 0, ?_⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨t, ?_⟩
    apply Subtype.ext
    change (z : L) - (algebraMap A L) (f.coeff 0) = α * (aeval α) g
    rw [← hf]
    calc
      (aeval α) f - (algebraMap A L) (f.coeff 0) =
          (aeval α) (f - C (f.coeff 0)) := by simp
      _ = α * (aeval α) g := by rw [hg, map_mul, aeval_X]
  have hπmax : π ∈ IsLocalRing.maximalIdeal A := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have hmeq : ∀ M : Ideal B, M.IsMaximal →
      Ideal.comap (algebraMap A B) M = IsLocalRing.maximalIdeal A := fun M hM =>
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (hI := hM) M)
  have hmax_contains : ∀ M : Ideal B, M.IsMaximal → β ∈ M := by
    intro M hM
    have hπM : algebraMap A B π ∈ M := by
      have : π ∈ Ideal.comap (algebraMap A B) M := by rw [hmeq M hM]; exact hπmax
      exact this
    have hpowM : β ^ q ∈ M := by
      rw [hrel]
      apply Ideal.add_mem M hπM
      exact M.mul_mem_right β (by
        simpa only [map_pow] using
          (M.pow_mem_of_mem hπM (n + q - 1) (by omega)))
    exact hM.isPrime.mem_of_pow_mem q hpowM
  have hspan_le : ∀ M : Ideal B, M.IsMaximal → Ideal.span {β} ≤ M := fun M hM => by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hmax_contains M hM
  have hmax_le : ∀ M : Ideal B, M.IsMaximal → M ≤ Ideal.span {β} := by
    intro M hM z hz
    obtain ⟨a, ha⟩ := hconst z
    have hmapa : algebraMap A B a ∈ M := by
      have hsub : z - algebraMap A B a ∈ M := hspan_le M hM ha
      have h : z - (z - algebraMap A B a) ∈ M := Ideal.sub_mem M hz hsub
      convert h using 1
      ring
    have haA : a ∈ IsLocalRing.maximalIdeal A := by
      rw [← hmeq M hM]
      exact hmapa
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at haA
    obtain ⟨c, rfl⟩ := haA
    have hmapspan : algebraMap A B (π * c) ∈ Ideal.span {β} := by
      rw [map_mul]
      exact Ideal.mul_mem_right _ _ hπspan
    have : z = (z - algebraMap A B (π * c)) + algebraMap A B (π * c) := by ring
    rw [this]
    exact Ideal.add_mem _ ha hmapspan
  obtain ⟨M, hM, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal B) bot_ne_top
  have hMeq : M = Ideal.span {β} := le_antisymm (hmax_le M hM) (hspan_le M hM)
  have hlocal : IsLocalRing B := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨M, hM, ?_⟩
    intro N hN
    have hNle : N ≤ M := by rw [hMeq]; exact hmax_le N hN
    exact hN.eq_of_le hM.ne_top hNle
  have hmaxeq : IsLocalRing.maximalIdeal B = Ideal.span {β} := by
    rw [← hMeq]
    exact (IsLocalRing.eq_maximalIdeal hM).symm
  have hfin : Module.Finite A B := finite_integralClosure_eisensteinExt π hπ n hq
  have hnoeth : IsNoetherianRing B := by
    have : IsNoetherian B B := isNoetherian_of_tower A inferInstance
    rwa [isNoetherianRing_iff]
  have hmax_ne : IsLocalRing.maximalIdeal B ≠ ⊥ := by
    rw [hmaxeq]
    intro hb
    have hβ0 : β = 0 := Ideal.span_singleton_eq_bot.mp hb
    have hπ0 : algebraMap A B π = 0 := by
      rw [hβ0] at hrel
      simpa [zero_pow (by omega : q ≠ 0)] using hrel.symm
    have hπL : algebraMap A L π = 0 := congrArg Subtype.val hπ0
    have hπK : algebraMap A K π = 0 := (algebraMap K L).injective (by
      rw [← IsScalarTower.algebraMap_apply A K L]
      simpa using hπL)
    exact hπ.ne_zero ((IsFractionRing.injective A K) (by simpa using hπK))
  have hprinc : Submodule.IsPrincipal (IsLocalRing.maximalIdeal B) := by
    rw [hmaxeq]
    exact ⟨β, by rw [Ideal.submodule_span_eq]⟩
  have hpir : IsPrincipalIdealRing B :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain B).out 5 1).mp hprinc
  have hdvr : IsDiscreteValuationRing B := IsDiscreteValuationRing.mk hmax_ne
  have hβne : β ≠ 0 := by
    intro hβ0
    apply hmax_ne
    rw [hmaxeq, hβ0]
    simp
  have hirr : Irreducible β :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal β hβne hmaxeq
  exact ⟨hdvr, hirr⟩

/-- The ramification index of the extension is `q`, and `π` factors as the `q`-th power of the
adjoined root times a unit. -/
private lemma ramificationIdx_eq_of_eisenstein_relation {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ} (hq : 2 ≤ q)
    [Fact (Irreducible (eisensteinPolyK π n q : K[X]))]
    [IsDiscreteValuationRing (integralClosure A (eisensteinExt (K := K) π n q))] :
    Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal (integralClosure A (eisensteinExt (K := K) π n q))) = q ∧
      ∃ c : integralClosure A (eisensteinExt (K := K) π n q),
        algebraMap A (integralClosure A (eisensteinExt (K := K) π n q)) π =
          (⟨AdjoinRoot.root (eisensteinPolyK π n q : K[X]),
            root_mem_integralClosure π n hq⟩ :
              integralClosure A (eisensteinExt (K := K) π n q)) ^ q * c := by
  let L := eisensteinExt (K := K) π n q
  let B := integralClosure A L
  let α : L := AdjoinRoot.root (eisensteinPolyK π n q : K[X])
  let β : B := ⟨α, root_mem_integralClosure π n hq⟩
  have hpair := integralClosure_dvr_and_irreducible_root (K := K) π hπ n hq
  have hirr : Irreducible β := hpair.2
  have hrel : β ^ q = algebraMap A B π + algebraMap A B (π ^ (n + q - 1)) * β :=
    root_relation_integralClosure π n hq
  let v : B := 1 + algebraMap A B (π ^ (n + q - 2)) * β
  have he : n + q - 2 + 1 = n + q - 1 := by omega
  have hrel2 : β ^ q = algebraMap A B π * v := by
    rw [hrel]
    dsimp [v]
    rw [mul_add, mul_one, ← mul_assoc, ← map_mul, ← pow_succ', he]
  have hv : IsUnit v := by
    have hβmax : β ∈ IsLocalRing.maximalIdeal B := by
      rw [hirr.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self β
    have ha : algebraMap A B (π ^ (n + q - 2)) * β ∈
        IsLocalRing.maximalIdeal B :=
      Ideal.mul_mem_left _ _ hβmax
    have hneg : -(algebraMap A B (π ^ (n + q - 2)) * β) ∈ nonunits B :=
      (IsLocalRing.mem_maximalIdeal _).mp (neg_mem ha)
    have hu := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      (-(algebraMap A B (π ^ (n + q - 2)) * β)) hneg
    simpa [v] using hu
  obtain ⟨uv, huv⟩ := hv
  have hπeq : algebraMap A B π = β ^ q * (↑uv⁻¹ : B) := by
    rw [hrel2, ← huv]
    simp [mul_assoc]
  have hmapeq : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      (IsLocalRing.maximalIdeal B) ^ q := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      hirr.maximalIdeal_eq, Ideal.span_singleton_pow]
    apply le_antisymm
    · rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨↑uv⁻¹, hπeq⟩
    · rw [Ideal.span_singleton_le_span_singleton]
      exact ⟨v, hrel2⟩
  constructor
  · apply Ideal.ramificationIdx'_spec
    · rw [hmapeq]
    · rw [hmapeq]
      rw [hirr.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
        Ideal.span_singleton_le_span_singleton]
      intro hdvd
      obtain ⟨c, hc⟩ := hdvd
      have hne0 : (β ^ q : B) ≠ 0 := pow_ne_zero _ hirr.ne_zero
      have hcancel : β * c = 1 := by
        apply mul_left_cancel₀ hne0
        rw [mul_one]
        conv_rhs => rw [hc]
        rw [pow_succ]
        ring
      exact hirr.not_isUnit (IsUnit.of_mul_eq_one c hcancel)
  · exact ⟨↑uv⁻¹, hπeq⟩

-- `Ideal.inertiaDeg'` and `Ideal.ramificationIdx'` have no semantics-preserving replacement
-- here, exactly as in `Stacks.KummerExtension.IsTotallyRamified`.
set_option linter.deprecated false in
/-- A finite extension of DVR fraction fields with one maximal ideal and full ramification
index has residue-field degree one, hence is totally ramified. -/
private lemma isTotallyRamified_of_ramificationIdx_eq_finrank
    (A : Type u) (K : Type v) (L : Type w) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Module.Finite K L]
    [IsDiscreteValuationRing (integralClosure A L)]
    [IsFractionRing (integralClosure A L) L]
    [Module.Finite A (integralClosure A L)]
    [Module.IsTorsionFree A (integralClosure A L)]
    (hmaxne : IsLocalRing.maximalIdeal A ≠ ⊥)
    (q : ℕ) (hqpos : 0 < q)
    (hdegree : Module.finrank K L = q)
    (hram : Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal (integralClosure A L)) = q) :
    Stacks.KummerExtension.IsTotallyRamified A K L := by
  let B := integralClosure A L
  let m : Ideal B := IsLocalRing.maximalIdeal B
  have hmmax : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal B
  have hcomap : (Ideal.comap (algebraMap A B) m).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) (hI := hmmax) m
  have hmlies : m.LiesOver (IsLocalRing.maximalIdeal A) := by
    refine ⟨?_⟩
    exact (IsLocalRing.eq_maximalIdeal hcomap).symm
  have hmuniq : ∀ m' : Ideal B, m'.IsMaximal →
      m'.LiesOver (IsLocalRing.maximalIdeal A) → m' = m := by
    intro m' hm' _
    exact IsLocalRing.eq_maximalIdeal hm'
  refine ⟨m, hmmax, hmlies, hmuniq, ?_⟩
  let p : Ideal A := IsLocalRing.maximalIdeal A
  have hpne : p ≠ ⊥ := hmaxne
  have hprimes : IsDedekindDomain.primesOverFinset p B = {m} := by
    apply Finset.coe_injective
    rw [IsDedekindDomain.coe_primesOverFinset hpne B]
    rw [Finset.coe_singleton]
    ext P
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Ideal.primesOver]
    constructor
    · rintro ⟨hPprime, hPlies⟩
      have hPne : P ≠ ⊥ := by
        intro hP0
        apply hpne
        have := hPlies.over
        rw [hP0] at this
        rwa [Ideal.under_bot] at this
      have hPmax : P.IsMaximal := hPprime.isMaximal hPne
      exact hmuniq P hPmax hPlies
    · rintro rfl
      exact ⟨hmmax.isPrime, hmlies⟩
  have hsum := Ideal.sum_ramification_inertia B K L hpne
  rw [hprimes, Finset.sum_singleton, hram, hdegree] at hsum
  have h : q * Ideal.inertiaDeg' p m = q * 1 := by rw [hsum, mul_one]
  exact Nat.eq_of_mul_eq_mul_left hqpos h

-- `Ideal.inertiaDeg'` and `Ideal.ramificationIdx'` have no semantics-preserving replacement
-- here, exactly as in `Stacks.KummerExtension.IsTotallyRamified`.
set_option linter.deprecated false in
/-- The extension is totally ramified with respect to `A`. -/
private lemma isTotallyRamified_of_eisenstein_relation {A : Type u} {K : Type v}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (n : ℕ) {q : ℕ} (hq : 2 ≤ q)
    [Fact (Irreducible (eisensteinPolyK π n q : K[X]))]
    [Module.Finite K (eisensteinExt (K := K) π n q)]
    [IsDiscreteValuationRing (integralClosure A (eisensteinExt (K := K) π n q))] :
    Stacks.KummerExtension.IsTotallyRamified A K (eisensteinExt (K := K) π n q) := by
  have hfr : IsFractionRing (integralClosure A (eisensteinExt (K := K) π n q))
      (eisensteinExt (K := K) π n q) :=
    integralClosure.isFractionRing_of_finite_extension K _
  have : Module.IsTorsionFree A (eisensteinExt (K := K) π n q) :=
    isTorsionFree_eisensteinExt π hπ n hq
  have := finite_integralClosure_eisensteinExt (K := K) π hπ n hq
  exact isTotallyRamified_of_ramificationIdx_eq_finrank A K _
    (by rw [hπ.maximalIdeal_eq]; simpa using hπ.ne_zero) q (by omega)
    (finrank_eisensteinExt π hπ n hq)
    (ramificationIdx_eq_of_eisenstein_relation (K := K) π hπ n hq).1

-- `Ideal.ramificationIdx'` has no semantics-preserving replacement here, exactly as in
-- `Stacks.KummerExtension.IsTotallyRamified`.
set_option linter.deprecated false in
/-- Let `A` be a discrete valuation ring with fraction field `K` and residue characteristic
`p > 0`, with uniformizer `π`, and let `n > 1`. For every power `q` of `p` there is a separable
extension `L / K` of degree `q`, totally ramified with respect to `A` with ramification index
`q`, whose integral closure `B` of `A` is a discrete valuation ring with a uniformizer `π_B`
satisfying `π_B^q = π + π^n b` and `π_B^q = π + π_B^{nq} b'` for some `b, b'` in `B`. -/
@[stacks 09EW]
theorem exists_totallyRamifiedExtension_with_uniformizer_eq
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : Irreducible π) (p n q : ℕ)
    (hp : 0 < p)
    (_hres : ringChar (A ⧸ IsLocalRing.maximalIdeal A) = p)
    (hn : 1 < n) (hq : ∃ r : ℕ, q = p ^ r) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra K L) (_ : Algebra A L)
      (_ : IsScalarTower A K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L)
      (_ : IsDiscreteValuationRing (integralClosure A L)),
      Module.finrank K L = q ∧
        Stacks.KummerExtension.IsTotallyRamified A K L ∧
        Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A)
            (IsLocalRing.maximalIdeal (integralClosure A L)) = q ∧
        ∃ πB b b' : integralClosure A L,
          Irreducible πB ∧
            πB ^ q = algebraMap A (integralClosure A L) π +
              (algebraMap A (integralClosure A L) π) ^ n * b ∧
            πB ^ q = algebraMap A (integralClosure A L) π + πB ^ (n * q) * b' := by
  by_cases hbig : 2 ≤ q
  · let L := eisensteinExt (K := K) π n q
    have hirr : Irreducible (eisensteinPolyK π n q : K[X]) :=
      eisensteinPolyK_irreducible π hπ n hbig
    let : Fact (Irreducible (eisensteinPolyK π n q : K[X])) := ⟨hirr⟩
    let : Module.Finite K L := (AdjoinRoot.powerBasis hirr.ne_zero).finite
    have hsep : Algebra.IsSeparable K L := isSeparable_eisensteinExt π hπ n hbig
    have hpair := integralClosure_dvr_and_irreducible_root (K := K) π hπ n hbig
    let : IsDiscreteValuationRing (integralClosure A L) := hpair.1
    let B := integralClosure A L
    let β : B := ⟨AdjoinRoot.root (eisensteinPolyK π n q : K[X]),
      root_mem_integralClosure π n hbig⟩
    have hβirr : Irreducible β := hpair.2
    obtain ⟨hram, c, hπeq⟩ :=
      ramificationIdx_eq_of_eisenstein_relation (K := K) π hπ n hbig
    let b : B := (algebraMap A B π) ^ (q - 1) * β
    have hrel : β ^ q = algebraMap A B π + algebraMap A B (π ^ (n + q - 1)) * β :=
      root_relation_integralClosure π n hbig
    have hb : β ^ q = algebraMap A B π + (algebraMap A B π) ^ n * b := by
      rw [hrel]
      dsimp [b]
      rw [map_pow, ← mul_assoc, ← pow_add]
      rw [show n + (q - 1) = n + q - 1 by omega]
    let b' : B := c ^ n * b
    have hb' : β ^ q = algebraMap A B π + β ^ (n * q) * b' := by
      rw [hb]
      congr 1
      dsimp [b']
      rw [hπeq, mul_pow, ← pow_mul]
      rw [Nat.mul_comm q n]
      ring
    refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, hsep, inferInstance, ?_, ?_, ?_, ?_⟩
    · exact finrank_eisensteinExt π hπ n hbig
    · exact isTotallyRamified_of_eisenstein_relation (K := K) π hπ n hbig
    · exact hram
    · exact ⟨β, b, b', hβirr, hb, hb'⟩
  · obtain ⟨r, hr⟩ := hq
    have hp1 : 1 ≤ p := hp
    have hq1 : q = 1 := by
      have : 1 ≤ p ^ r := one_le_pow₀ hp1
      omega
    subst q
    let B := integralClosure A K
    have hbot : B = (⊥ : Subalgebra A K) :=
      (IsIntegrallyClosed.integralClosure_eq_bot_iff K).mpr inferInstance
    let e : B ≃ₐ[A] A :=
      (Subalgebra.equivOfEq _ _ hbot).trans
        (Algebra.botEquivOfInjective (IsFractionRing.injective A K))
    let : IsDiscreteValuationRing B :=
      IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
    let β : B := algebraMap A B π
    have hβeq : β = e.symm π := by
      simp [β]
    have hβirr : Irreducible β := by
      rw [hβeq]
      exact hπ.map e.symm
    have hmapeq : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal B := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
        hβirr.maximalIdeal_eq]
    have hram : Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal B) = 1 := by
      apply Ideal.ramificationIdx'_spec
      · rw [hmapeq]; simp
      · rw [hmapeq]
        rw [hβirr.maximalIdeal_eq, Ideal.span_singleton_pow,
          Ideal.span_singleton_le_span_singleton]
        intro hdvd
        obtain ⟨c, hc⟩ := hdvd
        have hcancel : β * c = 1 := by
          apply mul_left_cancel₀ hβirr.ne_zero
          rw [mul_one]
          conv_rhs => rw [hc]
          ring
        exact hβirr.not_isUnit (IsUnit.of_mul_eq_one c hcancel)
    have : IsFractionRing B K :=
      integralClosure.isFractionRing_of_finite_extension K K
    have : Module.Finite A B := Module.Finite.equiv e.symm.toLinearEquiv
    have : Module.IsTorsionFree A B := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]
      intro a b hab
      have heq := congrArg e hab
      simpa using heq
    have hmaxne : IsLocalRing.maximalIdeal A ≠ ⊥ := by
      rw [hπ.maximalIdeal_eq]
      intro h
      rw [Ideal.span_singleton_eq_bot] at h
      exact hπ.ne_zero h
    have htot : Stacks.KummerExtension.IsTotallyRamified A K K :=
      isTotallyRamified_of_ramificationIdx_eq_finrank A K K hmaxne 1
        (by omega) (by simp) hram
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
    · rw [hq1]; simp
    · exact htot
    · rw [hq1]; exact hram
    · refine ⟨β, 0, 0, hβirr, ?_, ?_⟩ <;> simp [hq1, β] <;> rfl

end Stacks.EisensteinExtension
