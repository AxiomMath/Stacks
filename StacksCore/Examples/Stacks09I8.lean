module

public import Mathlib.Analysis.Complex.IsIntegral
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.NumberTheory.Niven
public import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
public import StacksCore.FieldTheory.PurelyTranscendental

/-! # ℚ(π) -/

@[expose] public section

open Real IntermediateField

open Polynomial Complex in
/-- **Stacks 09I8**.
The real number `π` is transcendental over `ℚ`: it is not a root of any nonzero polynomial with
rational coefficients (Lindemann, *Über die Zahl π*, Math. Ann. 20 (1882), 213–225). If it were,
the conjugates `α` of `π i` would satisfy `∏ (1 + exp α) = 0`, contradicting the estimate
`LindemannWeierstrass.exp_polynomial_approx`. -/
@[stacks 09I8]
theorem transcendental_pi : Transcendental ℚ π := by
  intro hπ
  have hα : IsIntegral ℚ (π * I : ℂ) :=
    ((hπ.algebraMap (A := ℂ)).mul (isIntegral_I ℚ).isAlgebraic).isIntegral
  set q := minpoly ℚ (π * I : ℂ)
  set L := IntermediateField.adjoin ℚ (q.rootSet ℂ)
  have hsplit := IntermediateField.adjoin_rootSet_isSplittingField
    (IsAlgClosed.splits (q.map (algebraMap ℚ ℂ)))
  have : FiniteDimensional ℚ L := @IsSplittingField.finiteDimensional ℚ _ _ _ _ q hsplit
  have : IsGalois ℚ L := @IsGalois.of_separable_splitting_field ℚ _ _ _ _ q hsplit
    (minpoly.irreducible hα).separable
  have : Algebra.IsAlgebraic ℤ L :=
    (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).mpr inferInstance
  set s := (q.aroots L).toFinset
  have hs (σ : L ≃ₐ[ℚ] L) : s.image σ = s := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_)
      (Finset.card_image_of_injective _ σ.injective).ge
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    simp_all [s, aeval_algHom_apply]
  have hinv (F : L → L) (hF : ∀ (σ : L ≃ₐ[ℚ] L) x, σ (F x) = F (σ x)) :
      ∃ r : ℚ, algebraMap ℚ L r = ∑ t ∈ s.powerset, F (∑ i ∈ t, i) := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr fun σ => ?_
    conv_rhs => rw [← hs σ, Finset.powerset_image,
      Finset.sum_image (Finset.image_injective σ.injective).injOn]
    simp [hF, map_sum, Finset.sum_image σ.injective.injOn]
  have hP (x : L) : ∃ P : ℤ[X], P.eval 0 ≠ 0 ∧ (x ≠ 0 → aeval x P = 0) := by
    by_cases hx : x = 0
    · exact ⟨1, by simp, fun h => (h hx).elim⟩
    obtain ⟨p, hp, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x
    obtain ⟨P, hpP, hP⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
    refine ⟨P, by simpa [X_dvd_iff, coeff_zero_eq_eval_zero] using hP, fun _ => ?_⟩
    rw [hpP] at hpx
    simpa [hx] using hpx
  choose P hP0 hPx using hP
  set f := ∏ t ∈ s.powerset, P (∑ i ∈ t, i)
  have hf0 : f.eval 0 ≠ 0 := by simp [f, eval_prod, Finset.prod_ne_zero_iff, hP0]
  obtain ⟨d, hd0, hd⟩ := Algebra.IsAlgebraic.exists_integral_multiples (R := ℤ) s
  have hexp : ∑ t ∈ s.powerset, exp (∑ i ∈ t, i : L) = 0 := by
    set a : L := ⟨π * I, IntermediateField.subset_adjoin _ _
      (by simp [q, mem_rootSet, minpoly.ne_zero hα])⟩
    have ha : a ∈ s := by
      simpa [s, mem_aroots] using And.intro (minpoly.ne_zero hα)
        ((aeval_algebraMap_apply ℂ a q).symm.trans (minpoly.aeval ℚ _))
    rw [← Finset.prod_eq_zero (f := fun i : L => 1 + exp i) ha
      (show 1 + exp (π * I) = 0 by simp [exp_pi_mul_I]), Finset.prod_one_add]
    simp [Complex.exp_sum]
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  set Z := s.powerset.filter (fun t => ∑ i ∈ t, i ≠ 0)
  set k := (s.powerset.filter (fun t => ¬ ∑ i ∈ t, i ≠ 0)).card
  have hk : 0 < k := Finset.card_pos.mpr ⟨∅, by simp⟩
  have hZ : ∑ t ∈ Z, exp (∑ i ∈ t, i : L) = -k := by
    rw [eq_neg_iff_add_eq_zero, ← hexp, ← Finset.sum_filter_add_sum_filter_not s.powerset
      (fun t => ∑ i ∈ t, i ≠ 0)]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) fun t ht => by
      rw [(by simpa using (Finset.mem_filter.mp ht).2 : ∑ i ∈ t, i = 0)]; simp]
    simp [k]
  set e := |(d : ℝ)| ^ f.natDegree * |c|
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp <|
    ((FloorSemiring.tendsto_pow_div_factorial_atTop e).const_mul (Z.card * e)).eventually
      (gt_mem_nhds (by simp : (Z.card * e * 0 : ℝ) < 1))
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + (f.eval 0).natAbs + d.natAbs + k + 2)
  obtain ⟨n, hn, g, hg, hb⟩ := hc p (by omega) hp
  set D := p * f.natDegree
  obtain ⟨r, hr⟩ := hinv (fun x => if x ≠ 0 then aeval x g else 0) fun σ x => by
    by_cases hx : x = 0
    · simp [hx]
    · simpa [hx] using (aeval_algHom_apply ((σ : L →ₐ[ℚ] L).restrictScalars ℤ) x g).symm
  rw [← Finset.sum_filter] at hr
  have hint : IsIntegral ℤ ((d : L) ^ D * ∑ t ∈ Z, aeval (∑ i ∈ t, i) g) := by
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun t ht => ?_
    have h1 : IsIntegral ℤ (d • ∑ i ∈ t, i) := by
      rw [Finset.smul_sum]
      exact .sum _ fun i hi => hd i (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1 hi)
    rw [← Nat.sub_add_cancel (show g.natDegree ≤ D by omega), pow_add, mul_assoc,
      show (d : L) ^ g.natDegree * aeval (∑ i ∈ t, i) g =
        aeval (d • ∑ i ∈ t, i) (g.scaleRoots d) by
        rw [scaleRoots_aeval_smul, zsmul_eq_mul, Int.cast_pow]]
    exact .mul (.pow (by simpa using isIntegral_algebraMap (R := ℤ) (A := L) (x := d)) _)
      (by simpa [aeval_subalgebra_coe, mem_integralClosure_iff] using
        (aeval (⟨_, h1⟩ : integralClosure ℤ L) (g.scaleRoots d)).2)
  obtain ⟨z, hz⟩ := hint.exists_int_iff_exists_rat.mp ⟨d ^ D * r, by simp [Z, ← hr]⟩
  have hzC : (z : ℂ) = (d : ℂ) ^ D * ∑ t ∈ Z, aeval ((∑ i ∈ t, i : L) : ℂ) g := by
    have := congrArg (algebraMap L ℂ) hz
    rw [map_mul, map_pow, map_intCast, map_sum] at this
    simp only [← aeval_algebraMap_apply] at this
    exact this
  have hroot (t) (ht : t ∈ Z) : ((∑ i ∈ t, i : L) : ℂ) ∈ f.aroots ℂ := by
    have : aeval (∑ i ∈ t, i) f = 0 := by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_filter.mp ht).1 (hPx _ (Finset.mem_filter.mp ht).2)
    refine mem_aroots.mpr ⟨fun h => hf0 (by simp [h]), ?_⟩
    rw [show ((∑ i ∈ t, i : L) : ℂ) = algebraMap L ℂ (∑ i ∈ t, i) from rfl,
      aeval_algebraMap_apply, this, map_zero]
  have key : ‖∑ t ∈ Z, (n • exp (∑ i ∈ t, i : L) - p • aeval ((∑ i ∈ t, i : L) : ℂ) g)‖ ≤
      Z.card * (|c| ^ p / ((p - 1).factorial : ℝ)) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ fun t ht =>
      (hb (hroot t ht)).trans ?_).trans (nsmul_eq_mul _ _).le)
    exact div_le_div_of_nonneg_right ((le_abs_self _).trans (abs_pow c p).le) (by positivity)
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hZ] at key
  set M : ℤ := -(d ^ D * n * k) - p * z
  have hMC : (M : ℂ) =
      (d : ℂ) ^ D * (n • -(k : ℂ) - p • ∑ t ∈ Z, aeval ((∑ i ∈ t, i : L) : ℂ) g) := by
    simp only [M, zsmul_eq_mul, nsmul_eq_mul]; push_cast at hzC ⊢; rw [hzC]; ring
  have hM0 : M ≠ 0 := by
    intro hM0
    have hp' := Nat.prime_iff_prime_int.mp hp
    have : (p : ℤ) ∣ d ^ D * n * k := ⟨-z, by linarith⟩
    simp only [hp'.dvd_mul] at this
    rcases this with (h | h) | h
    · exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hd0)
        (Int.natCast_dvd.mp (hp'.dvd_of_dvd_pow h))) (by omega)
    · exact hn h
    · exact absurd (Nat.le_of_dvd hk (Int.natCast_dvd_natCast.mp h)) (by omega)
  have h1 : (1 : ℝ) ≤ |(M : ℝ)| := by exact_mod_cast Int.one_le_abs hM0
  have h2 : |(M : ℝ)| ≤ |(d : ℝ)| ^ D * (Z.card * (|c| ^ p / ((p - 1).factorial : ℝ))) := by
    rw [← Complex.norm_intCast, hMC, norm_mul, norm_pow, Complex.norm_intCast]
    gcongr
  have h3 := hN (p - 1) (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have : |(d : ℝ)| ^ D * (Z.card * (|c| ^ (m + 1) / ((m + 1 - 1).factorial : ℝ))) =
      Z.card * e * (e ^ (m + 1 - 1) / ((m + 1 - 1).factorial : ℝ)) := by
    simp only [D, e, Nat.add_sub_cancel]; ring
  linarith

attribute [-instance] DivisionRing.toRatAlgebra

/-- **Stacks 09I8**.
Because `π` is transcendental over `ℚ`, the simple extension `ℚ(π)` is `ℚ`-algebra isomorphic to
the field of rational functions `RatFunc ℚ`. -/
@[stacks 09I8]
noncomputable def adjoinPiAlgEquivRatFunc : ℚ⟮π⟯ ≃ₐ[ℚ] RatFunc ℚ :=
  RatFunc.algEquivOfTranscendental _ transcendental_pi |>.symm

/-- **Stacks 09I8**.
The extension `ℚ(π)/ℚ` is purely transcendental, witnessed by the transcendental element `π`. -/
@[stacks 09I8]
instance purelyTranscendental_adjoinPi : PurelyTranscendental ℚ ℚ⟮π⟯ :=
  transcendental_pi.purelyTranscendental_adjoin
