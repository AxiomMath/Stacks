module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.GradedAlgebra.Examples.WeightedPolynomialTwists

/-!
# The first two localized twists in the weighted polynomial example

Let `S = k[x, y, z]` be the polynomial ring in three variables graded by the weights `1`, `2`
and `3`, and let `S₍z₎ ⊆ S_z` be the degree-zero localization at `z`. This file computes the
degree-zero localizations of the first two twists `S(1)` and `S(2)` as explicit `S₍z₎`-submodules
of the ordinary localization `S_z`:

* `S(1)₍z₎ = S₍z₎ · x + S₍z₎ · (y² / z)`,
* `S(2)₍z₎ = S₍z₎ · y + S₍z₎ · x²`.

## Main results

* `Stacks.WeightedPolynomialSituation.firstTwistLocalization_eq_span`: the degree-zero
  localization of `S(1)` is spanned by `x` and `y² / z`.
* `Stacks.WeightedPolynomialSituation.secondTwistLocalization_eq_span`: the degree-zero
  localization of `S(2)` is spanned by `y` and `x²`.

## References

* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
-/

@[expose] public noncomputable section

namespace Stacks.WeightedPolynomialSituation

private theorem z_mem_naturalGrading (E : WeightedPolynomialSituation) :
    E.z ∈ E.naturalGrading (E.naturalWeight 2) := by
  change MvPolynomial.IsWeightedHomogeneous E.naturalWeight E.z (E.naturalWeight 2)
  exact MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 2

/-- Multiplying `m / s` by the degree-zero element `q / z ^ j` gives `q * m / t`, where
`t = z ^ j * s`. -/
private theorem away_mk_smul_mk (E : WeightedPolynomialSituation) (j : ℕ) (q : E.S)
    (hq : q ∈ E.naturalGrading (3 * j)) (m : E.S) (s t : Submonoid.powers E.z)
    (hts : (t : E.S) = E.z ^ j * s) :
    Localization.mk (q * m) t =
      HomogeneousLocalization.Away.mk (𝒜 := E.naturalGrading) (f := E.z)
        (z_mem_naturalGrading E) j q (by simpa [WeightedPolynomialSituation.naturalWeight,
          Nat.mul_comm] using hq) • Localization.mk m s := by
  rw [Algebra.smul_def, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  congr 1
  exact Subtype.ext hts

private theorem fraction_mul_x_mem_span (E : WeightedPolynomialSituation) (k : ℕ)
    (q : E.S) (hq : q ∈ E.naturalGrading (3 * k)) :
    Localization.mk (q * E.x)
        ⟨E.z ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) k⟩ ∈
      Submodule.span E.R
        {Localization.mk E.x (1 : Submonoid.powers E.z),
          Localization.mk (E.y ^ 2) ⟨E.z, Submonoid.mem_powers E.z⟩} := by
  rw [away_mk_smul_mk E k q hq E.x 1 _ (mul_one _).symm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem fraction_mul_y_sq_mem_span (E : WeightedPolynomialSituation) (k : ℕ)
    (q : E.S) (hk : 1 ≤ k) (hq : q ∈ E.naturalGrading (3 * (k - 1))) :
    Localization.mk (q * E.y ^ 2)
        ⟨E.z ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) k⟩ ∈
      Submodule.span E.R
        {Localization.mk E.x (1 : Submonoid.powers E.z),
          Localization.mk (E.y ^ 2) ⟨E.z, Submonoid.mem_powers E.z⟩} := by
  rw [away_mk_smul_mk E (k - 1) q hq (E.y ^ 2) ⟨E.z, Submonoid.mem_powers E.z⟩ _
    (by simp [← pow_succ, Nat.sub_add_cancel hk])]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))


private theorem exponent_weight_formula (E : WeightedPolynomialSituation)
    (a : Fin 3 →₀ ℕ) :
    Finsupp.weight E.naturalWeight a = a 0 + 2 * a 1 + 3 * a 2 := by
  rw [Finsupp.weight_eq_sum]
  simp [WeightedPolynomialSituation.naturalWeight, Fin.sum_univ_succ]
  ring

private theorem monomial_twist_fraction_mem_span (E : WeightedPolynomialSituation)
    (k : ℕ) (a : Fin 3 →₀ ℕ) (c : E.k)
    (ha : Finsupp.weight E.naturalWeight a = 3 * k + 1) :
    Localization.mk (MvPolynomial.monomial a c)
        ⟨E.z ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) k⟩ ∈
      Submodule.span E.R
        {Localization.mk E.x (1 : Submonoid.powers E.z),
          Localization.mk (E.y ^ 2) ⟨E.z, Submonoid.mem_powers E.z⟩} := by
  classical
  have hweight := exponent_weight_formula E a
  by_cases h0 : 0 < a 0
  · let b := a - Finsupp.single 0 1
    have hab : a = b + Finsupp.single 0 1 := by
      ext i
      fin_cases i
      · simp [b, Nat.sub_add_cancel (by omega : 1 ≤ a 0)]
      · simp [b]
      · simp [b]
    have hb : Finsupp.weight E.naturalWeight b = 3 * k := by
      rw [exponent_weight_formula]
      simp [b]
      omega
    rw [hab, MvPolynomial.monomial_add_single, pow_one]
    exact fraction_mul_x_mem_span E k _
      (MvPolynomial.isWeightedHomogeneous_monomial E.naturalWeight b c hb)
  · have h0' : a 0 = 0 := by omega
    have h1 : 2 ≤ a 1 := by omega
    let b := a - Finsupp.single 1 2
    have hab : a = b + Finsupp.single 1 2 := by
      ext i
      fin_cases i
      · simp [b, h0']
      · simp [b, Nat.sub_add_cancel (by omega : 2 ≤ a 1)]
      · simp [b]
    have hk : 1 ≤ k := by omega
    have hb : Finsupp.weight E.naturalWeight b = 3 * (k - 1) := by
      rw [exponent_weight_formula]
      simp [b]
      omega
    rw [hab, MvPolynomial.monomial_add_single]
    exact fraction_mul_y_sq_mem_span E k _ hk
      (MvPolynomial.isWeightedHomogeneous_monomial E.naturalWeight b c hb)

private theorem homogeneous_twist_fraction_mem_span (E : WeightedPolynomialSituation)
    (k : ℕ) (p : E.S) (hp : p ∈ E.naturalGrading (3 * k + 1)) :
    Localization.mk p ⟨E.z ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) k⟩ ∈
      Submodule.span E.R
        {Localization.mk E.x (1 : Submonoid.powers E.z),
          Localization.mk (E.y ^ 2) ⟨E.z, Submonoid.mem_powers E.z⟩} := by
  classical
  change MvPolynomial.IsWeightedHomogeneous E.naturalWeight p (3 * k + 1) at hp
  rw [MvPolynomial.as_sum p, Localization.mk_sum]
  exact Submodule.sum_mem _ fun a ha => monomial_twist_fraction_mem_span E k a _
    (hp (MvPolynomial.mem_support_iff.mp ha))

/-- The degree-zero localization of the first twist is generated by `x` and `y²/z`. -/
public theorem firstTwistLocalization_eq_span (E : WeightedPolynomialSituation) :
    E.firstTwistLocalization =
      Submodule.span E.R
        {Localization.mk E.x (1 : Submonoid.powers E.z),
          Localization.mk (E.y ^ 2) ⟨E.z, Submonoid.mem_powers E.z⟩} := by
  apply le_antisymm
  · change Submodule.span E.R
        {z | ∃ (k e : ℕ) (p : E.S), (e : ℤ) = (k * 3 : ℕ) + 1 ∧
          p ∈ E.naturalGrading e ∧ z = Localization.mk p
            ⟨E.z ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) k⟩} ≤ _
    apply Submodule.span_le.2
    rintro z ⟨k, e, p, he, hp, rfl⟩
    obtain rfl : e = 3 * k + 1 := by omega
    exact homogeneous_twist_fraction_mem_span E k p hp
  · apply Submodule.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · change Localization.mk E.x (1 : Submonoid.powers E.z) ∈
        Submodule.span E.R
          {z | ∃ (k e : ℕ) (p : E.S), (e : ℤ) = (k * 3 : ℕ) + 1 ∧
            p ∈ E.naturalGrading e ∧ z = Localization.mk p
              ⟨E.z ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) k⟩}
      apply Submodule.subset_span
      refine ⟨0, 1, E.x, by norm_num, ?_, ?_⟩
      · change MvPolynomial.IsWeightedHomogeneous E.naturalWeight E.x 1
        exact MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 0
      · congr 1
    · change Localization.mk (E.y ^ 2) ⟨E.z, Submonoid.mem_powers E.z⟩ ∈
        Submodule.span E.R
          {z | ∃ (k e : ℕ) (p : E.S), (e : ℤ) = (k * 3 : ℕ) + 1 ∧
            p ∈ E.naturalGrading e ∧ z = Localization.mk p
              ⟨E.z ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) k⟩}
      apply Submodule.subset_span
      refine ⟨1, 4, E.y ^ 2, by norm_num, ?_, ?_⟩
      · change MvPolynomial.IsWeightedHomogeneous E.naturalWeight (E.y ^ 2) 4
        simpa [WeightedPolynomialSituation.naturalWeight] using
          (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 1).pow 2
      · congr 1
        apply Subtype.ext
        simp

/-- The degree-zero localization of the second twist is generated by `y` and `x²`. -/
public theorem secondTwistLocalization_eq_span (E : WeightedPolynomialSituation) :
    E.secondTwistLocalization =
      Submodule.span E.R
        ({algebraMap E.S E.ordinaryLocalization E.y,
          algebraMap E.S E.ordinaryLocalization (E.x ^ 2)} :
          Set E.ordinaryLocalization) := by
  apply le_antisymm
  · let W := Submodule.span E.R
      ({algebraMap E.S E.ordinaryLocalization E.y,
        algebraMap E.S E.ordinaryLocalization (E.x ^ 2)} : Set E.ordinaryLocalization)
    have hstep (k : ℕ) (r : E.k) (d' : Fin 3 →₀ ℕ)
        (hd' : Finsupp.weight E.naturalWeight d' = 3 * k) (m : E.S)
        (hm : algebraMap E.S E.ordinaryLocalization m ∈ W) :
        Localization.mk (MvPolynomial.monomial d' r * m)
          ⟨E.z ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) k⟩ ∈ W := by
      rw [away_mk_smul_mk E k _ (MvPolynomial.isWeightedHomogeneous_monomial _ _ _ hd') m 1 _
        (mul_one _).symm]
      exact W.smul_mem _ (by rwa [Localization.mk_one_eq_algebraMap])
    have hfrac (k : ℕ) (p : E.S) (hp : p ∈ E.naturalGrading (3 * k + 2)) :
        Localization.mk p ⟨E.z ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers E.z) k⟩ ∈ W := by
      change MvPolynomial.IsWeightedHomogeneous E.naturalWeight p (3 * k + 2) at hp
      induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
      | zero =>
          rw [Localization.mk_zero]
          exact W.zero_mem
      | add p q hp hq ihp ihq =>
          rw [← Localization.add_mk_self]
          exact W.add_mem ihp ihq
      | monomial d r hd =>
          have hdeg : d 0 + 2 * d 1 + 3 * d 2 = 3 * k + 2 := by
            rw [← exponent_weight_formula E d]
            exact hd
          by_cases hy : d 1 = 0
          · let d' := d - Finsupp.single 0 2
            have hsplit : d = d' + Finsupp.single 0 2 := by
              ext i
              fin_cases i
              all_goals simp [d']
              omega
            have hdeg' : Finsupp.weight E.naturalWeight d' = 3 * k := by
              rw [exponent_weight_formula]
              simp [d']
              omega
            have hp_eq : MvPolynomial.monomial d r = MvPolynomial.monomial d' r * E.x ^ 2 := by
              rw [hsplit, MvPolynomial.monomial_add_single]
            rw [hp_eq]
            exact hstep k r d' hdeg' _ (Submodule.subset_span (by simp))
          · let d' := d - Finsupp.single 1 1
            have hsplit : d = d' + Finsupp.single 1 1 := by
              ext i
              fin_cases i
              all_goals simp [d']
              omega
            have hdeg' : Finsupp.weight E.naturalWeight d' = 3 * k := by
              rw [exponent_weight_formula]
              simp [d']
              omega
            have hp_eq : MvPolynomial.monomial d r = MvPolynomial.monomial d' r * E.y := by
              rw [hsplit, MvPolynomial.monomial_add_single]
              simp [WeightedPolynomialSituation.y]
            rw [hp_eq]
            exact hstep k r d' hdeg' _ (Submodule.subset_span (by simp))
    unfold WeightedPolynomialSituation.secondTwistLocalization
      WeightedPolynomialSituation.localizedTwist Stacks.ProjStandardOpenBaseChange.twistAway
    rw [Submodule.span_le]
    rintro x ⟨k', e', p', he', hp', rfl⟩
    obtain rfl : e' = 3 * k' + 2 := by omega
    exact hfrac k' p' hp'
  · rw [Submodule.span_le]
    rintro a (ha | ha)
    · subst a
      change algebraMap E.S E.ordinaryLocalization E.y ∈ E.secondTwistLocalization
      unfold WeightedPolynomialSituation.secondTwistLocalization
        WeightedPolynomialSituation.localizedTwist Stacks.ProjStandardOpenBaseChange.twistAway
      apply Submodule.subset_span
      refine ⟨0, 2, E.y, by norm_num, ?_, ?_⟩
      · change E.y ∈ E.naturalGrading 2
        simpa [WeightedPolynomialSituation.naturalWeight] using
          (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 1)
      · change algebraMap E.S (Localization (Submonoid.powers E.z)) E.y =
          Localization.mk E.y 1
        exact (Localization.mk_one_eq_algebraMap
          (M := Submonoid.powers E.z) E.y).symm
    · subst a
      change algebraMap E.S E.ordinaryLocalization (E.x ^ 2) ∈ E.secondTwistLocalization
      unfold WeightedPolynomialSituation.secondTwistLocalization
        WeightedPolynomialSituation.localizedTwist Stacks.ProjStandardOpenBaseChange.twistAway
      apply Submodule.subset_span
      refine ⟨0, 2, E.x ^ 2, by norm_num, ?_, ?_⟩
      · change MvPolynomial.IsWeightedHomogeneous E.naturalWeight (E.x ^ 2) 2
        simpa [WeightedPolynomialSituation.naturalWeight] using
          (MvPolynomial.isWeightedHomogeneous_X E.k E.naturalWeight 0).pow 2
      · change algebraMap E.S (Localization (Submonoid.powers E.z)) (E.x ^ 2) =
          Localization.mk (E.x ^ 2) 1
        exact (Localization.mk_one_eq_algebraMap
          (M := Submonoid.powers E.z) (E.x ^ 2)).symm

end Stacks.WeightedPolynomialSituation

end
