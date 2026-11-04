module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveDualTraceConjugation

/-!
# The dual of a pure lisse sheaf on an affine curve: the Frobenius roots as multisets

The multiset form of `Stacks.EtaleCohomology.isRoot_zpow_mul_conj_of_curve`. On a smooth
geometrically connected affine curve `U` over `k`, `#k = q`, for `σ` `ι'`-pure of weight `β` with
`H²_c` vanishing for `ℱ_σ` and `ℱ_{σ^∨}`, the nonzero Frobenius roots (along `ι'`, with
multiplicity) on `H¹_c(U_k̄, ℱ_{σ^∨} ⊗ ℚ_ℓ)` are the images `q ^ (-β) · z̄` of the nonzero
Frobenius roots `z` on `H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ)`.

## Main results

* `Stacks.EtaleCohomology.filter_ne_zero_eq_of_forall_sum_map_pow_eq`: power sums determine the
  nonzero part of a multiset.
* `Stacks.EtaleCohomology.roots_filter_ne_zero_contragredient_eq_map_conj_of_curve`: the nonzero
  Frobenius roots on `H¹_c` of `ℱ_{σ^∨}` are the images `q ^ (-β) · z̄` of those of `ℱ_σ`.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
* K. Kedlaya, *Fourier transforms and p-adic Weil II*, proof of Theorem 6.4
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

/-- **Power sums determine the nonzero part of a multiset**: if two finite multisets of complex
numbers have the same power sums `∑ wᴺ` for all `N ≥ 1`, their nonzero elements agree with
multiplicity. -/
public theorem filter_ne_zero_eq_of_forall_sum_map_pow_eq {A B : Multiset ℂ}
    (h : ∀ N : ℕ, 0 < N → (B.map (· ^ N)).sum = (A.map (· ^ N)).sum) :
    B.filter (· ≠ 0) = A.filter (· ≠ 0) := by
  classical
  ext w
  rw [Multiset.count_filter, Multiset.count_filter]
  split_ifs with hw0
  · by_cases hmem : w ∈ A + B
    · have hc := Stacks.PowerProduct.coeff_eq_of_sum_pow_eq (A + B).toFinset
        (fun z ↦ (B.count z : ℂ)) (fun z ↦ (A.count z : ℂ))
        (fun N hN ↦ by
          rw [← sum_map_pow_eq_sum_count (Multiset.le_add_left B A),
            ← sum_map_pow_eq_sum_count (Multiset.le_add_right A B)]
          exact h N hN)
        w (Multiset.mem_toFinset.2 hmem) hw0
      exact_mod_cast hc
    · rw [Multiset.mem_add, not_or] at hmem
      rw [Multiset.count_eq_zero.2 hmem.1, Multiset.count_eq_zero.2 hmem.2]
  · rfl

section Curve

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1] [IsAffine U.1]
  (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar]
  [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
  (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (hℓp : ℓ ≠ p)
  (x : GeometricPoint U.1)
  (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
  (hσ : Continuous (restrictScalarsRep b σ)) (ι' : E →+* ℂ) (β : ℤ)


include hℓp in
/-- **The nonzero Frobenius roots of the dual of a pure lisse sheaf on an affine curve, with
multiplicity**: if `σ` is `ι'`-pure of weight `β` and `H²_c` vanishes for `ℱ_σ` and `ℱ_{σ^∨}`, the
nonzero roots (along `ι'`) of the characteristic polynomial of the `E`-linear Frobenius on
`H¹_c(U_k̄, ℱ_{σ^∨} ⊗ ℚ_ℓ)` are, as a multiset, the images `q ^ (-β) · z̄` of the nonzero roots `z`
of the one on `H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ)`. -/
public theorem roots_filter_ne_zero_contragredient_eq_map_conj_of_curve
    (hpure : ∀ (y : closedPoints U.1) (z : ℂ),
      ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2))
    (h₂ : Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
      (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 2))
    (h₂' : Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
      (restrictScalarsRepCoefficientSheaf B U x b (contragredient σ)
        (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 2))
    [hV : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
      f j kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1)]
    [hV' : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
      f j kbar (restrictScalarsRepCoefficientSheaf B U x b (contragredient σ)
        (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1)] :
    letI := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
    haveI :=
      (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule_isScalarTower
        f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
    haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
        kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) :=
      Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    letI := (restrictScalarsRepCoefficientSheaf B U x b (contragredient σ)
      (continuous_restrictScalarsRep_contragredient b hσ)).rationalCohomologyModule f j kbar 1 E
    haveI := (restrictScalarsRepCoefficientSheaf B U x b (contragredient σ)
      (continuous_restrictScalarsRep_contragredient b hσ)).rationalCohomologyModule_isScalarTower
      f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
    haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
        kbar (restrictScalarsRepCoefficientSheaf B U x b (contragredient σ)
          (continuous_restrictScalarsRep_contragredient b hσ)).toLAdicSheaf 1) :=
      Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    ((LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B U x b (contragredient σ)
        (continuous_restrictScalarsRep_contragredient b
          hσ)).rationalGeometricCompactlySupportedFrobenius
          f j kbar 1 E p n hcard)).map ι').roots.filter (· ≠ 0) =
      (((LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B U x b σ
        hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard)).map
          ι').roots.filter (· ≠ 0)).map fun z => (((p ^ n : ℕ) : ℂ) ^ β)⁻¹ * starRingEnd ℂ z := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : Nonempty U.1 := ConnectedSpace.toNonempty
  have : ∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) := fun n T ↦
    AlgebraicGeometry.hasWeakSheafify_smallEtale_of_scheme B _ T
  have hσ' := continuous_restrictScalarsRep_contragredient b hσ
  set q : ℕ := p ^ n
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  set c : ℂ := ((q : ℂ) ^ β)⁻¹ with hc_def
  have hc0 : c ≠ 0 := inv_ne_zero (zpow_ne_zero _ hq0)
  set S : (EtaleFundamentalGroup U.1 x →* GL (Fin m) E) → ℕ → E := fun τ N ↦
    ∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : E) *
      (((τ (geometricFrobeniusFamily f x y)).val) ^ (N / residueDegree f y.1)).trace with hS_def
  have hSconj : ∀ N : ℕ, ι' (S (contragredient σ) N) = c ^ N * starRingEnd ℂ (ι' (S σ N)) := by
    intro N
    refine map_finsum_mem_eq_mul_conj ι' (pow_ne_zero _ hc0) _ _
      {y : closedPoints U.1 | residueDegree f y.1 ∣ N} fun y hy ↦ ?_
    set g := σ (geometricFrobeniusFamily f x y)
    set dg := residueDegree f y.1 with hdg
    have hval : ((contragredient σ (geometricFrobeniusFamily f x y) : GL (Fin m) E) :
        Matrix (Fin m) (Fin m) E) = ((g : Matrix (Fin m) (Fin m) E)⁻¹)ᵀ := by
      rw [contragredient_val, Matrix.coe_units_inv]
    set Q : ℝ := ((q : ℕ) : ℝ) ^ ((((dg : ℤ) * β : ℤ)) : ℝ) with hQ_def
    have hQ : ∀ z : ℂ, ((g : Matrix (Fin m) (Fin m) E).charpoly.map ι').IsRoot z →
        ‖z‖ ^ 2 = Q := by
      intro z hz
      rw [hpure y z hz, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), hQ_def]
      congr 1
      push_cast
      ring
    have hQc : ((Q : ℂ)) ^ (N / dg) = ((q : ℂ) ^ β) ^ N := by
      obtain ⟨t, ht⟩ := (hy : dg ∣ N)
      rw [hQ_def, Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_natCast, ht]
      rcases Nat.eq_zero_or_pos dg with h0 | hpos
      · rw [← hdg, h0]
        simp
      · rw [Nat.mul_div_cancel_left t hpos, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul,
          ← _root_.zpow_mul]
        congr 1
        push_cast
        ring
    change ι' ((dg : E) * (((contragredient σ (geometricFrobeniusFamily f x y) : GL (Fin m) E) :
        Matrix (Fin m) (Fin m) E) ^ (N / dg)).trace) =
      c ^ N * starRingEnd ℂ (ι' ((dg : E) * ((g : Matrix (Fin m) (Fin m) E) ^ (N / dg)).trace))
    rw [hval, map_mul, map_mul, map_natCast, map_mul, map_natCast,
      map_trace_inv_transpose_pow_of_norm_sq ι' g.isUnit hQ, hQc, hc_def, inv_pow]
    ring
  have hsum : ∀ (τ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
      (hτ : Continuous (restrictScalarsRep b τ))
      [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
        f j kbar (restrictScalarsRepCoefficientSheaf B U x b τ hτ).toLAdicSheaf 1)],
      Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B U x b τ hτ).toLAdicSheaf 2) →
      ∀ N : ℕ, 0 < N →
        letI := (restrictScalarsRepCoefficientSheaf B U x b τ hτ).rationalCohomologyModule f j
          kbar 1 E
        haveI := (restrictScalarsRepCoefficientSheaf B U x b τ
          hτ).rationalCohomologyModule_isScalarTower f j kbar 1 E
            (algebraMap_conjIntegralSubring_algebraMap _ _)
        haveI : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ
            f j kbar (restrictScalarsRepCoefficientSheaf B U x b τ hτ).toLAdicSheaf 1) :=
          Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
        (((LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B U x b τ
          hτ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard)).map
            ι').roots.map (· ^ N)).sum = -ι' (S τ N) := by
    intro τ hτ _ h2 N hN
    let := (restrictScalarsRepCoefficientSheaf B U x b τ hτ).rationalCohomologyModule f j kbar 1 E
    have := (restrictScalarsRepCoefficientSheaf B U x b τ hτ).rationalCohomologyModule_isScalarTower
      f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
    have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
        kbar (restrictScalarsRepCoefficientSheaf B U x b τ hτ).toLAdicSheaf 1) :=
      Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    rw [← map_trace_pow_eq_sum_roots_map_pow, ← map_neg]
    congr 1
    open LAdicSheaf in
    have : Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B U x b τ hτ).toLAdicSheaf 0) :=
      subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_smoothOfRelativeDimension
        B U ℓ f j kbar _ (LAdicSheaf.representationSheaf_isLisse B U x _ hτ)
    have h := curveLinearTraceFormulaInput B U ℓ k f j kbar p n hcard hℓp x E b τ hτ N hN
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
      trace_pow_eq_zero_of_subsingleton, mul_zero, zero_add, add_zero, pow_one,
      neg_one_mul] at h
    rw [hS_def]
    beta_reduce
    linear_combination h
  have hmain : ∀ A B : Multiset ℂ, (∀ N : ℕ, 0 < N → (A.map (· ^ N)).sum = -ι' (S σ N)) →
      (∀ N : ℕ, 0 < N → (B.map (· ^ N)).sum = -ι' (S (contragredient σ) N)) →
      B.filter (· ≠ 0) = (A.filter (· ≠ 0)).map fun z ↦ c * starRingEnd ℂ z := by
    intro A B hA hB
    have hsq : ∀ N : ℕ, 0 < N → (B.map (· ^ N)).sum =
        ((A.map fun z ↦ c * starRingEnd ℂ z).map (· ^ N)).sum := by
      intro N hN
      have hfun : (fun z : ℂ ↦ (c * starRingEnd ℂ z) ^ N) =
          fun z ↦ c ^ N * starRingEnd ℂ (z ^ N) := by
        funext z
        rw [mul_pow, map_pow]
      rw [hB N hN, hSconj N, Multiset.map_map, Function.comp_def, hfun,
        Multiset.sum_map_mul_left,
        show (fun z : ℂ ↦ starRingEnd ℂ (z ^ N)) = (starRingEnd ℂ) ∘ (· ^ N) from rfl,
        ← Multiset.map_map, ← map_multiset_sum, hA N hN, map_neg, mul_neg]
    rw [filter_ne_zero_eq_of_forall_sum_map_pow_eq hsq, Multiset.filter_map]
    congr 1
    refine Multiset.filter_congr fun z _ ↦ ?_
    simp only [Function.comp_apply, ne_eq, mul_eq_zero, hc0, false_or, map_eq_zero]
  exact hmain _ _ (hsum σ hσ h₂) (hsum _ hσ' h₂')

end Curve

end Stacks.EtaleCohomology

end
