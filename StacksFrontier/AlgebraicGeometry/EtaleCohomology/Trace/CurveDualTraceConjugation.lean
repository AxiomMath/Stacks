module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLinearTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SmoothAffineCurveCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ContragredientTraceConj
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRootConjugation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsRepContinuity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitDescent

/-!
# The dual of a pure lisse sheaf on an affine curve: Frobenius roots by complex conjugation

Let `U` be a smooth geometrically connected affine curve over `k`, `#k = q`, and
`σ : π₁(U, x̄) → GL_m(E)` with `Res_b σ` continuous, `ι'`-pure of weight `β` at the closed points.
If `H²_c` vanishes for `ℱ_σ` and for the sheaf of the contragredient `σ^∨` (as `H⁰_c` always does,
`U` being affine), the `E`-linear trace formula (Tag 03V2) and
`ι' Tr(σ^∨(F_y)ʳ) = q_y^{-β r} conj(ι' Tr(σ(F_y)ʳ))`
(`Stacks.EtaleCohomology.map_trace_inv_transpose_pow_of_norm_sq`) give
`∑ wᴺ = ∑ (q^{-β} z̄)ᴺ` for the Frobenius roots `w` on `H¹_c(U_k̄, ℱ_{σ^∨})` and `z` on
`H¹_c(U_k̄, ℱ_σ)` along `ι'`; so for every nonzero root `w`, `q ^ β · w̄` is a root `z`
(`Stacks.EtaleCohomology.isRoot_zpow_mul_conj_of_curve`). This is the conjugation step of the
duality argument in Laumon's purity of the Fourier family
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Kedlaya, *Fourier transforms and p-adic
Weil II*, proof of Theorem 6.4).

## Main results

* `Stacks.EtaleCohomology.map_finsum_mem_eq_mul_conj`.
* `Stacks.EtaleCohomology.isRoot_zpow_mul_conj_of_curve`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

/-- **Finite sums along `ι`, twisted by conjugation**: if `ι (g y) = c · conj(ι (h y))` on `s`
with `c ≠ 0`, the same holds for `∑ᶠ y ∈ s` (both sides vanish when the support is infinite). -/
public theorem map_finsum_mem_eq_mul_conj {E Y : Type*} [Field E] (ι : E →+* ℂ) {c : ℂ}
    (hc : c ≠ 0) (g h : Y → E) (s : Set Y)
    (hgh : ∀ y ∈ s, ι (g y) = c * starRingEnd ℂ (ι (h y))) :
    ι (∑ᶠ y ∈ s, g y) = c * starRingEnd ℂ (ι (∑ᶠ y ∈ s, h y)) := by
  classical
  have hsupp : s ∩ Function.support g = s ∩ Function.support h := by
    ext y
    simp only [Set.mem_inter_iff, Function.mem_support, and_congr_right_iff]
    intro hy
    rw [Ne, Ne, ← (map_eq_zero_iff ι ι.injective), hgh y hy, mul_eq_zero, map_eq_zero,
      map_eq_zero_iff ι ι.injective, or_iff_right hc]
  by_cases hfin : (s ∩ Function.support h).Finite
  · rw [← finsum_mem_inter_support g s, ← finsum_mem_inter_support h s, hsupp,
      finsum_mem_eq_finite_toFinset_sum g hfin, finsum_mem_eq_finite_toFinset_sum h hfin,
      map_sum, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => hgh y ?_
    exact ((Set.Finite.mem_toFinset _).1 hy).1
  · rw [finsum_mem_eq_zero_of_infinite (by rwa [hsupp]), finsum_mem_eq_zero_of_infinite hfin,
      map_zero, map_zero, mul_zero]

/-- The trace of an endomorphism of a subsingleton module vanishes. -/
theorem trace_pow_eq_zero_of_subsingleton {E M : Type*} [Field E] [AddCommGroup M] [Module E M]
    [Subsingleton M] (F : Module.End E M) (N : ℕ) : LinearMap.trace E M (F ^ N) = 0 := by
  rw [Subsingleton.elim (F ^ N) 0, map_zero]

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
/-- **The Frobenius roots of the dual of a pure lisse sheaf on an affine curve, by complex
conjugation**: if `σ` is `ι'`-pure of weight `β` and `H²_c` vanishes for `ℱ_σ` and `ℱ_{σ^∨}`,
then for every nonzero root `w` (along `ι'`) of the characteristic polynomial of the `E`-linear
Frobenius on `H¹_c(U_k̄, ℱ_{σ^∨} ⊗ ℚ_ℓ)`, `q ^ β · w̄` is a root of the one on
`H¹_c(U_k̄, ℱ_σ ⊗ ℚ_ℓ)`. -/
public theorem isRoot_zpow_mul_conj_of_curve
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
    haveI := (restrictScalarsRepCoefficientSheaf B U x b σ
      hσ).rationalCohomologyModule_isScalarTower f j kbar 1 E
      (algebraMap_conjIntegralSubring_algebraMap _ _)
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
    ∀ w : ℂ, w ≠ 0 →
      ((LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B U x b (contragredient σ)
        (continuous_restrictScalarsRep_contragredient b
          hσ)).rationalGeometricCompactlySupportedFrobenius
          f j kbar 1 E p n hcard)).map ι').IsRoot w →
      ((LinearMap.charpoly ((restrictScalarsRepCoefficientSheaf B U x b σ
        hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard)).map ι').IsRoot
          (((p ^ n : ℕ) : ℂ) ^ β * starRingEnd ℂ w) := by
  intros w hw0 hw
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : Nonempty U.1 := ConnectedSpace.toNonempty
  have : ∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) := fun n T =>
    AlgebraicGeometry.hasWeakSheafify_smallEtale_of_scheme B _ T
  have hσ' := continuous_restrictScalarsRep_contragredient b hσ
  set q : ℕ := p ^ n with hq_def
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  set c : ℂ := ((q : ℂ) ^ β)⁻¹ with hc_def
  have hc0 : c ≠ 0 := inv_ne_zero (zpow_ne_zero _ hq0)
  have hcconj : starRingEnd ℂ c = c := by
    rw [hc_def, map_inv₀, map_zpow₀, map_natCast]
  -- the point sums of `σ` and `σ^∨`
  set S : (EtaleFundamentalGroup U.1 x →* GL (Fin m) E) → ℕ → E := fun τ N =>
    ∑ᶠ (y : closedPoints U.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : E) *
      (((τ (geometricFrobeniusFamily f x y)).val) ^ (N / residueDegree f y.1)).trace with hS_def
  have hSconj : ∀ N : ℕ, ι' (S (contragredient σ) N) = c ^ N * starRingEnd ℂ (ι' (S σ N)) := by
    intro N
    refine map_finsum_mem_eq_mul_conj ι' (pow_ne_zero _ hc0) _ _
      {y : closedPoints U.1 | residueDegree f y.1 ∣ N} fun y hy => ?_
    set g := σ (geometricFrobeniusFamily f x y) with hg
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
    show ι' ((dg : E) * (((contragredient σ (geometricFrobeniusFamily f x y) : GL (Fin m) E) :
        Matrix (Fin m) (Fin m) E) ^ (N / dg)).trace) =
      c ^ N * starRingEnd ℂ (ι' ((dg : E) * ((g : Matrix (Fin m) (Fin m) E) ^ (N / dg)).trace))
    rw [hval, map_mul, map_mul, map_natCast, map_mul, map_natCast,
      map_trace_inv_transpose_pow_of_norm_sq ι' g.isUnit hQ, hQc, hc_def, inv_pow]
    ring
  -- the trace formula with `H⁰_c = H²_c = 0`
  have hkey : ∀ (τ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
      (hτ : Continuous (restrictScalarsRep b τ)),
      Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B U x b τ hτ).toLAdicSheaf 2) →
      ∀ N : ℕ, 0 < N →
        (let := (restrictScalarsRepCoefficientSheaf B U x b τ hτ).rationalCohomologyModule f j
          kbar 1 E
        LinearMap.trace E _ (((restrictScalarsRepCoefficientSheaf B U x b τ
          hτ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard) ^ N)) =
          -S τ N := by
    intro τ hτ h2 N hN
    have : Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (restrictScalarsRepCoefficientSheaf B U x b τ hτ).toLAdicSheaf 0) :=
      open LAdicSheaf in
      subsingleton_rationalGeometricCompactlySupportedCohomology_zero_of_smoothOfRelativeDimension
        B U ℓ f j kbar _ (LAdicSheaf.representationSheaf_isLisse B U x _ hτ)
    have h := curveLinearTraceFormulaInput B U ℓ k f j kbar p n hcard hℓp x E b τ hτ N hN
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
      trace_pow_eq_zero_of_subsingleton, mul_zero, zero_add, add_zero, pow_one, neg_one_mul] at h
    rw [hS_def]
    beta_reduce
    linear_combination h
  let := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule f j kbar 1 E
  have := (restrictScalarsRepCoefficientSheaf B U x b σ hσ).rationalCohomologyModule_isScalarTower
    f j kbar 1 E (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B U x b σ hσ).toLAdicSheaf 1) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  let := (restrictScalarsRepCoefficientSheaf B U x b (contragredient σ)
    hσ').rationalCohomologyModule f j kbar 1 E
  have := (restrictScalarsRepCoefficientSheaf B U x b (contragredient σ)
    hσ').rationalCohomologyModule_isScalarTower f j kbar 1 E
      (algebraMap_conjIntegralSubring_algebraMap _ _)
  have : FiniteDimensional E (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j
      kbar (restrictScalarsRepCoefficientSheaf B U x b (contragredient σ) hσ').toLAdicSheaf 1) :=
    Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  set F₁ := (restrictScalarsRepCoefficientSheaf B U x b σ
    hσ).rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard with hF₁
  set F₂ := (restrictScalarsRepCoefficientSheaf B U x b (contragredient σ)
    hσ').rationalGeometricCompactlySupportedFrobenius f j kbar 1 E p n hcard with hF₂
  have hsum₁ : ∀ N : ℕ, 0 < N →
      (((LinearMap.charpoly F₁).map ι').roots.map (· ^ N)).sum = -ι' (S σ N) := fun N hN => by
    rw [← map_trace_pow_eq_sum_roots_map_pow ι' F₁ N, hkey σ hσ h₂ N hN, map_neg]
  have hsum₂ : ∀ N : ℕ, 0 < N →
      (((LinearMap.charpoly F₂).map ι').roots.map (· ^ N)).sum =
        -ι' (S (contragredient σ) N) := fun N hN => by
    rw [← map_trace_pow_eq_sum_roots_map_pow ι' F₂ N, hkey (contragredient σ) hσ' h₂' N hN,
      map_neg]
  have hmain : ∀ N : ℕ, 0 < N →
      (((LinearMap.charpoly F₂).map ι').roots.map (· ^ N)).sum =
        (((LinearMap.charpoly F₁).map ι').roots.map fun z => (c * starRingEnd ℂ z) ^ N).sum := by
    intro N hN
    have hfun : (fun z : ℂ => (c * starRingEnd ℂ z) ^ N) =
        fun z => c ^ N * starRingEnd ℂ (z ^ N) := by
      funext z
      rw [mul_pow, map_pow]
    rw [hsum₂ N hN, hSconj N, hfun, Multiset.sum_map_mul_left,
      show (fun z : ℂ => starRingEnd ℂ (z ^ N)) = (starRingEnd ℂ) ∘ (· ^ N) from rfl,
      ← Multiset.map_map, ← map_multiset_sum, hsum₁ N hN, map_neg, mul_neg]
  have hwmem : w ∈ ((LinearMap.charpoly F₂).map ι').roots :=
    (Polynomial.mem_roots ((LinearMap.charpoly_monic F₂).map ι').ne_zero).2 hw
  obtain ⟨z, hz, rfl⟩ := mem_of_forall_sum_map_pow_eq_conj hmain hwmem hw0
  rw [map_mul, Complex.conj_conj, hcconj, ← mul_assoc, hc_def, mul_inv_cancel₀ (zpow_ne_zero _ hq0),
    one_mul]
  exact (Polynomial.mem_roots ((LinearMap.charpoly_monic F₁).map ι').ne_zero).1 hz

end Curve

end Stacks.EtaleCohomology

end
