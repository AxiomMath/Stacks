module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionTraceCriterion
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.PerfectTowerSystemPow
public import StacksFrontier.RingTheory.PowerSeries.LogDerivativeMap

/-!
# The rational image of an ℓ-adic characteristic series of `RΓ_c(X_k̄, F)`

Let `F` be an ℓ-adic sheaf with flat levels on a separated scheme `X` of finite type over a finite
field `k`, whose complexes `Kₙ = RΓ_c(X_k̄, Fₙ)` are perfect.  A power series `c ∈ ℤ_ℓ⟦T⟧` with
constant coefficient `1` whose logarithmic derivative has, modulo `ℓⁿ⁺¹`, the coefficients
`Tr((π_X^*) ^ m | Kₙ)` — as the ℓ-adic limit of the inverse characteristic series
`det(1 - π_X^* T | Kₙ)⁻¹` has — maps in `ℚ_ℓ⟦T⟧` to

`∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)) ^ ((-1) ^ (i + 1))`.

The reason is that `ℤ_ℓ` has no `ℓ`-torsion: the coefficients of the logarithmic derivative of
`c` are the ℓ-adic integers `t_∞(πᵐ)` with these reductions, which by Tag 03V4 (3) for the tower
`(Kₙ, πₙ ^ m)` are the alternating sums `∑ᵢ (-1)ⁱ Tr((π_X^*) ^ m | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ))`, the
coefficients of the logarithmic derivative of the alternating product; and over `ℚ_ℓ` a series
with constant coefficient `1` is determined by its logarithmic derivative.

## Main results

* `coeff_logDerivative_gradedCharSeries`: the logarithmic derivative of
  `∏ᵢ det(1 - φᵢ T | Vᵢ) ^ ((-1) ^ (i + 1))`.
* `LAdicSheaf.alternating_trace_pow_rationalGeometricCompactlySupportedFrobenius`:
  `∑ᵢ (-1)ⁱ Tr((π_X^*) ^ m | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)) = t_∞(πᵐ)`.
* `LAdicSheaf.map_padic_eq_gradedCharSeries_of_logDerivative`: the comparison above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem PowerSeries

universe u w

namespace Stacks.EtaleCohomology

/-! ### The logarithmic derivative of an alternating product -/

section Graded

variable {Λ : Type*} [CommRing Λ] [Nontrivial Λ] (V : ℤ → Type w) [∀ i, AddCommGroup (V i)]
  [∀ i, Module Λ (V i)] [∀ i, Module.Finite Λ (V i)] [∀ i, Module.Free Λ (V i)]
  (φ : ∀ i, V i →ₗ[Λ] V i)

/-- The alternating product `∏ᵢ det(1 - φᵢ T | Vᵢ) ^ ((-1) ^ (i + 1))` has constant
coefficient `1`, provided the `Vᵢ` vanish outside a finite set of degrees. -/
public theorem constantCoeff_gradedCharSeries (S : Finset ℤ) (hS : ∀ i ∉ S, Subsingleton (V i)) :
    constantCoeff (gradedCharSeries V φ) = 1 := by
  rw [gradedCharSeries_eq_alternatingCharSeries V φ S hS]
  exact constantCoeff_alternatingCharSeries _ _ _

/-- The coefficient of `T ^ m`, `m ≥ 1`, of the logarithmic derivative of the alternating product
`∏ᵢ det(1 - φᵢ T | Vᵢ) ^ ((-1) ^ (i + 1))` is `∑ᵢ (-1)ⁱ Tr(φᵢ ^ m)`. -/
public theorem coeff_logDerivative_gradedCharSeries (S : Finset ℤ)
    (hS : ∀ i ∉ S, Subsingleton (V i)) {m : ℕ} (hm : m ≠ 0) :
    coeff m (logDerivative (gradedCharSeries V φ)) =
      ∑ᶠ i : ℤ, (if Even i then (1 : Λ) else -1) * LinearMap.trace Λ (V i) (φ i ^ m) := by
  rw [gradedCharSeries_eq_alternatingCharSeries V φ S hS,
    coeff_logDerivative_alternatingCharSeries _ _ _ hm, Finset.sum_coe_sort S
      (fun a => (if Even a then (1 : Λ) else -1) *
        ((LinearMap.toMatrix (Module.finBasis Λ (V a)) (Module.finBasis Λ (V a)) (φ a)) ^
          m).trace)]
  rw [finsum_eq_sum_of_support_subset _ (s := S) fun i hi => ?_]
  · exact Finset.sum_congr rfl fun i _ => by rw [trace_pow_eq_matrix V φ i m]
  · by_contra h
    have := hS i h
    exact hi (by simp only [Subsingleton.elim (φ i ^ m) 0, map_zero, mul_zero])

end Graded

/-! ### The sheaf -/

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [AlgebraicGeometry.IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **`∑ᵢ (-1)ⁱ Tr((π_X^*) ^ m | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)) = t_∞(πᵐ)`**, the ℓ-adic trace of the tower
`(Kₙ = RΓ_c(X_k̄, Fₙ), (π_X^*) ^ m)`, for an ℓ-adic sheaf with flat levels whose `Kₙ` are
perfect. -/
public theorem LAdicSheaf.alternating_trace_pow_rationalGeometricCompactlySupportedFrobenius
    (F : LAdicSheaf B X ℓ) (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n)))) (m : ℕ) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom ^ m) =
      (padicTrace ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).pow m) :
        ℚ_[ℓ]) :=
  alternating_trace_pow_rational_limit_of_iso _ _
    (fun i => LAdicSheaf.geometricLevelCohomologySystemIso B X ℓ f j kbar p q hcard F hF hP i)
    (fun i => LAdicSheaf.geometricLevelCohomologySystemIso_frobenius B X ℓ f j kbar p q hcard F hF
      hP i) m

/-- **The rational image of an ℓ-adic characteristic series of `RΓ_c(X_k̄, F)`.** Let `F` be an
ℓ-adic sheaf with flat levels on a separated scheme of finite type over a finite field whose
complexes `Kₙ = RΓ_c(X_k̄, Fₙ)` are perfect, and let `c ∈ ℤ_ℓ⟦T⟧` have constant coefficient `1`
and logarithmic derivative with coefficients reducing modulo `ℓⁿ⁺¹` to `Tr((π_X^*) ^ m | Kₙ)`.
Then the image of `c` in `ℚ_ℓ⟦T⟧` is
`∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)) ^ ((-1) ^ (i + 1))`. -/
public theorem LAdicSheaf.map_padic_eq_gradedCharSeries_of_logDerivative
    (F : LAdicSheaf B X ℓ) (hF : ∀ n, PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ F n))
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n))))
    {c : ℤ_[ℓ]⟦X⟧} (hc : constantCoeff c = 1)
    (htr : ∀ m : ℕ, m ≠ 0 → ∀ n : ℕ, PadicInt.toZModPow (n + 1) (coeff m (logDerivative c)) =
      traceAtLevel ((LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard F hF hP).pow m) n) :
    PowerSeries.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) c =
      gradedCharSeries
        (fun i => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
        (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
          hcard F i).hom) := by
  have := fun i => LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_flat B X ℓ
    f j kbar p q hcard F hF hP i
  have hfin := LAdicSheaf.finite_nontrivial_rationalGeometricCompactlySupportedCohomology_of_flat
    B X ℓ f j kbar p q hcard F hF hP
  have hS : ∀ i ∉ hfin.toFinset, Subsingleton
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) :=
    fun i hi => not_nontrivial_iff_subsingleton.1 fun h => hi (hfin.mem_toFinset.2 h)
  have hc' : constantCoeff (PowerSeries.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) c) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hc,
      map_one]
  refine eq_of_logDerivative_eq hc' (constantCoeff_gradedCharSeries _ _ _ hS) (ext fun m => ?_)
  rcases eq_or_ne m 0 with rfl | hm
  · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_logDerivative, constantCoeff_logDerivative]
  rw [coeff_logDerivative_gradedCharSeries _ _ _ hS hm,
    LAdicSheaf.alternating_trace_pow_rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p
      q hcard F hF hP m, ← map_logDerivative _ hc, coeff_map,
    (exists_unique_padicTrace _).unique (htr m hm) (toZModPow_padicTrace _)]
  rfl

end Stacks.EtaleCohomology

end
