module

public import StacksFrontier.RingTheory.Polynomial.BivariateWeightedDegree
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The derivation along a plane curve

For `Ψ ∈ R[X][Y]`, the derivation `δ_Ψ = Ψ_Y ∂_X - Ψ_X ∂_Y` of `R[X][Y]` kills `Ψ`, so it is a
derivation along the curve `Ψ = 0`. On a power-series branch `s ↦ (a + s, β(s))` of the curve it
becomes `u · d/ds`, where `u = Ψ_Y(a + s, β(s))`: this is the chain rule
`d/ds g(a + s, β(s)) = g_X(a + s, β(s)) + g_Y(a + s, β(s)) β'(s)` together with
`Ψ(a + s, β(s)) = 0`.

## Main definitions

* `Polynomial.Bivariate.derivX`: the partial derivative in the inner variable `X`.
* `Polynomial.Bivariate.curveDeriv`: the derivation `Ψ_Y ∂_X - Ψ_X ∂_Y`.
* `Polynomial.Bivariate.branchEval`: evaluation along the power-series curve `s ↦ (a + s, β)`.

## Main results

* `Polynomial.Bivariate.WeightedDegreeLE.iterate_curveDeriv`: `δ_Ψ` raises weighted degree by at
  most that of `Ψ`.
* `Polynomial.Bivariate.derivative_branchEval`: the chain rule along a branch.
* `Polynomial.Bivariate.branchEval_iterate_curveDeriv`: on a branch, `δ_Ψ^j` becomes
  `(u · d/ds)^j`.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

section CommRing

variable {R : Type*} [CommRing R]

/-- The partial derivative of a bivariate polynomial with respect to the inner variable `X`. -/
noncomputable def derivX (g : R[X][Y]) : R[X][Y] :=
  ∑ j ∈ g.support, monomial j (derivative (g.coeff j))

/-- The `j`-th coefficient of `∂_X g` is the derivative of the `j`-th coefficient of `g`. -/
@[simp]
theorem coeff_derivX (g : R[X][Y]) (j : ℕ) : (derivX g).coeff j = derivative (g.coeff j) := by
  rw [derivX, finsetSum_coeff]
  simp only [coeff_monomial]
  by_cases hj : j ∈ g.support
  · rw [Finset.sum_eq_single j (fun b _ hb => ite_eq_right hb) (fun h => absurd hj h),
      ite_eq_left rfl]
  · rw [Finset.sum_eq_zero fun b hb => ite_eq_right fun h => hj (by rw [← h]; exact hb)]
    rw [notMem_support_iff.mp hj, derivative_zero]

/-- `∂_X` is additive. -/
theorem derivX_add (g h : R[X][Y]) : derivX (g + h) = derivX g + derivX h := by
  ext1 j; simp

/-- `∂_X` commutes with subtraction. -/
theorem derivX_sub (g h : R[X][Y]) : derivX (g - h) = derivX g - derivX h := by
  ext1 j; simp

/-- `∂_X` commutes with scalar multiplication by `R`. -/
theorem derivX_smul (c : R) (g : R[X][Y]) : derivX (c • g) = c • derivX g := by
  ext1 j; simp

/-- The Leibniz rule for `∂_X`. -/
theorem derivX_mul (g h : R[X][Y]) : derivX (g * h) = derivX g * h + g * derivX h := by
  ext1 j
  simp only [coeff_derivX, coeff_mul, coeff_add, derivative_sum, derivative_mul,
    Finset.sum_add_distrib]

/-- `∂_X` of a constant `C a` in `Y` is `C a'`. -/
@[simp]
theorem derivX_C (a : R[X]) : derivX (C a : R[X][Y]) = C (derivative a) := by
  ext1 j; simp [coeff_C]; split_ifs <;> simp

/-- `∂_X` of the outer variable `Y` vanishes. -/
@[simp]
theorem derivX_X : derivX (X : R[X][Y]) = 0 := by
  ext1 j; simp [coeff_X]; split_ifs <;> simp

/-- `∂_X` as an `R`-linear map. -/
noncomputable def derivXLinear : R[X][Y] →ₗ[R] R[X][Y] where
  toFun := derivX
  map_add' := derivX_add
  map_smul' := derivX_smul

/-- The derivation `δ_Ψ = Ψ_Y ∂_X - Ψ_X ∂_Y` along the curve `Ψ = 0`, as an `R`-linear map. -/
noncomputable def curveDeriv (Ψ : R[X][Y]) : R[X][Y] →ₗ[R] R[X][Y] :=
  LinearMap.mulLeft R (derivative Ψ) ∘ₗ derivXLinear -
    LinearMap.mulLeft R (derivX Ψ) ∘ₗ (derivative : R[X][Y] →ₗ[R[X]] R[X][Y]).restrictScalars R

/-- `δ_Ψ g = Ψ_Y · ∂_X g - Ψ_X · ∂_Y g`. -/
theorem curveDeriv_apply (Ψ g : R[X][Y]) :
    curveDeriv Ψ g = derivative Ψ * derivX g - derivX Ψ * derivative g := rfl

namespace WeightedDegreeLE

variable {w n : ℕ} {g : R[X][Y]}

/-- `∂_X` does not increase the `w`-weighted degree. -/
theorem derivX (hg : WeightedDegreeLE w n g) : WeightedDegreeLE w n (derivX g) := by
  intro j hj
  rw [coeff_derivX] at hj ⊢
  have hgj : g.coeff j ≠ 0 := fun h => by simp [h] at hj
  exact (Nat.add_le_add_right (natDegree_derivative_le _) _).trans
    ((Nat.add_le_add_right (Nat.sub_le _ 1) _).trans (hg j hgj))

/-- If `Ψ` has weighted degree at most `nΨ` and `g` at most `n`, then `δ_Ψ g` has weighted
degree at most `n + nΨ`. -/
theorem curveDeriv {Ψ : R[X][Y]} {nΨ : ℕ} (hΨ : WeightedDegreeLE w nΨ Ψ)
    (hg : WeightedDegreeLE w n g) : WeightedDegreeLE w (n + nΨ) (curveDeriv Ψ g) := by
  rw [curveDeriv_apply, add_comm n]
  exact (hΨ.derivative.mul hg.derivX).sub (hΨ.derivX.mul hg.derivative)

/-- If `Ψ` has weighted degree at most `nΨ` and `g` at most `n`, then `δ_Ψ^j g` has weighted
degree at most `n + j * nΨ`. -/
theorem iterate_curveDeriv {Ψ : R[X][Y]} {nΨ : ℕ} (hΨ : WeightedDegreeLE w nΨ Ψ)
    (hg : WeightedDegreeLE w n g) (j : ℕ) :
    WeightedDegreeLE w (n + j * nΨ) ((Polynomial.Bivariate.curveDeriv Ψ)^[j] g) := by
  induction j with
  | zero => simpa using hg
  | succ j ih =>
    rw [Function.iterate_succ_apply', Nat.succ_mul, ← add_assoc]
    exact WeightedDegreeLE.curveDeriv hΨ ih

end WeightedDegreeLE

end CommRing

section Branch

variable {K : Type*} [Field K]

/-- Evaluation of a bivariate polynomial along the power-series curve `s ↦ (a + s, β)`. -/
noncomputable def branchEval (a : K) (β : PowerSeries K) : K[X][Y] →+* PowerSeries K :=
  (eval₂RingHom (aeval (R := K) (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom β)

/-- `branchEval a β g` is `g`, with `a + s` substituted for `X`, evaluated at `Y = β`. -/
theorem branchEval_apply (a : K) (β : PowerSeries K) (g : K[X][Y]) :
    branchEval a β g =
      (g.map (aeval (R := K)
        (PowerSeries.C a + PowerSeries.X : PowerSeries K)).toRingHom).eval β := by
  rw [branchEval, coe_eval₂RingHom, eval_map]

/-- Evaluation along a branch commutes with scalar multiplication by `K`. -/
theorem branchEval_smul (a : K) (β : PowerSeries K) (c : K) (g : K[X][Y]) :
    branchEval a β (c • g) = c • branchEval a β g := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  simp [branchEval, Polynomial.algebraMap_apply]

/-- The derivative of `h(a + s)` is `h'(a + s)`. -/
theorem derivative_aeval_C_add_X (a : K) (h : K[X]) :
    PowerSeries.derivative (R := K) (aeval (PowerSeries.C a + PowerSeries.X : PowerSeries K) h) =
      aeval (PowerSeries.C a + PowerSeries.X : PowerSeries K) (derivative h) := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, derivative_monomial, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_pow, map_add, PowerSeries.derivative_C, PowerSeries.derivative_X,
      zero_add, mul_one]
    rw [show (algebraMap K (PowerSeries K) c) = PowerSeries.C c from rfl,
      PowerSeries.derivative_C, mul_zero, add_zero, map_mul, map_natCast,
      show (algebraMap K (PowerSeries K) c) = PowerSeries.C c from rfl]
    ring

/-- **The chain rule along a branch**: the derivative of `g(a + s, β(s))` is
`g_X(a + s, β(s)) + g_Y(a + s, β(s)) β'(s)`. -/
theorem derivative_branchEval (a : K) (β : PowerSeries K) (g : K[X][Y]) :
    PowerSeries.derivative (R := K) (branchEval a β g) =
      branchEval a β (derivX g) +
        branchEval a β (derivative g) * PowerSeries.derivative (R := K) β := by
  induction g using Polynomial.induction_on with
  | C h =>
    simp [branchEval]
  | add g h hg hh =>
    rw [map_add, map_add, hg, hh, derivX_add, derivative_add, map_add, map_add]
    ring
  | monomial n h ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih,
      derivX_mul (C h * X ^ n), derivative_mul (f := C h * X ^ n)]
    simp [branchEval]
    ring

/-- On a branch of the curve `Ψ = 0`, the derivation `δ_Ψ` becomes `Ψ_Y · d/ds`. -/
theorem branchEval_curveDeriv {Ψ : K[X][Y]} {a : K} {β : PowerSeries K}
    (hβ : branchEval a β Ψ = 0) (g : K[X][Y]) :
    branchEval a β (curveDeriv Ψ g) =
      branchEval a β (derivative Ψ) * PowerSeries.derivative (R := K) (branchEval a β g) := by
  have h0 := derivative_branchEval a β Ψ
  rw [hβ, map_zero] at h0
  rw [curveDeriv_apply, map_sub, map_mul, map_mul, derivative_branchEval,
    eq_neg_of_add_eq_zero_left h0.symm]
  ring

/-- On a branch of the curve `Ψ = 0`, the iterates of `δ_Ψ` become the iterates of
`u · d/ds`, with `u = Ψ_Y` along the branch. -/
theorem branchEval_iterate_curveDeriv {Ψ : K[X][Y]} {a : K} {β : PowerSeries K}
    (hβ : branchEval a β Ψ = 0) (g : K[X][Y]) (j : ℕ) :
    branchEval a β ((curveDeriv Ψ)^[j] g) =
      (fun G => branchEval a β (derivative Ψ) * PowerSeries.derivative (R := K) G)^[j]
        (branchEval a β g) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', branchEval_curveDeriv hβ, ih]

end Branch

end Polynomial.Bivariate
