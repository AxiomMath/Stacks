module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The logarithmic derivative of a formal power series

A power series `u` with constant coefficient `1` is a unit of `R⟦T⟧`, and the series
`T · u' · u⁻¹` is the operator `T d/dT log` applied to `u`, without any logarithm having to
exist.  It is additive in `u`, turns inverses into negatives, and — over a ring whose additive
group is torsion free — determines `u` among the series with constant coefficient `1`.  That
last statement is the substitute for "take logarithmic derivatives of both sides" in a
characteristic zero argument.

The coefficient of `T ^ m` of `T · u' · u⁻¹` depends only on `u` modulo `T ^ (m + 1)`, which is
what makes the operator usable on a series defined only as a limit of truncations, such as an
Euler product.

## Main definitions

* `PowerSeries.logDerivative`: the series `T · u' · u⁻¹`.

## Main results

* `PowerSeries.logDerivative_mul` and `PowerSeries.logDerivative_finsetProd`: additivity.
* `PowerSeries.logDerivative_invOfUnit`: inverses go to negatives.
* `PowerSeries.eq_of_logDerivative_eq`: injectivity on series with constant coefficient `1`,
  over a ring with torsion-free additive group.
* `PowerSeries.coeff_logDerivative_congr`: the coefficient of `T ^ m` only sees `u` modulo
  `T ^ (m + 1)`.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The logarithmic derivative `T · u' · u⁻¹` of a formal power series, computed with the
inverse that exists when the constant coefficient is `1`.  Away from that case the definition
carries no meaning. -/
noncomputable def logDerivative (u : R⟦X⟧) : R⟦X⟧ := X * d⁄dX R u * invOfUnit u 1

/-- A power series with constant coefficient `1` is inverted by `invOfUnit _ 1`. -/
theorem mul_invOfUnit_one {u : R⟦X⟧} (hu : constantCoeff u = 1) : u * invOfUnit u 1 = 1 :=
  mul_invOfUnit u 1 (by simpa using hu)

/-- The inverse supplied by `invOfUnit _ 1` has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_invOfUnit_one (u : R⟦X⟧) :
    constantCoeff (invOfUnit u (1 : Rˣ)) = 1 := by
  simp [constantCoeff_invOfUnit]

/-- A power series with vanishing derivative is its own constant coefficient, provided the
additive group of the coefficient ring is torsion free. -/
theorem eq_C_of_derivative_eq_zero [IsAddTorsionFree R] {u : R⟦X⟧} (h : d⁄dX R u = 0) :
    u = C (constantCoeff u) :=
  derivative.ext (by rw [h, derivative_C]) (by simp)

/-- The inverse of a product of two series with constant coefficient `1`. -/
theorem invOfUnit_one_mul {u v : R⟦X⟧} (hu : constantCoeff u = 1) (hv : constantCoeff v = 1) :
    invOfUnit (u * v) 1 = invOfUnit u 1 * invOfUnit v 1 := by
  have h1 : u * v * invOfUnit (u * v) 1 = 1 := mul_invOfUnit_one (by simp [hu, hv])
  have h2 : u * v * (invOfUnit u 1 * invOfUnit v 1) = 1 := by
    linear_combination (v * invOfUnit v 1) * mul_invOfUnit_one hu + mul_invOfUnit_one hv
  linear_combination invOfUnit u 1 * invOfUnit v 1 * h1 - invOfUnit (u * v) 1 * h2

/-- The Leibniz rule for the derivative of power series, with multiplication in place of `•`. -/
private theorem derivative_mul_eq (a b : R⟦X⟧) :
    d⁄dX R (a * b) = a * d⁄dX R b + b * d⁄dX R a := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

/-- The logarithmic derivative has vanishing constant coefficient, being a multiple of `T`. -/
@[simp]
theorem constantCoeff_logDerivative (u : R⟦X⟧) : constantCoeff (logDerivative u) = 0 := by
  simp [logDerivative]

/-- The logarithmic derivative of `1` vanishes. -/
@[simp]
theorem logDerivative_one : logDerivative (1 : R⟦X⟧) = 0 := by simp [logDerivative]

/-- The logarithmic derivative is additive on series with constant coefficient `1`. -/
theorem logDerivative_mul {u v : R⟦X⟧} (hu : constantCoeff u = 1) (hv : constantCoeff v = 1) :
    logDerivative (u * v) = logDerivative u + logDerivative v := by
  have hu' := mul_invOfUnit_one hu
  have hv' := mul_invOfUnit_one hv
  rw [logDerivative, logDerivative, logDerivative, invOfUnit_one_mul hu hv, derivative_mul_eq]
  linear_combination (X * d⁄dX R v * invOfUnit v 1) * hu' +
    (X * d⁄dX R u * invOfUnit u 1) * hv'

/-- The logarithmic derivative of a finite product of series with constant coefficient `1`. -/
theorem logDerivative_finsetProd {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 1) :
    logDerivative (∏ i ∈ s, f i) = ∑ i ∈ s, logDerivative (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hprod : constantCoeff (∏ i ∈ s, f i) = 1 := by
        rw [map_prod]
        exact Finset.prod_eq_one fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        logDerivative_mul (hf a (Finset.mem_insert_self a s)) hprod,
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- The logarithmic derivative of the inverse of a series with constant coefficient `1`. -/
theorem logDerivative_invOfUnit {u : R⟦X⟧} (hu : constantCoeff u = 1) :
    logDerivative (invOfUnit u 1) = -logDerivative u := by
  have h := logDerivative_mul hu (constantCoeff_invOfUnit_one u)
  rw [mul_invOfUnit_one hu, logDerivative_one] at h
  linear_combination -h

/-- Two power series with constant coefficient `1` and the same logarithmic derivative agree,
provided the additive group of the coefficient ring is torsion free. -/
@[sga "6 V 7.5" "(ii)"]
theorem eq_of_logDerivative_eq [IsAddTorsionFree R] {u v : R⟦X⟧}
    (hu : constantCoeff u = 1) (hv : constantCoeff v = 1)
    (h : logDerivative u = logDerivative v) : u = v := by
  have hu' := mul_invOfUnit_one hu
  have hv' := mul_invOfUnit_one hv
  have hcross : d⁄dX R u * v = d⁄dX R v * u := by
    refine X_mul_cancel ?_
    have h' : logDerivative u * (u * v) = logDerivative v * (u * v) := by rw [h]
    rw [logDerivative, logDerivative] at h'
    linear_combination h' - (X * d⁄dX R u * v) * hu' + (X * d⁄dX R v * u) * hv'
  have hleib : v * d⁄dX R (invOfUnit v 1) + invOfUnit v 1 * d⁄dX R v = 0 := by
    have hc := congrArg (d⁄dX R) hv'
    rwa [derivative_mul_eq, derivative_one] at hc
  have hzero : d⁄dX R (u * invOfUnit v 1) = 0 := by
    rw [derivative_mul_eq]
    linear_combination (invOfUnit v 1 * u) * hleib + (invOfUnit v 1 ^ 2) * hcross -
      (u * d⁄dX R (invOfUnit v 1) + invOfUnit v 1 * d⁄dX R u) * hv'
  have hone : u * invOfUnit v 1 = 1 := by
    rw [eq_C_of_derivative_eq_zero hzero]
    simp [hu]
  linear_combination v * hone - u * hv'

/-- The coefficient of `T ^ m` of the logarithmic derivative depends only on the series modulo
`T ^ (m + 1)`.  This is what allows the operator to be applied to a convergent infinite
product through its finite truncations. -/
theorem coeff_logDerivative_congr {u v : R⟦X⟧} {m : ℕ} (hu : constantCoeff u = 1)
    (hv : constantCoeff v = 1) (h : (X : R⟦X⟧) ^ (m + 1) ∣ u - v) :
    coeff m (logDerivative u) = coeff m (logDerivative v) := by
  have hu' := mul_invOfUnit_one hu
  have hv' := mul_invOfUnit_one hv
  have hinv : (X : R⟦X⟧) ^ (m + 1) ∣ invOfUnit u 1 - invOfUnit v 1 := by
    have he : invOfUnit u 1 - invOfUnit v 1 = invOfUnit u 1 * invOfUnit v 1 * (v - u) := by
      linear_combination invOfUnit v 1 * hu' - invOfUnit u 1 * hv'
    rw [he, ← neg_sub]
    exact h.neg_right.mul_left _
  have hder : (X : R⟦X⟧) ^ (m + 1) ∣ X * d⁄dX R u - X * d⁄dX R v := by
    obtain ⟨g, hg⟩ := h
    have hsub : X * d⁄dX R u - X * d⁄dX R v = X * d⁄dX R (u - v) := by rw [map_sub]; ring
    refine ⟨X * d⁄dX R g + ((m : R⟦X⟧) + 1) * g, ?_⟩
    rw [hsub, hg, Derivation.leibniz, derivative_pow, derivative_X]
    push_cast
    simp only [smul_eq_mul]
    ring
  have hsplit : logDerivative u - logDerivative v
      = (X * d⁄dX R u - X * d⁄dX R v) * invOfUnit u 1
        + X * d⁄dX R v * (invOfUnit u 1 - invOfUnit v 1) := by
    simp only [logDerivative]
    ring
  have hdvd : (X : R⟦X⟧) ^ (m + 1) ∣ logDerivative u - logDerivative v := by
    rw [hsplit]
    exact dvd_add (hder.mul_right _) (hinv.mul_left _)
  have hz := PowerSeries.X_pow_dvd_iff.1 hdvd m (Nat.lt_succ_self m)
  rw [map_sub, sub_eq_zero] at hz
  exact hz

end PowerSeries

end
