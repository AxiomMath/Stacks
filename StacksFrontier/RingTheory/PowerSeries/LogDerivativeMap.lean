module

public import StacksFrontier.RingTheory.PowerSeries.LogDerivative

/-!
# The logarithmic derivative under a change of coefficients

A ring homomorphism `φ : R → S` commutes with the derivative of formal power series, with the
inverse `invOfUnit _ 1` of a series with constant coefficient `1`, and hence with the logarithmic
derivative `T · u' · u⁻¹`.

## Main results

* `PowerSeries.derivative_map`: `(φ u)' = φ (u')`.
* `PowerSeries.map_invOfUnit_one`: `φ (u⁻¹) = (φ u)⁻¹` for `u` with constant coefficient `1`.
* `PowerSeries.map_logDerivative`: `φ (T u' / u) = T (φ u)' / φ u`.
-/

@[expose] public section

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The derivative commutes with a change of coefficients. -/
theorem derivative_map (u : R⟦X⟧) : d⁄dX (map φ u) = map φ (d⁄dX u) := by
  ext n
  simp [coeff_derivative]

/-- The inverse of a series with constant coefficient `1` commutes with a change of
coefficients. -/
theorem map_invOfUnit_one {u : R⟦X⟧} (hu : constantCoeff u = 1) :
    map φ (invOfUnit u 1) = invOfUnit (map φ u) 1 := by
  have hu' : constantCoeff (map φ u) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu,
      map_one]
  calc map φ (invOfUnit u 1)
      = map φ (invOfUnit u 1) * (map φ u * invOfUnit (map φ u) 1) := by
        rw [mul_invOfUnit_one hu', mul_one]
    _ = (map φ u * map φ (invOfUnit u 1)) * invOfUnit (map φ u) 1 := by ring
    _ = invOfUnit (map φ u) 1 := by rw [← map_mul, mul_invOfUnit_one hu, map_one, one_mul]

/-- The logarithmic derivative commutes with a change of coefficients. -/
theorem map_logDerivative {u : R⟦X⟧} (hu : constantCoeff u = 1) :
    map φ (logDerivative u) = logDerivative (map φ u) := by
  rw [logDerivative, logDerivative, map_mul, map_mul, map_X, derivative_map,
    map_invOfUnit_one φ hu]

end PowerSeries

end
