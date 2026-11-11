module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import StacksFrontier.RingTheory.PowerSeries.RegularRing

/-!
# Power series in finitely many variables over a regular ring

If `R` is a regular ring, so is `R[[x_1, …, x_n]]`: it is obtained from `R` by adjoining one
power series variable at a time, and the power series ring over a regular ring is regular
(`PowerSeries.isRegularRing_of_isRegularRing`).

## Main results

* `MvPowerSeries.isRegularRing_fin`: `R[[x_1, …, x_n]]` is regular when `R` is.
-/

@[expose] public section

namespace MvPowerSeries

/-- **Power series in finitely many variables over a regular ring form a regular ring.** -/
theorem isRegularRing_fin (R : Type*) [CommRing R] [IsRegularRing R] (n : ℕ) :
    IsRegularRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero => exact IsRegularRing.of_ringEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv.symm
  | succ n ih => exact IsRegularRing.of_ringEquiv (MvPowerSeries.finSuccEquiv R n).toRingEquiv.symm

end MvPowerSeries

end
