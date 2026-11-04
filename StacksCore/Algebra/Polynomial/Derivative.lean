module

public import Mathlib.Algebra.Polynomial.Derivative

/-! # Derivative of polynomials -/

@[expose] public section

namespace Polynomial

/-- If `p` is monic over a semiring `R` and the image of `p.natDegree` in `R` is nonzero,
then `p.derivative` has natural degree exactly `p.natDegree - 1`. -/
theorem Monic.natDegree_derivative {R : Type*} [Semiring R] {p : R[X]}
    (hp : p.Monic) (hn : (p.natDegree : R) ≠ 0) : p.derivative.natDegree = p.natDegree - 1 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero p.natDegree_derivative_le ?_
  have hn0 : p.natDegree ≠ 0 := fun h0 ↦ hn <| by simp [h0]
  rw [coeff_derivative, ← Nat.cast_add_one, Nat.sub_add_cancel (by grind), hp.coeff_natDegree]
  simpa

end Polynomial
