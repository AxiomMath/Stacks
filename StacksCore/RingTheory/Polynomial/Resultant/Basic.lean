module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import StacksCore.Algebra.Polynomial.Derivative

/-! # Resultants -/

@[expose] public section

namespace Polynomial

/-- A monic polynomial `p` over a commutative ring is separable iff the resultant of `p` and
`p.derivative` is a unit. -/
theorem Monic.separable_iff_isUnit_resultant
    {R : Type*} [CommRing R] {p : R[X]} (hp : p.Monic) :
    p.Separable ↔ IsUnit (p.resultant p.derivative) := by
  rw [Separable, ← isUnit_resultant_iff_isCoprime hp]

/-- A monic polynomial `p` whose natural degree is invertible in `R` is separable iff its
discriminant `p.discr` is a unit. -/
theorem Monic.separable_iff_isUnit_discr
    {R : Type*} [CommRing R] {p : R[X]} (hp : p.Monic) (hn : (p.natDegree : R) ≠ 0) :
    p.Separable ↔ IsUnit p.discr := by
  have hn0 : p.natDegree ≠ 0 := fun h0 ↦ hn <| by simp [h0]
  have hn0' := natDegree_pos_iff_degree_pos.mp (pos_of_ne_zero hn0)
  rw [Separable, ← isUnit_resultant_iff_isCoprime hp, hp.natDegree_derivative hn,
    resultant_deriv hn0', hp, mul_one, IsUnit.mul_iff]
  simp [IsUnit.pow]

end Polynomial
