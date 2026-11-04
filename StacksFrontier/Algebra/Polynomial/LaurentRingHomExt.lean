module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Ring homomorphisms out of a Laurent polynomial ring

A ring homomorphism `R[T;T⁻¹] →+* S` is determined by its values on the constants and on `T`.

## Main results

* `LaurentPolynomial.ringHom_ext_of_T`
-/

@[expose] public section

namespace LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- **Ring homomorphisms out of a Laurent polynomial ring agree as soon as they agree on the
constants and on `T`.** -/
theorem ringHom_ext_of_T {S : Type*} [CommRing S] {φ ψ : R[T;T⁻¹] →+* S}
    (hC : ∀ r, φ (C r) = ψ (C r)) (hT : φ (T 1) = ψ (T 1)) : φ = ψ := by
  have hu : IsUnit (φ (T 1)) := (isUnit_T 1).map φ
  have hTn : ∀ n : ℤ, φ (T n) = ψ (T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => rw [T_zero, map_one, map_one]
    | succ n ih => rw [T_add, map_mul, map_mul, ih, hT]
    | pred n ih =>
      have h1 : φ (T (-(n : ℤ) - 1)) * φ (T 1) = ψ (T (-(n : ℤ) - 1)) * φ (T 1) := by
        rw [← map_mul, ← T_add, sub_add_cancel, ih, hT, ← map_mul, ← T_add, sub_add_cancel]
      exact hu.mul_left_inj.1 h1
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T n a => rw [map_mul, map_mul, hC, hTn]

end LaurentPolynomial
