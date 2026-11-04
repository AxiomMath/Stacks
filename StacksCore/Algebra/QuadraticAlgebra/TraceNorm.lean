module

public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import StacksCore.RingTheory.Discriminant
public import StacksCore.RingTheory.NormTrace

/-! # Trace and Norm of Quadratic Algebra -/

@[expose] public section

open Algebra Polynomial Matrix

namespace QuadraticAlgebra

section comm_semiring
variable {R : Type*} [CommSemiring R] {a b : R} (z : QuadraticAlgebra R a b)

-- `QuadraticAlgebra.trace` and its `trace_def`, `trace_one`, `trace_omega` lemmas used to live
-- here; Mathlib gained them in #42207 with identical statements, along with `trace_algebraMap`,
-- `trace_natCast`, `trace_intCast` and `trace_star`. Our `basis_zero` and `basis_one` went the
-- same way: Mathlib now has them as the `@[simp]` lemmas `basis_apply_zero` and `basis_apply_one`,
-- so `simpNF` reported ours as duplicates once the pin caught up. What remains below is the
-- matrix API, plus the bridges to `Algebra.trace'`, `Algebra.norm` and `discr'`.

/-- The matrix of left multiplication by `z` in the standard basis `{1, ω}`. -/
theorem leftMulMatrix_basis_eq :
    leftMulMatrix (basis a b) z = !![z.re, a * z.im; z.im, z.re + b * z.im] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftMulMatrix_eq_repr_mul]

end comm_semiring

section comm_ring
variable {R : Type*} [CommRing R] {a b : R} (z : QuadraticAlgebra R a b)

-- `QuadraticAlgebra.trace` is stated over a `CommRing` upstream, so this bridge lives here
-- rather than in the `CommSemiring` section where it used to sit.
/-- The Mathlib `Algebra.trace` agrees with the explicit formula in `QuadraticAlgebra.trace`. -/
@[simp] theorem trace_eq : Algebra.trace' R _ z = z.trace := by
  simp only [trace_eq_matrix_trace' (basis a b), leftMulMatrix_basis_eq, trace_fin_two_of,
    trace_def]
  grind

/-- The Mathlib `Algebra.norm` agrees with the explicit `QuadraticAlgebra.norm`. -/
@[simp] theorem norm_eq : Algebra.norm R z = z.norm := z.det_toLinearMap_eq_norm

/-- The discriminant class of `QuadraticAlgebra R a b` is the class of `b ^ 2 + 4 * a`. -/
@[simp] theorem discr'_eq : discr' R (QuadraticAlgebra R a b) = .mk _ (b ^ 2 + 4 * a) := by
  simp only [← mk_discr_eq_discr' (basis a b), discr, det_fin_two, Fin.isValue, traceMatrix_apply,
    basis_apply_zero, traceForm_apply, trace_eq_trace', mul_one, trace_eq, trace_one,
    basis_apply_one, omega_mul_omega_eq_add, map_add, map_smul, smul_eq_mul, trace_omega, one_mul]
  ring_nf

end comm_ring

end QuadraticAlgebra
