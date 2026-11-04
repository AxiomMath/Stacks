module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The Hecke recursion and the local `L`-factor

For an eigenform with eigenvalues `T_v f = t_v f` and `U_v f = u_v f`, the Fourier–Whittaker
coefficients along the powers of the prime divisor `v` satisfy the recursion
`c_{n+2} = t_v c_{n+1} - q_v u_v c_n`, `c_0 = 1`, `c_1 = t_v`. When `t_v = Tr ρ(F_v)` and
`q_v u_v = det ρ(F_v)`, as in Stacks Tags 03VT and 03VU, the generating series of the
coefficients is the local `L`-factor `det (1 - ρ(F_v) X)⁻¹ = (1 - t_v X + q_v u_v X²)⁻¹`. This
file proves that identity of formal power series for an arbitrary commutative ring.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.heckeSeq t d` — the sequence `c_0 = 1`, `c_1 = t`,
  `c_{n+2} = t c_{n+1} - d c_n`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.heckeSeq_mul_eq_one` —
  `(1 - t X + d X²) · ∑ c_n Xⁿ = 1`.
-/

@[expose] public noncomputable section

namespace Stacks.Adeles.GlobalFunctionField

variable {R : Type*} [CommRing R]

/-- The sequence `c_0 = 1`, `c_1 = t`, `c_{n+2} = t c_{n+1} - d c_n` of the Hecke recursion. -/
public def heckeSeq (t d : R) : ℕ → R
  | 0 => 1
  | 1 => t
  | n + 2 => t * heckeSeq t d (n + 1) - d * heckeSeq t d n

/-- The zeroth term of the Hecke recursion is `c_0 = 1`. -/
@[simp]
public theorem heckeSeq_zero (t d : R) : heckeSeq t d 0 = 1 := rfl

/-- The first term of the Hecke recursion is `c_1 = t`. -/
@[simp]
public theorem heckeSeq_one (t d : R) : heckeSeq t d 1 = t := rfl

/-- The Hecke recursion `c_{n+2} = t c_{n+1} - d c_n`. -/
public theorem heckeSeq_add_two (t d : R) (n : ℕ) :
    heckeSeq t d (n + 2) = t * heckeSeq t d (n + 1) - d * heckeSeq t d n := rfl

/-- Twisting `t ↦ c t`, `d ↦ c² d` multiplies `c_n` by `cⁿ`. -/
public theorem heckeSeq_mul_mul (c t d : R) :
    ∀ n, heckeSeq (c * t) (c ^ 2 * d) n = c ^ n * heckeSeq t d n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [heckeSeq_add_two, heckeSeq_add_two, heckeSeq_mul_mul c t d (n + 1),
      heckeSeq_mul_mul c t d n]
    ring

open PowerSeries in
/-- **The local `L`-factor of the Hecke recursion**:
`(1 - t X + d X²) · ∑ₙ cₙ Xⁿ = 1` for the sequence `heckeSeq t d`. -/
public theorem heckeSeq_mul_eq_one (t d : R) :
    (1 - C t * X + C d * X ^ 2) * mk (heckeSeq t d) = 1 := by
  ext n
  rcases n with _ | _ | n
  · simp [sub_mul, add_mul, mul_assoc]
  · simp [sub_mul, add_mul, mul_assoc, coeff_X_pow_mul', coeff_succ_X_mul]
  · simp only [sub_mul, add_mul, mul_assoc, one_mul, map_sub, map_add, coeff_C_mul,
      coeff_X_pow_mul', coeff_succ_X_mul, coeff_mk, coeff_one, heckeSeq_add_two]
    simp

end Stacks.Adeles.GlobalFunctionField
