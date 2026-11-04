module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic

/-!
# Irreducibility of a quadratic polynomial with a negative discriminant

Let `R` be a domain and `f = a X² + b X + c ∈ R[X]`. A factorization of `f` into two linear
factors `(g₁ X + g₀)(h₁ X + h₀)` makes the discriminant a square:
`b² - 4ac = (g₁ h₀ - g₀ h₁)²`; a factorization with a constant factor `g₀` makes `g₀` a common
divisor of `a, b, c`. Hence `f` is irreducible as soon as

* `a, b, c` generate the unit ideal of `R`, and
* some ring homomorphism `φ : R → K` to an ordered ring sends `b² - 4ac` to a negative element,

since a square in `R` is sent to a square, which is nonnegative. In practice `R` is a polynomial
ring over `ℚ`, `φ` is the evaluation at a rational point and the first condition is witnessed by
an explicit identity `p a + q b + r c = 1`.

## Main results

* `Polynomial.irreducible_of_discrim_neg`: the criterion above.
-/

@[expose] public section

namespace Polynomial

variable {R K : Type*} [CommRing R] [IsDomain R] [CommRing K] [LinearOrder K]
  [IsStrictOrderedRing K]

/-- **A quadratic polynomial whose coefficients generate the unit ideal and whose discriminant is
negative somewhere is irreducible.** -/
theorem irreducible_of_discrim_neg (φ : R →+* K) {a b c : R}
    (hunit : ∃ p q r : R, p * a + q * b + r * c = 1) (hdisc : φ (b ^ 2 - 4 * a * c) < 0) :
    Irreducible (C a * X ^ 2 + C b * X + C c) := by
  obtain ⟨p, q, r, hpqr⟩ := hunit
  set f : R[X] := C a * X ^ 2 + C b * X + C c with hf
  have hfa : f.coeff 2 = a := by simp [hf]
  have hfb : f.coeff 1 = b := by simp [hf, coeff_C, coeff_X_pow]
  have hfc : f.coeff 0 = c := by simp [hf, coeff_X, coeff_C, coeff_X_pow]
  have ha : a ≠ 0 := by
    rintro rfl
    have : (0 : K) ≤ φ (b ^ 2 - 4 * 0 * c) := by simp [map_pow, sq_nonneg]
    exact absurd hdisc (not_lt.mpr this)
  have hdeg : f.natDegree = 2 := by
    rw [hf]
    exact natDegree_quadratic ha
  have hf0 : f ≠ 0 := fun h => by simp [h] at hdeg
  -- a constant factor divides all the coefficients, hence is a unit
  have hconst : ∀ g h : R[X], f = g * h → g.natDegree = 0 → IsUnit g := by
    intro g h hgh hg
    rw [eq_C_of_natDegree_eq_zero hg] at hgh ⊢
    refine isUnit_C.mpr (isUnit_of_dvd_one ?_)
    have hcoef : ∀ n, f.coeff n = g.coeff 0 * h.coeff n := fun n => by rw [hgh, coeff_C_mul]
    rw [← hpqr]
    refine dvd_add (dvd_add ?_ ?_) ?_
    · exact dvd_mul_of_dvd_right ⟨_, hfa ▸ hcoef 2⟩ _
    · exact dvd_mul_of_dvd_right ⟨_, hfb ▸ hcoef 1⟩ _
    · exact dvd_mul_of_dvd_right ⟨_, hfc ▸ hcoef 0⟩ _
  refine ⟨fun hu => ?_, fun g h hgh => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    omega
  · have hg0 : g ≠ 0 := fun h0 => hf0 (by rw [hgh, h0, zero_mul])
    have hh0 : h ≠ 0 := fun h0 => hf0 (by rw [hgh, h0, mul_zero])
    have hsum : g.natDegree + h.natDegree = 2 := by rw [← natDegree_mul hg0 hh0, ← hgh, hdeg]
    by_cases hg : g.natDegree = 0
    · exact Or.inl (hconst g h hgh hg)
    by_cases hh : h.natDegree = 0
    · exact Or.inr (hconst h g (by rw [hgh, mul_comm]) hh)
    exfalso
    have hg1 : g.natDegree ≤ 1 := by omega
    have hh1 : h.natDegree ≤ 1 := by omega
    have hfgh : f = C (g.coeff 1 * h.coeff 1) * X ^ 2 +
        C (g.coeff 1 * h.coeff 0 + g.coeff 0 * h.coeff 1) * X + C (g.coeff 0 * h.coeff 0) := by
      rw [hgh, eq_X_add_C_of_natDegree_le_one hg1, eq_X_add_C_of_natDegree_le_one hh1]
      simp only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C, coeff_X_zero]
      simp only [one_ne_zero, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add, C_mul, C_add]
      ring
    have e2 : a = g.coeff 1 * h.coeff 1 := by
      rw [← hfa, hfgh]
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num
    have e1 : b = g.coeff 1 * h.coeff 0 + g.coeff 0 * h.coeff 1 := by
      rw [← hfb, hfgh]
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num
    have e0 : c = g.coeff 0 * h.coeff 0 := by
      rw [← hfc, hfgh]
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num
    have hsq : b ^ 2 - 4 * a * c = (g.coeff 1 * h.coeff 0 - g.coeff 0 * h.coeff 1) ^ 2 := by
      rw [e2, e1, e0]; ring
    rw [hsq, map_pow] at hdisc
    exact absurd hdisc (not_lt.mpr (sq_nonneg _))

end Polynomial
