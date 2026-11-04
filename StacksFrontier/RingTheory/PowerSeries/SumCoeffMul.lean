module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The sum of the coefficients of a product of power series of bounded degree

Let `R` be a semiring, not necessarily commutative, and `f, g ∈ R⟦X⟧` power series without
coefficients in degrees above `a`, respectively `b`. Then the sum of the coefficients of `f g` up
to degree `a + b` is the product of the sums of the coefficients of `f` and `g`.

## Main results

* `PowerSeries.sum_range_coeff_mul_of_coeff_eq_zero`: the sum of the coefficients of `f g` up to
  degree `a + b` is the product of the sums of the coefficients of `f` and `g`.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- The sum of the coefficients of a product of power series of bounded degree is the product of
the sums of their coefficients: if `f` and `g` have no coefficients in degrees above `a` and `b`,
then `∑_{n ≤ a + b} [Xⁿ] (f g) = (∑_{i ≤ a} [Xⁱ] f) (∑_{j ≤ b} [Xʲ] g)`. -/
theorem sum_range_coeff_mul_of_coeff_eq_zero (f g : R⟦X⟧) {a b : ℕ}
    (hf : ∀ i, a < i → coeff i f = 0) (hg : ∀ j, b < j → coeff j g = 0) :
    ∑ n ∈ Finset.range (a + b + 1), coeff n (f * g) =
      (∑ i ∈ Finset.range (a + 1), coeff i f) * ∑ j ∈ Finset.range (b + 1), coeff j g := by
  simp only [coeff_mul]
  rw [Finset.sum_mul_sum, Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij_ne_zero (fun x _ _ => ⟨x.2.1, x.2.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨n, i, j⟩ - hx
    have hi : i ≤ a := by
      by_contra! hi
      exact hx (by simp [hf i hi])
    have hj : j ≤ b := by
      by_contra! hj
      exact hx (by simp [hg j hj])
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · rintro ⟨n, i, j⟩ h₁ - ⟨n', i', j'⟩ h₁' - he
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal, Sigma.mk.injEq,
      heq_eq_eq] at h₁ h₁' he
    obtain ⟨rfl, rfl⟩ := he
    obtain rfl : n = n' := by omega
    rfl
  · rintro ⟨i, j⟩ hij hne
    simp only [Finset.mem_sigma, Finset.mem_range] at hij
    exact ⟨⟨i + j, i, j⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (by dsimp only; omega),
      Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩, hne, rfl⟩
  · rintro ⟨n, i, j⟩ - -
    rfl

end PowerSeries

end
