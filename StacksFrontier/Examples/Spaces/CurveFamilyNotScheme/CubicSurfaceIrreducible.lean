module

public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeCurveDimension
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface

/-!
# The cubic surface is irreducible

The surface `Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t T₀ T₁ T₂ = 0` of Stacks 0D5E is `Proj` of
`k[t][T₀, T₁, T₂] ⧸ (F)`. Read as a polynomial in `t` over `k[T₀, T₁, T₂]`, the equation is
`F₀ - t · T₀ T₁ T₂` with `F₀ = T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3`, of degree one with coprime coefficients
(no variable `Tᵢ` divides `F₀`), hence irreducible, hence prime because the polynomial ring is
factorial. So the homogeneous coordinate ring is a domain, and `Y`, the `Proj` of a nonempty
graded domain, is irreducible.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.prime_cubicEquation`: the equation of `Y` is prime.
* `Stacks.Examples.CurveFamilyNotScheme.nonempty_cubicSurface`: `Y` is nonempty.
* `Stacks.Examples.CurveFamilyNotScheme.irreducibleSpace_cubicSurface`: `Y` is irreducible.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry MvPolynomial Stacks.AlgebraicGeometry.ProjPolyChart
  Stacks.RingTheory.HomogeneousQuotient

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The ring isomorphism `k[t][T₀, T₁, T₂] ≃ k[T₀, T₁, T₂][t]` exchanging the roles of the
coefficient variable and the polynomial variables. -/
def swapEquiv :
    MvPolynomial (Fin 3) (Polynomial k) ≃ₐ[k] Polynomial (MvPolynomial (Fin 3) k) :=
  (optionEquivRight k (Fin 3)).symm.trans (optionEquivLeft k (Fin 3))

/-- `swapEquiv` sends the variable `Tᵢ` to the constant `Tᵢ`. -/
theorem swapEquiv_X (i : Fin 3) : swapEquiv k (X i) = Polynomial.C (X i) := by
  have h : (optionEquivRight k (Fin 3)).symm (X i) = X (some i) :=
    (AlgEquiv.symm_apply_eq _).mpr (optionEquivRight_X_some k (Fin 3) i).symm
  rw [swapEquiv, AlgEquiv.trans_apply, h, optionEquivLeft_X_some]

/-- `swapEquiv` sends the coefficient `t` to the variable `t`. -/
theorem swapEquiv_C_X : swapEquiv k (C Polynomial.X) = Polynomial.X := by
  have h : (optionEquivRight k (Fin 3)).symm (C Polynomial.X) = X none :=
    (AlgEquiv.symm_apply_eq _).mpr (optionEquivRight_X_none k (Fin 3)).symm
  rw [swapEquiv, AlgEquiv.trans_apply, h, optionEquivLeft_X_none]

/-- Under `swapEquiv`, the equation of `Y` is `F₀ - t · T₀ T₁ T₂`, of degree one in `t`. -/
theorem swapEquiv_cubicEquation :
    swapEquiv k (cubicEquation k) =
      Polynomial.C (X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3) -
        Polynomial.X * Polynomial.C (X 0 * X 1 * X 2) := by
  simp [cubicEquation, swapEquiv_X, swapEquiv_C_X, map_sub, map_add, map_mul, map_pow]

/-- No variable `Tᵢ` divides the Fermat cubic. -/
theorem not_X_dvd_fermat (i : Fin 3) :
    ¬ (X i : MvPolynomial (Fin 3) k) ∣ X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 := by
  rintro ⟨q, hq⟩
  -- evaluate at the point with `Tᵢ = 0` and the other two coordinates `1` and `0`
  fin_cases i
  · have h := congrArg (MvPolynomial.eval ![0, 1, 0]) hq
    simp at h
  · have h := congrArg (MvPolynomial.eval ![1, 0, 0]) hq
    simp at h
  · have h := congrArg (MvPolynomial.eval ![1, 0, 0]) hq
    simp at h

/-- The Fermat cubic and the monomial `T₀ T₁ T₂` have no common factor. -/
theorem isRelPrime_fermat_monomial :
    IsRelPrime (X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 : MvPolynomial (Fin 3) k) (X 0 * X 1 * X 2) := by
  have h : ∀ i : Fin 3, IsRelPrime (X 0 ^ 3 + X 1 ^ 3 + X 2 ^ 3 : MvPolynomial (Fin 3) k) (X i) :=
    fun i => ((MvPolynomial.X_prime (R := k) (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr
      (not_X_dvd_fermat k i)).symm
  exact ((h 0).mul_right (h 1)).mul_right (h 2)

/-- **The equation of the cubic surface is prime** in `k[t][T₀, T₁, T₂]`. -/
theorem prime_cubicEquation : Prime (cubicEquation k) := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  refine (MulEquiv.irreducible_iff (swapEquiv k).toMulEquiv).mp ?_
  change Irreducible (swapEquiv k (cubicEquation k))
  rw [swapEquiv_cubicEquation]
  have hm : (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1)) (X_ne_zero 2)
  refine Polynomial.irreducible_of_degree_eq_one_of_isRelPrime_coeff ?_ ?_
  · rw [sub_eq_add_neg, ← mul_neg, ← map_neg, mul_comm, add_comm]
    exact Polynomial.degree_linear (neg_ne_zero.mpr hm)
  · simp only [Polynomial.coeff_sub, Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero,
      sub_zero, Polynomial.coeff_C_succ, Polynomial.coeff_X_mul, zero_sub]
    exact (isRelPrime_fermat_monomial k).neg_right

/-- The homogeneous ideal of the cubic surface is prime. -/
theorem isPrime_cubicIdeal : (cubicIdeal k).toIdeal.IsPrime :=
  (Ideal.span_singleton_prime (prime_cubicEquation k).ne_zero).mpr (prime_cubicEquation k)

/-- **The cubic surface is nonempty**: its homogeneous coordinate ring is a domain whose zero ideal
is relevant, because `T₀` is not a multiple of the equation. -/
theorem nonempty_cubicSurface : Nonempty (cubicSurface k) := by
  have := isPrime_cubicIdeal k
  have : IsDomain (MvPolynomial (Fin 3) (Polynomial k) ⧸ (cubicIdeal k).toIdeal) :=
    Ideal.Quotient.isDomain _
  refine ⟨⟨⊥, by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot, fun hle => ?_⟩⟩
  have hmem : Ideal.Quotient.mk (cubicIdeal k).toIdeal (MvPolynomial.X 0) ∈
      (⊥ : HomogeneousIdeal (quotientGrading (polyGrading (Polynomial k) 2) (cubicIdeal k))) :=
    hle (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
      (Stacks.RingTheory.HomogeneousQuotient.quotientGrading_mk_mem _ _
        (MvPolynomial.isHomogeneous_X (Polynomial k) 0)))
  have hdvd : cubicEquation k ∣ MvPolynomial.X 0 := Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_bot.mp (HomogeneousIdeal.mem_iff.mpr hmem)))
  obtain ⟨q, hq⟩ := ((prime_cubicEquation k).irreducible.associated_of_dvd
    (MvPolynomial.X_prime (R := Polynomial k) (i := 0)).irreducible hdvd).symm.dvd
  have hev := congrArg (MvPolynomial.eval (![0, 0, 1] : Fin 3 → Polynomial k)) hq
  simp [cubicEquation] at hev

/-- **The cubic surface is irreducible**: it is `Proj` of a nonempty graded domain. -/
theorem irreducibleSpace_cubicSurface : IrreducibleSpace (cubicSurface k) := by
  have := isPrime_cubicIdeal k
  have : IsDomain (MvPolynomial (Fin 3) (Polynomial k) ⧸ (cubicIdeal k).toIdeal) :=
    Ideal.Quotient.isDomain _
  have : Nonempty (AlgebraicGeometry.Proj
      (quotientGrading (polyGrading (Polynomial k) 2) (cubicIdeal k))) :=
    nonempty_cubicSurface k
  exact AlgebraicGeometry.irreducibleSpace_proj_of_isDomain _

end Stacks.Examples.CurveFamilyNotScheme

end
