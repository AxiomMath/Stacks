module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.GoodCoordinatePropagation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.RelationPermutation

/-!
# The blowup is regular on the hyperplane of a good coordinate

Let `x₁` be a good coordinate of `A`, with generators `x₁, x₂, x₃` and quadratic form `q`. A
point of the exceptional divisor in the chart of `xⱼ` (`j ≠ 1`) at which `x₁/xⱼ` vanishes, that is
a point on the hyperplane `t₁ = 0`, is a regular point of the blowup: otherwise it is a
`κ`-rational singular point of the conic `q = 0` lying on the line `t₁ = 0`, so that `q(0, t₂, t₃)`
has a double root and is a scalar times a square, contradicting the choice of `x₁`.

## Main results

* `AlgebraicGeometry.exists_rational_point_of_chart_not_isRegularLocalRing`: a singular point of a
  chart at which a fraction `y_{k+1}/y₁` vanishes gives a `κ`-rational point with coordinate `0` at
  `k` at which the dehomogenized form vanishes together with its partial derivatives.
* `AlgebraicGeometry.not_exists_singular_point_at_infinity`: for a good coordinate there is no such
  point of the permuted form with coordinate `0` at the position of that coordinate.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] [IsLocalRing A] {y : Fin 3 → A}
  (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away (y 0) S]

/-- **The rational point of a singular point of a chart, in case I.** At a singular point of the
chart at which a given fraction `y_{k+1}/y₁` vanishes, the point of `κ[y₂, y₃]` it defines is
`κ`-rational with coordinate `0` at `k`, and the dehomogenized form vanishes there together with
its partial derivatives. -/
theorem exists_rational_point_of_chart_not_isRegularLocalRing [IsNoetherianRing A]
    (hspan : Ideal.span (Set.range y) = maximalIdeal A)
    (a : Fin 3 → Fin 3 → A) (hupper : ∀ p q, q < p → a p q = 0)
    (hunit : ∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal A)
    (hrel : ∑ p, ∑ q, a p q * (y p * y q) ∈ maximalIdeal A ^ 3)
    (hcase : ¬ IsScalarSqLinear fun p q => residue A (a p q))
    (z : Ideal (affineBlowupAlgebra (maximalIdeal A) (y 0) S)) [z.IsMaximal]
    (h0 : algebraMap A (affineBlowupAlgebra (maximalIdeal A) (y 0) S) (y 0) ∈ z)
    (k : Fin 2) (hk : chartFraction S (fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩) k.succ ∈ z)
    [IsNoetherianRing (Localization.AtPrime z)]
    (hdim : 2 ≤ ringKrullDim (Localization.AtPrime z))
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime z)) :
    ∃ c : Fin 2 → ResidueField A, c k = 0 ∧
      residue A (a 0 0) + residue A (a 0 1) * c 0 + residue A (a 0 2) * c 1 +
        residue A (a 1 1) * (c 0 * c 0) + residue A (a 1 2) * (c 0 * c 1) +
        residue A (a 2 2) * (c 1 * c 1) = 0 ∧
      residue A (a 0 1) + 2 * (residue A (a 1 1) * c 0) + residue A (a 1 2) * c 1 = 0 ∧
      residue A (a 0 2) + residue A (a 1 2) * c 0 + 2 * (residue A (a 2 2) * c 1) = 0 := by
  have hy : ∀ i, y i ∈ maximalIdeal A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨hM, hmem⟩ := dehomogenized_mem_sq_of_not_isRegularLocalRing S hy hspan a hupper hrel z
    h0 hdim hsing
  set M := Ideal.comap (chartPresentation S hy)
    (Ideal.map (Ideal.Quotient.mk (Ideal.span
      {algebraMap A (affineBlowupAlgebra (maximalIdeal A) (y 0) S) (y 0)})) z) with hMdef
  have hunitk : ∃ p q, p ≤ q ∧ residue A (a p q) ≠ 0 := by
    obtain ⟨p, q, hpq, hne⟩ := hunit
    exact ⟨p, q, hpq, fun h => hne ((residue_eq_zero_iff _).mp h)⟩
  obtain ⟨c, hc⟩ := exists_eval_eq_zero_of_bijective_algebraMap_quotient M
    (bijective_algebraMap_quotient_of_not_isScalarSqLinear (fun p q => residue A (a p q))
      (fun p q h => by rw [hupper p q h, map_zero]) hunitk hcase M hM.ne_top hmem)
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · have hXk : MvPolynomial.X k ∈ M := by
      rw [hMdef, Ideal.mem_comap, chartPresentation, MvPolynomial.eval₂Hom_X']
      exact Ideal.mem_map_of_mem _ hk
    simpa using hc _ hXk
  · have h := hc _ (Ideal.pow_le_self (by norm_num) hmem)
    simp only [map_add, map_mul, map_pow, eval_C, eval_X] at h
    linear_combination h
  · have h := hc _ ((MvPolynomial.pderiv (0 : Fin 2)).map_mem_of_mem_ideal_sq M hmem)
    simp [mul_comm, mul_left_comm, mul_assoc] at h
    linear_combination h
  · have h := hc _ ((MvPolynomial.pderiv (1 : Fin 2)).map_mem_of_mem_ideal_sq M hmem)
    simp [mul_comm, mul_left_comm, mul_assoc] at h
    linear_combination h

/-- **No singular point on the hyperplane of a good coordinate (the algebra).** If `x₁` is a good
coordinate for the upper triangular matrix `a` and `σ` is the transposition `1 ↔ j` (`j ≠ 1`),
there is no point `c` with coordinate `0` at the position of `x₁` at which the dehomogenization of
the permuted form vanishes together with its partial derivatives. -/
theorem not_exists_singular_point_at_infinity {k : Type*} [Field k] (a : Fin 3 → Fin 3 → k)
    (hupper : ∀ p q, q < p → a p q = 0) (hgood : IsGoodCoordinateForm a) (j : Fin 2) :
    ¬ ∃ c : Fin 2 → k, c j = 0 ∧
      (let a' := permuteRelation a (Equiv.swap 0 j.succ)
      a' 0 0 + a' 0 1 * c 0 + a' 0 2 * c 1 + a' 1 1 * (c 0 * c 0) + a' 1 2 * (c 0 * c 1) +
        a' 2 2 * (c 1 * c 1) = 0 ∧
      a' 0 1 + 2 * (a' 1 1 * c 0) + a' 1 2 * c 1 = 0 ∧
      a' 0 2 + a' 1 2 * c 0 + 2 * (a' 2 2 * c 1) = 0) := by
  rintro ⟨c, hcj, h1, h2, h3⟩
  apply hgood
  have h10 := hupper 1 0 (by decide)
  have h20 := hupper 2 0 (by decide)
  have h21 := hupper 2 1 (by decide)
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    simp only [permuteRelation, Fin.succ_zero_eq_one] at h1 h2 h3
    simp (config := {decide := true}) only [Equiv.swap_apply_left, Equiv.swap_apply_right, e2,
      if_true, if_false] at h1 h2 h3
    rw [hcj] at h1 h3
    refine ⟨a 2 2, ![-c 1, 1], fun p => ?_, fun p q hpq => ?_⟩
    · fin_cases p
      · simp only [restrictFirstVar_apply]
        show a 1 1 = a 2 2 * -c 1 * -c 1
        linear_combination h1 - c 1 * h3
      · simp [restrictFirstVar_apply]
    · fin_cases p <;> fin_cases q
      all_goals first | exact absurd hpq (by decide) | skip
      simp only [restrictFirstVar_apply]
      show a 1 2 + a 2 1 = 2 * (a 2 2 * -c 1 * 1)
      linear_combination h3
  · have e1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
    have es : (1 : Fin 2).succ = (2 : Fin 3) := by decide
    simp only [permuteRelation, es] at h1 h2 h3
    simp (config := {decide := true}) only [Equiv.swap_apply_left, Equiv.swap_apply_right, e1,
      if_true, if_false] at h1 h2 h3
    rw [hcj] at h1 h2
    refine ⟨a 1 1, ![1, -c 0], fun p => ?_, fun p q hpq => ?_⟩
    · fin_cases p
      · simp [restrictFirstVar_apply]
      · simp only [restrictFirstVar_apply]
        show a 2 2 = a 1 1 * -c 0 * -c 0
        linear_combination h1 - c 0 * h2
    · fin_cases p <;> fin_cases q
      all_goals first | exact absurd hpq (by decide) | skip
      simp only [restrictFirstVar_apply]
      show a 1 2 + a 2 1 = 2 * (a 1 1 * 1 * -c 0)
      linear_combination h2

end AlgebraicGeometry

end
