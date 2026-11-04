module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionTraceCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalCharPolynomial

/-!
# The alternating product of characteristic series is a rational function

For finite free modules `V_i` over a commutative ring `Λ`, nonzero for finitely many `i` only,
with endomorphisms `φ_i`, the alternating product
`∏_i det(1 - φ_i T | V_i)^{(-1)^{i+1}}` of Tag 03V0 is a quotient of two polynomials, the
denominator having constant coefficient `1`: it is
`∏_{i odd} det(1 - φ_i T) / ∏_{i even} det(1 - φ_i T)`.

## Main results

* `Stacks.EtaleCohomology.gradedCharSeries_mul_prod_even`: the identity above.
* `Stacks.EtaleCohomology.exists_gradedCharSeries_mul_eq_polynomial`: the rationality.
-/

@[expose] public noncomputable section

open PowerSeries

universe v w

namespace Stacks.EtaleCohomology

variable {Λ : Type v} [CommRing Λ] [Nontrivial Λ] (V : ℤ → Type w) [∀ i, AddCommGroup (V i)]
  [∀ i, Module Λ (V i)] [∀ i, Module.Finite Λ (V i)] [∀ i, Module.Free Λ (V i)]
  (φ : ∀ i, V i →ₗ[Λ] V i)

/-- The polynomial `det(1 - φ_i T)` in degree `i`, through the matrix of `φ_i` in the basis
`Module.finBasis`. -/
def gradedCharPolynomial (i : ℤ) : Polynomial Λ :=
  localCharPolynomial
    (LinearMap.toMatrix (Module.finBasis Λ (V i)) (Module.finBasis Λ (V i)) (φ i)) 1

/-- **The alternating product as a quotient of polynomials.**  If the `V_i` vanish outside the
finite set `S`, then
`∏_i det(1 - φ_i T)^{(-1)^{i+1}} · ∏_{i ∈ S even} det(1 - φ_i T) = ∏_{i ∈ S odd} det(1 - φ_i T)`.
-/
theorem gradedCharSeries_mul_prod_even (S : Finset ℤ) (hS : ∀ i ∉ S, Subsingleton (V i)) :
    gradedCharSeries V φ * ((∏ i ∈ S.filter Even, gradedCharPolynomial V φ i : Polynomial Λ) :
        Λ⟦X⟧) =
      ((∏ i ∈ S.filter (fun i => ¬ Even i), gradedCharPolynomial V φ i : Polynomial Λ) :
        Λ⟦X⟧) := by
  simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply]
  rw [gradedCharSeries_eq_prod V φ S hS, ← Finset.prod_filter_mul_prod_filter_not S Even, mul_comm,
    ← mul_assoc, ← Finset.prod_mul_distrib]
  have h1 : ∀ i ∈ S.filter Even,
      ((gradedCharPolynomial V φ i : Polynomial Λ) : Λ⟦X⟧) * gradedCharFactor V φ i = 1 := by
    intro i hi
    rw [gradedCharFactor_eq_matrix, if_pos (Finset.mem_filter.1 hi).2, gradedCharPolynomial,
      coe_localCharPolynomial]
    exact localCharSeries_mul_localEulerFactor _ one_ne_zero
  rw [Finset.prod_congr rfl h1, Finset.prod_const_one, one_mul]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [gradedCharFactor_eq_matrix, if_neg (Finset.mem_filter.1 hi).2, gradedCharPolynomial,
    coe_localCharPolynomial]

/-- **The alternating product is a rational function**: its product with a polynomial of
constant coefficient `1` is a polynomial, when only finitely many `V_i` are nonzero. -/
theorem exists_gradedCharSeries_mul_eq_polynomial (hfin : {i : ℤ | Nontrivial (V i)}.Finite) :
    ∃ P Q : Polynomial Λ, Q.eval 0 ≠ 0 ∧ gradedCharSeries V φ * (Q : Λ⟦X⟧) = (P : Λ⟦X⟧) := by
  have hS : ∀ i ∉ hfin.toFinset, Subsingleton (V i) := fun i hi =>
    not_nontrivial_iff_subsingleton.1 fun h => hi (hfin.mem_toFinset.2 h)
  refine ⟨_, _, ?_, gradedCharSeries_mul_prod_even V φ hfin.toFinset hS⟩
  rw [Polynomial.eval_prod, Finset.prod_eq_one fun i _ => ?_]
  · exact one_ne_zero
  · rw [← Polynomial.coeff_zero_eq_eval_zero, gradedCharPolynomial]
    exact coeff_zero_localCharPolynomial _ one_ne_zero

end Stacks.EtaleCohomology

end
