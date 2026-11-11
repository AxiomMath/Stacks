module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HypersurfaceSmooth

/-!
# The Fermat quartic is smooth

Let `k` be a field in which `2` is invertible. The Fermat quartic
`X = V(x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴) ⊆ 𝐏³_k` is smooth over `k`: the partial derivatives
`∂F/∂xᵢ = 4 xᵢ³` have no common zero in `𝐏³_k`, since `4 ≠ 0` in `k`, so the projective Jacobian
criterion `Stacks.ProjectiveChart.smooth_of_ker_eq_zeroScheme` applies.

## Main results

* `AlgebraicGeometry.FermatQuartic.pderiv_fermatPolynomial`: `∂F/∂xⱼ = 4 xⱼ³`.
* `AlgebraicGeometry.FermatQuartic.smooth_toSpec`: **the Fermat quartic is smooth over `k`**
  when `2 ≠ 0` in `k`.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

universe u

namespace AlgebraicGeometry.FermatQuartic

variable (k : Type u) [Field k]

/-- The partial derivatives of the Fermat quartic polynomial: `∂F/∂xⱼ = 4 xⱼ³`. -/
theorem pderiv_fermatPolynomial (j : Fin 4) :
    pderiv j (fermatPolynomial k : MvPolynomial (Fin 4) k) = 4 * X j ^ 3 := by
  classical
  rw [coe_fermatPolynomial, map_sum]
  simp [Derivation.leibniz_pow, pderiv_X, Pi.single_apply, Finset.sum_ite_eq']

/-- **The Fermat quartic is smooth over `k`** when `2` is invertible in `k`. -/
instance smooth_toSpec [NeZero (2 : k)] : Smooth (toSpec k) := by
  refine Stacks.ProjectiveChart.smooth_of_ker_eq_zeroScheme (fermatPolynomial k)
    (toProjectiveSpace k) (ker_toProjectiveSpace k) fun j => ⟨3, ?_⟩
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero (NeZero.ne 2) (NeZero.ne 2)
  have hX : X j ^ 3 = C (4 : k)⁻¹ * pderiv j (fermatPolynomial k : MvPolynomial (Fin 4) k) := by
    rw [pderiv_fermatPolynomial, ← mul_assoc,
      ← (map_ofNat (C : k →+* MvPolynomial (Fin 4) k) 4), ← C_mul, inv_mul_cancel₀ h4, C_1,
      one_mul]
  rw [hX]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩))

end AlgebraicGeometry.FermatQuartic

end
