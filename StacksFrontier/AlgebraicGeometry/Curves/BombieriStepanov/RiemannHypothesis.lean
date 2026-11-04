module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.LowerBoundCurve
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.EigenvalueSqrtBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveEigenvaluePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantSheafCurve

/-!
# The Riemann hypothesis for curves, in the form of Tag 03V8

Let `X` be a smooth proper geometrically integral curve over a finite field `k` with `q`
elements and let `A` be the matrix of `π_X^*` on `H¹`, in the form in which Tag 03V8 uses it:
the point counts satisfy the trace formula `hpoint`. If the cup product pairing is a matrix `J`
with `det J` a unit and `Aᵀ J A = q J`, then every reciprocal root `α_i` of `det(1 - A T)` read in
`ℂ` has `‖α_i‖ = √q`.

This combines the point count formula of Tag 03V8, part (3)
(`Stacks.EtaleCohomology.card_rationalPoints_eq_one_sub_sum_add`), the pairing of the
eigenvalues (`Stacks.EtaleCohomology.exists_mul_eq_of_localCharPolynomial`) and the Riemann
hypothesis of Bombieri–Stepanov (`Stacks.BombieriStepanov.norm_eq_sqrt_of_smooth`).

## Main results

* `Stacks.BombieriStepanov.norm_curveEigenvalue_eq_sqrt`
* `Stacks.BombieriStepanov.norm_le_sqrt_of_smooth` (in
  `StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.EigenvalueSqrtBound`): `‖α_i‖ ≤ √q` from
  the point count formula alone.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Matrix

universe u v

namespace Stacks.BombieriStepanov

/-- **The Riemann hypothesis for curves over finite fields, in the form of Tag 03V8.** -/
theorem norm_curveEigenvalue_eq_sqrt {k : Type u} [Field k] [Fintype k] (pr : ℕ)
    [Fact pr.Prime] [CharP k pr] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] [Smooth p]
    [GeometricallyIntegral p] [IsCurve k p] (N : ℕ → ℕ)
    (hNcard : ∀ m : ℕ, m ≠ 0 → ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      Module.finrank k K = m → Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K) = N m)
    {Λ : Type v} [CommRing Λ] {g : ℕ} (A J : Matrix (Fin (2 * g)) (Fin (2 * g)) Λ)
    (hpoint : ∀ n : ℕ, n ≠ 0 → (N n : Λ) =
      ∑ a : Fin 3, (if Even (Stacks.EtaleCohomology.curveDeg a) then (1 : Λ) else -1) *
        ((Stacks.EtaleCohomology.curveFrobenius (Fintype.card k) A a) ^ n).trace)
    (hJ : IsUnit J.det) (hAJ : Aᵀ * J * A = (Fintype.card k : Λ) • J)
    (φ : Λ →+* ℂ) (α : Fin (2 * g) → ℂ)
    (hα : (Stacks.EtaleCohomology.localCharPolynomial A 1).map φ =
      ∏ i, (1 - Polynomial.C (α i) * Polynomial.X)) (i : Fin (2 * g)) :
    ‖α i‖ = Real.sqrt (Fintype.card k) := by
  refine norm_eq_sqrt_of_smooth p pr N hNcard α (fun m hm => ?_) (fun j => ?_) i
  · exact Stacks.EtaleCohomology.card_rationalPoints_eq_one_sub_sum_add
      (Fintype.card k) A N hpoint φ α hα hm
  · exact Stacks.EtaleCohomology.exists_mul_eq_of_localCharPolynomial φ A J (Fintype.card k)
      (by exact_mod_cast Fintype.card_ne_zero) hJ hAJ α hα j

end Stacks.BombieriStepanov

end
