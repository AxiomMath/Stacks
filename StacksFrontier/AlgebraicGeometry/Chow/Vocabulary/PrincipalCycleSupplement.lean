module

public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary.PrincipalCycle

/-!
# The order of vanishing of an inverse

On an integral locally Noetherian scheme, the order of vanishing of the inverse of a nonzero
rational function is the negative of its order of vanishing.

## Main results

* `Stacks.Chow.ord_inv_eq_neg'`: if `a * b = 1` with `a` and `b` nonzero rational functions, then
  `ord_ξ(b) = -ord_ξ(a)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The order of vanishing of an inverse -/

/-- The order of vanishing of the inverse of a nonzero rational function is the negative of its
order of vanishing: if `a * b = 1` with `a` and `b` nonzero, then `ord_ξ(b) = -ord_ξ(a)`. -/
theorem ord_inv_eq_neg' {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {a b : X.functionField} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b = 1) (ξ : X) :
    X.ord b ξ = -X.ord a ξ := by
  have hone : X.ord (1 : X.functionField) ξ = 0 := by
    have h := X.ord_mul (x := ξ) (one_ne_zero (α := X.functionField))
      (one_ne_zero (α := X.functionField))
    rw [one_mul] at h
    omega
  have h := X.ord_mul (x := ξ) ha hb
  rw [hab, hone] at h
  omega

end Stacks.Chow
