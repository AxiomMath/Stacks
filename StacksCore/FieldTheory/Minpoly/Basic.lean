module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.PowerBasis

/-! # Minimal Polynomial -/

@[expose] public section

open Polynomial

/-- Scaling an element by a nonzero scalar `c : K` scales the roots of its minimal polynomial:
`minpoly K (c • x)` is `(minpoly K x).scaleRoots c`. -/
theorem minpoly_smul {K A : Type*} [Field K] [Ring A] [Algebra K A]
    {c : K} (x : A) (hc : c ≠ 0) : minpoly K (c • x) = (minpoly K x).scaleRoots c := by
  by_cases hx : IsIntegral K x
  · refine minpoly.eq_of_linearIndependent _ _ ?_ ?_ (minpoly K x).natDegree ?_ ?_
    · simp [monic_scaleRoots_iff, minpoly.monic hx]
    · simp [Algebra.smul_def, scaleRoots_aeval_eq_zero]
    · simp [degree_eq_natDegree (minpoly.ne_zero hx)]
    · convert (linearIndependent_pow (K := K) x).units_smul fun i ↦ .mk0 _ hc ^ i.1 using 2
      · simp [Units.smul_def, smul_pow]
      · rfl
  · have hcx : ¬IsIntegral K (c • x) := fun hcx ↦ hx <| by
      convert hcx.smul c⁻¹; simp [hc]
    rw [minpoly.eq_zero hx, minpoly.eq_zero hcx, zero_scaleRoots]
