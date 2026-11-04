module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.LowerBoundCurve
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.SmoothUpperBound
public import StacksFrontier.NumberTheory.TraceFormula.RiemannHypothesisBound

/-!
# The Riemann inequality `‖α_i‖ ≤ √q` from the point count formula

Let `X` be a smooth proper geometrically integral curve over a finite field with `q` elements and
suppose its point counts are `N m = 1 - ∑ α_i ^ m + q ^ m`. Then every `α_i` has `‖α_i‖ ≤ √q`:
the upper and lower Bombieri–Stepanov bounds make the point counts `q ^ m + O(√q ^ m)`, and the
sector argument of `Stacks.TraceFormula.norm_le_sqrt_of_pointCount` concludes.

This is the declaration `Stacks.BombieriStepanov.norm_le_sqrt_of_smooth` of the Riemann
hypothesis development
`StacksFrontier/AlgebraicGeometry/Curves/BombieriStepanov/RiemannHypothesis.lean`, stated here
without the rest of that file (whose other declaration needs the étale cohomology of the curve).

## Main results

* `Stacks.BombieriStepanov.norm_le_sqrt_of_smooth`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Matrix

universe u v

namespace Stacks.BombieriStepanov

/-- **The Riemann inequality `‖α_i‖ ≤ √q` from the point count formula alone.** For a smooth proper
geometrically integral curve over a finite field with `N m = 1 - ∑ α_i ^ m + q ^ m`, every
`α_i` has `‖α_i‖ ≤ √q`: the point counts are `q ^ m + O(√q ^ m)` by the upper and lower
Bombieri–Stepanov bounds. No pairing of the `α_i` is needed. -/
theorem norm_le_sqrt_of_smooth {k : Type u} [Field k] [Fintype k] (pr : ℕ) [Fact pr.Prime]
    [CharP k pr] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] [Smooth p]
    [GeometricallyIntegral p] [IsCurve k p] (N : ℕ → ℕ)
    (hNcard : ∀ m : ℕ, m ≠ 0 → ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      Module.finrank k K = m → Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K) = N m)
    {ι : Type*} [Fintype ι] (α : ι → ℂ)
    (hN : ∀ m : ℕ, m ≠ 0 → (N m : ℂ) = 1 - (∑ i, α i ^ m) + (Fintype.card k : ℂ) ^ m) (i : ι) :
    ‖α i‖ ≤ Real.sqrt (Fintype.card k) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨C₁, m₁, d₁, hd₁, hup⟩ := exists_upper_bound_of_smooth p pr N hNcard
  obtain ⟨C₂, m₂, d₂, hd₂, hlow⟩ := exists_lower_bound_of_isCurve p pr
    (isDiscreteValuationRing_stalk_of_coheight_eq_one p) N hNcard
  refine Stacks.TraceFormula.norm_le_sqrt_of_pointCount α Fintype.card_pos N hN
    (C := |C₁| + |C₂| + 1) (Nat.mul_ne_zero hd₁ hd₂) (max m₁ m₂) (fun m hm hdm => ?_) i
  have hs : 1 ≤ Real.sqrt (Fintype.card k) ^ m :=
    one_le_pow₀ (Real.one_le_sqrt.mpr (by exact_mod_cast Fintype.card_pos))
  have h1 := hup m (le_of_max_le_left hm) ((dvd_mul_right d₁ d₂).trans hdm)
  have h2 := hlow m (le_of_max_le_right hm) ((dvd_mul_left d₂ d₁).trans hdm)
  have hC₁ := le_abs_self C₁
  have hC₂ := le_abs_self C₂
  have hs0 : (0 : ℝ) ≤ Real.sqrt (Fintype.card k) ^ m := by positivity
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg C₁, abs_nonneg C₂]

end Stacks.BombieriStepanov

end
