module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurveSections
import StacksCore.Tactic.StacksAttribute

/-!
# The exceptional curve is a proper Cohen–Macaulay curve

In Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal and let
`E ⊆ X` be the exceptional divisor. This file proves clause (1) of [Stacks, Tag 0B63]: `E` is
proper over the residue field `κ`, of dimension one, and Cohen–Macaulay.

The three parts are `AlgebraicGeometry.isProper_exceptionalDivisorToCentre_residuePoint`,
`AlgebraicGeometry.topologicalKrullDim_exceptionalDivisor_residuePoint` and
`AlgebraicGeometry.isCohenMacaulay_exceptionalDivisor_residuePoint`. The last takes the normality
of the blowup as a hypothesis; that normality is [Stacks, Tag 0B4Z],
`AlgebraicGeometry.isNormal_blowUp_maximalIdeal_rationalSingularitySituation`.

## References

* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open Stacks.Blowup

/-- In Situation [Stacks, Tag 0B4W], let `X` be the blowup of `Spec(A)` in the maximal ideal and
`E ⊆ X` its exceptional divisor. Then `E` is a proper Cohen–Macaulay curve over the residue field
`κ`: the morphism `E ⟶ Spec(κ)` is proper, `E` has dimension one, and `E` is Cohen–Macaulay.

Cohen–Macaulayness comes from the normality of `X` ([Stacks, Tag 0B4Z]): `E` is an effective
Cartier divisor on a normal scheme, so it satisfies `(S₁)`, which for a scheme of dimension at
most one is Cohen–Macaulayness. -/
@[stacks 0B63 "clause (1)"]
theorem isProper_and_topologicalKrullDim_eq_one_and_isCohenMacaulay_exceptionalDivisor
    (S : RationalSingularitySituation.{u}) :
    IsProper (exceptionalDivisorToCentre (residuePoint S.A)) ∧
      topologicalKrullDim (exceptionalDivisor (residuePoint S.A).ker) = 1 ∧
      IsCohenMacaulay (exceptionalDivisor (residuePoint S.A).ker) := by
  have hnorm : IsNormal (blowUp (residuePoint S.A).ker) := by
    rw [ker_residuePoint_eq_ofIdealTop_map]
    exact isNormal_blowUp_maximalIdeal_rationalSingularitySituation S
  exact ⟨isProper_exceptionalDivisorToCentre_residuePoint S.A,
    topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two,
    isCohenMacaulay_exceptionalDivisor_residuePoint S.A S.dimension_two hnorm⟩

end AlgebraicGeometry

end
