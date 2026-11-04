module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RecoveryFromChartBase

/-!
# Stacks 04KL over a base

`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` is [Stacks Project, Tag 04KL] over a base
in the form its consumers use: a locally ringed morphism `ψ` of the small étale ringed topoi of
two algebraic spaces over `S` which is 2-compatible with a pair of structure morphisms to a
third is induced by exactly one morphism of algebraic spaces over `S`.

`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_holds` proves it with no hypothesis on `S`:
`AlgebraicGeometry.Space.isRecoveredFromSmallEtale_of_isChartOverBase` reduces it to the chart
morphisms of a 2-compatible `ψ` being over `S`, which is
`AlgebraicGeometry.Space.isChartOverBase_of_twoCompatible`.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04KL over an arbitrary base scheme**, in the form of
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`: a locally ringed morphism of the small étale
ringed topoi of two algebraic spaces over `S`, 2-compatible with a pair of structure morphisms to
a third algebraic space, is induced by exactly one morphism of algebraic spaces over `S`. -/
theorem isRecoveredFromSmallEtale_holds : IsRecoveredFromSmallEtale B S hS :=
  isRecoveredFromSmallEtale_of_isChartOverBase B S hS fun pP pQ ψ _ ⟨t⟩ ↦
    isChartOverBase_of_twoCompatible pP pQ ψ t

end AlgebraicGeometry.Space

end
