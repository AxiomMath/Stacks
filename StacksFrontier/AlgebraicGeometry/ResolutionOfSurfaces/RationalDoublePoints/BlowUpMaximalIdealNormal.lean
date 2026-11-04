module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpCompletionNormal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpNormal
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormalityExtra

/-!
# Blowing up the maximal ideal of a rational surface singularity

`AlgebraicGeometry.BlowUpMaximalIdealIsNormal` is the statement of [Stacks, Tag 0B4Z]: for every
local normal Nagata domain `B` of dimension two defining a rational singularity, the blowup of
`Spec(B)` in the maximal ideal is normal. This file proves it.

## Main results

* `AlgebraicGeometry.blowUpMaximalIdealIsNormal`: `BlowUpMaximalIdealIsNormal` holds.

## References

* [Stacks Project, Tag 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- The blowup of the spectrum of a two-dimensional local normal Nagata domain defining a rational
singularity in its maximal ideal is a normal scheme ([Stacks, Tag 0B4Z]). -/
theorem blowUpMaximalIdealIsNormal : BlowUpMaximalIdealIsNormal.{u} :=
  fun B _ _ _ hnag hdim hrat =>
    isNormal_blowUp_maximalIdeal_of_forall_isIntegrallyClosed_pow B fun n =>
      isIntegrallyClosed_maximalIdeal_pow_of_definesRationalSingularity B hnag hdim hrat n

end AlgebraicGeometry

end
