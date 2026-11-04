module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDifferentials
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Serre
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionDrop
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SerreCondition
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.DimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.GeneralDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpNormal
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Sober.Generization
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpClosedPointDimension

/-!
# Further results on `ExceptionalCurve`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve` that
need imports beyond those of that module.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order

universe u

namespace AlgebraicGeometry

section Dimension

end Dimension

open Stacks.Blowup in
open Stacks.Blowup in
/-- **[Stacks, Tag 0B63] clause (1), Cohen–Macaulayness.** In Situation [Stacks, Tag 0B4W] the
exceptional divisor of the blowup of `Spec(A)` in the maximal ideal is Cohen–Macaulay.

The blowup is normal by [Stacks, Tag 0B4Z]
(`AlgebraicGeometry.isNormal_blowUp_maximalIdeal_rationalSingularitySituation`), so the
exceptional divisor satisfies Serre's condition `(S₁)`; in dimension at most one that is
Cohen–Macaulayness. -/
@[stacks 0B63 "clause (1): in Situation 0B4W the exceptional curve of the blowup in the maximal \
ideal is Cohen-Macaulay"]
theorem isCohenMacaulay_exceptionalDivisor_residuePoint_of_situation
    (S : RationalSingularitySituation.{u}) :
    IsCohenMacaulay (exceptionalDivisor (residuePoint S.A).ker) := by
  have hnormal : IsNormal (blowUp (residuePoint S.A).ker) := by
    rw [ker_residuePoint_eq_ofIdealTop_map]
    exact isNormal_blowUp_maximalIdeal_rationalSingularitySituation S
  have := hnormal
  have : IsProper (blowUpToBase (residuePoint S.A).ker) :=
    isProper_blowUpToBase (residuePoint S.A).ker
  have : IsLocallyNoetherian (blowUp (residuePoint S.A).ker) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (residuePoint S.A).ker)
  have : IsLocallyNoetherian (exceptionalDivisor (residuePoint S.A).ker) :=
    LocallyOfFiniteType.isLocallyNoetherian (exceptionalIdeal (residuePoint S.A).ker).subschemeι
  have hsk : HasPropertySk (exceptionalDivisor (residuePoint S.A).ker) 1 :=
    isNormal_effectiveCartierDivisor_hasPropertySk_one _
      (exceptionalIdeal (residuePoint S.A).ker) inferInstance
  have hdimE : topologicalKrullDim (exceptionalDivisor (residuePoint S.A).ker) ≤ 1 :=
    le_of_eq (topologicalKrullDim_exceptionalDivisor_residuePoint S.A S.dimension_two)
  refine (isCohenMacaulay_iff_hasNoEmbeddedPoints_of_topologicalKrullDim_le_one _ hdimE).mpr ?_
  have hsheaf := sheafHasPropertySk_one_of_hasPropertySk_one
    (exceptionalDivisor (residuePoint S.A).ker) hsk
  simpa only [HasNoEmbeddedPoints, IsEmbeddedPoint] using
    (hasNoEmbeddedAssociatedPoints_iff_hasPropertySk_one
      (exceptionalDivisor (residuePoint S.A).ker) _).symm.mp hsheaf

end AlgebraicGeometry

end

end
