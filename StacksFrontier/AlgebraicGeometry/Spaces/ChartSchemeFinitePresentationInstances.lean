module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeFinitePresentation

/-!
# Two instances on the slice at an étale chart

Companions of the instances of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeFinitePresentation.lean`, in the same
slice-as-a-ringed-site spelling: sheafification of abelian sheaves on the slice at a chart, and
the cocontinuity of the functor of the chart-scheme identification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (U : AlgebraicSpaces B S hS) (W : (smallEtaleRingedSite B S hS U.1 U.2).C)

/-- Sheafification of abelian sheaves on the slice at a chart, in the same slice-as-a-ringed-site
spelling. -/
instance hasSheafify_chartSlice :
    HasSheafify ((smallEtaleRingedSite B S hS U.1 U.2).over W).J AddCommGrpCat.{u} :=
  smallEtaleRingedSite_hasSheafify_over B S hS U.1 U.2 W

/-- The functor of the chart-scheme identification is cocontinuous, being a dense subsite
inclusion. -/
instance isCocontinuous_chartSchemeIdentification_functor :
    (chartSchemeIdentification B S hS U W).functor.IsCocontinuous
      (chartSchemeTopology B S hS U W) ((smallEtaleRingedSite B S hS U.1 U.2).over W).J :=
  haveI := isDenseSubsite_chartSchemeIdentification_functor B S hS U W
  inferInstance

end AlgebraicGeometry.Space

end
