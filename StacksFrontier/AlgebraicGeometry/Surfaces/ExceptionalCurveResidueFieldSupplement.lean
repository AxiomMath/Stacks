module

public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueField
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveThickeningSurjective
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodFiltration
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningRestriction

/-!
# Further results on `ExceptionalCurveResidueField`

For an exceptional curve of the first kind `D` on a scheme `X` over a field `k`, the residue ring
of the formal neighbourhood of `D` is a field. These are results about the objects of
`StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveResidueField` that need imports beyond
those of that module.

## Main results

* `IdealSheafData.isField_quotient_of_isExceptionalCurveOfFirstKind_unconditional`: the quotient
  of the formal neighbourhood ring of `D` by the first filtration step is a field.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]

/-- **The residue ring of the formal neighbourhood of an exceptional curve of the first kind is a
field**: the quotient of `formalNeighborhoodRing D` by `formalNeighborhoodFiltration D 1` is a
field, with no further hypothesis.

The transition maps of the inverse system of thickenings are surjective for an exceptional curve
of the first kind, by
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
`.surjective_thickeningRestriction`, so the projection to the first thickening is onto and the
residue ring is the field of global functions on the projective line. This is the `hfield` input
of `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodMonomialFiltration`, discharged. -/
public theorem isField_quotient_of_isExceptionalCurveOfFirstKind_unconditional
    {e : projectiveLineProj k ≅ D.subscheme} (hE : IsExceptionalCurveOfFirstKind D k e) :
    IsField (formalNeighborhoodRing D ⧸ formalNeighborhoodFiltration D 1) :=
  isField_quotient_formalNeighborhoodFiltration_one D k
    (hE.surjective_formalNeighborhoodProjection 0) e

end AlgebraicGeometry.Scheme.IdealSheafData

end
