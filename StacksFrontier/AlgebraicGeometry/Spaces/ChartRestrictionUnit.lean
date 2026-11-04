module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The chart restriction of the structure sheaf

The restriction `AlgebraicGeometry.Space.restrictToChart` of an `𝒪_X`-module to the scheme of
an étale chart `V` of an algebraic space `X` carries the structure sheaf `𝒪_X` to the structure
sheaf of the chart scheme.

The same holds for the restriction `AlgebraicGeometry.Space.restrictToChartScheme`, by
`AlgebraicGeometry.Space.restrictToChartSchemeUnitIso`; the two restrictions are equal by
`AlgebraicGeometry.Space.restrictToChart_eq_restrictToChartScheme`, and the isomorphism is
transported along that equality.

## Main definitions

* `AlgebraicGeometry.Space.restrictToChartUnitIso`: `𝒪_X|_V ≅ 𝒪_V`.

## References

* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **The chart restriction of the structure sheaf is the structure sheaf of the chart
scheme.** -/
def restrictToChartUnitIso (hF : IsAlgebraicSpace B S hS F) (V : SmallEtale B S hS F) :
    restrictToChart B S hS hF
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))) V ≅
      SheafOfModules.unit (chartScheme V).ringCatSheaf :=
  eqToIso (restrictToChart_eq_restrictToChartScheme B S hS hF _ V) ≪≫
    restrictToChartSchemeUnitIso B S hS F hF V

end AlgebraicGeometry.Space

end
