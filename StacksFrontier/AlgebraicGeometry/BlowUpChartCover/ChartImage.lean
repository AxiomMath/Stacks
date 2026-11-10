module

public import StacksFrontier.AlgebraicGeometry.BlowUpChartCover.Cartier
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing

/-!
# The affine chart of a blowup, inside the relative-`Proj` chart over its affine open

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on it, `U` an affine open of `X` and
`a ∈ I(U)`. The standard affine chart of the blowup at `a` has image
`Stacks.BlowUpChartCover.chartOpen I U a` in `Bl_I(X)`, and that image sits inside the image of
the relative-`Proj` chart over `U`, `Stacks.RelativeProj.Situation.relativeProjChart`. This file
identifies where: the chart at `a` is the part of the chart over `U` cut out by the degree-one
generator of `a`.

This is what lets a sheaf of modules on `Bl_I(X)` be read over `chartOpen I U a` as a sheaf on
`Proj 𝒜(U)` *and* trivialized there — the trivializations of
`StacksFrontier/AlgebraicGeometry/ProjTrivialization/Basic.lean` live over a standard open of a
projective spectrum, and `chartOpen I U a` is an open of the blowup, so the preimage of the one
has to be recognized as the other.

## Main results

* `Stacks.BlowUpChartCover.chartOpen_eq_image`: the chart's image is the relative-`Proj` chart's
  image of the standard open `D₊(a⁽¹⁾)`.
* `Stacks.BlowUpChartCover.preimage_relativeProjChart_chartOpen`: **the chart's image pulls back,
  along the relative-`Proj` chart over `U`, to `D₊(a⁽¹⁾)`.**

## Implementation notes

`Stacks.BlowUpChartCover.range_chart` already presents the chart's range as the range of
`D₊(a⁽¹⁾).ι ≫ relativeProjChart`; turning that into an image of opens is a set-level
manipulation, and the preimage statement then follows from
`AlgebraicGeometry.Scheme.Hom.preimage_image_eq`, which is where the chart's being an open
immersion is used. The instance is the global
`Stacks.RelativeProj.Situation.isOpenImmersion_relativeProjChart`, which is why this file imports
`StacksFrontier/AlgebraicGeometry/RelativeProjSituation/BaseChangeGluing.lean`: it is not in the
import closure of `StacksFrontier/AlgebraicGeometry/BlowUpChartCover/Cartier.lean`.

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeProj

universe u

namespace Stacks.BlowUpChartCover

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)

/-- **The image of the standard affine chart at `a` is the relative-`Proj` chart's image of the
standard open of the degree-one generator of `a`.** -/
theorem chartOpen_eq_image :
    (chartOpen I U a).1 =
      Situation.relativeProjChart (reesSituation I) U ''ᵁ
        Proj.basicOpen ((reesSituation I).sectionRingGrading U.1) (reesDegreeOne I U a).1 := by
  refine TopologicalSpace.Opens.ext ?_
  change Set.range (chart I U a) = _
  rw [range_chart I U a]
  refine Set.ext fun z => ⟨?_, ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, y.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

/-- **The image of the standard affine chart at `a` pulls back to `D₊(a⁽¹⁾)`.** The preimage,
under the relative-`Proj` chart over `U`, of the image of the standard affine chart at `a` is the
standard open of the degree-one generator of `a`. -/
theorem preimage_relativeProjChart_chartOpen :
    Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ (chartOpen I U a).1 =
      Proj.basicOpen ((reesSituation I).sectionRingGrading U.1) (reesDegreeOne I U a).1 := by
  rw [chartOpen_eq_image I U a, Scheme.Hom.preimage_image_eq]

end Stacks.BlowUpChartCover

end
