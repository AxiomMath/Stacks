module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.Statement

/-!
# The chart geometry of a relative projective spectrum

For a relative projective spectrum over `S`, the chart over an affine open `U` of the base is an
open immersion whose image is the inverse image of `U`, and these images cover the relative Proj.
The transition morphisms between the charts over nested affine opens compose and are the
identity on a single open. A `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData` on the
constructed relative Proj is determined by a family of chart identifications of the twists.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chartData`: a
  `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData` built from the degreewise chart
  identifications alone.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart`: the chart over an affine
  open of the base is an open immersion.
* `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top`: its image is the inverse image
  of the affine open.
* `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.iSup_toBase_preimage_eq_top`: the inverse images
  of the affine opens of the base cover the relative Proj.
* `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.projInclusionMap_comp` and
  `Stacks.AlgebraicGeometry.RelativeProjTwistGlue.projInclusionMap_self`: the transition
  morphisms compose and are the identity on a single open, for arbitrary nested affine opens of
  the base.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.RelativeProjTwistGlue

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

section Charts

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (P : RelativeProjData A)

/-- The chart of a relative Proj over an affine open of the base is an open immersion. -/
public instance isOpenImmersion_chart (U : S.Opens) (hU : IsAffineOpen U) :
    IsOpenImmersion (P.chart U hU) :=
  MorphismProperty.of_isPullback (P.chart_isPullback U hU).flip inferInstance

/-- The image of the chart over an affine open `U` of the base is the inverse image of `U` under
the structure morphism of the relative Proj. -/
public theorem chart_image_top (U : S.Opens) (hU : IsAffineOpen U) :
    (P.chart U hU) ''ᵁ ⊤ = P.toBase ⁻¹ᵁ U := by
  simpa using IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (P.chart_isPullback U hU).flip ⊤

/-- The inverse images of the affine opens of the base under the structure morphism cover the
relative Proj. -/
public theorem iSup_toBase_preimage_eq_top :
    (⨆ U : S.affineOpens, P.toBase ⁻¹ᵁ (U.1 : S.Opens)) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

end Charts

section Transition

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- The transition morphisms are functorial: for affine opens `U ≤ V ≤ W` of the base, the
transition of `U ≤ V` followed by that of `V ≤ W` is the transition of `U ≤ W`. -/
public theorem projInclusionMap_comp (U V W : S.Opens) (hUV : U ≤ V) (hVW : V ≤ W)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    projInclusionMap A U V hUV hU hV ≫ projInclusionMap A V W hVW hV hW =
      projInclusionMap A U W (hUV.trans hVW) hU hW := by
  refine (cancel_mono ((relativeProj A).chart W hW)).mp ?_
  rw [Category.assoc, (relativeProj A).chart_transition V W hVW hV hW,
    (relativeProj A).chart_transition U V hUV hU hV,
    (relativeProj A).chart_transition U W (hUV.trans hVW) hU hW]

/-- The transition morphism of an affine open into itself is the identity. -/
public theorem projInclusionMap_self (U : S.Opens) (hU : IsAffineOpen U) :
    projInclusionMap A U U le_rfl hU hU = 𝟙 (AlgebraicGeometry.Proj (A.grading U)) := by
  refine (cancel_mono ((relativeProj A).chart U hU)).mp ?_
  rw [(relativeProj A).chart_transition U U le_rfl hU hU, Category.id_comp]

end Transition

section Reduction

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- The `Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData` on the constructed relative Proj
given by a family of isomorphisms, for every affine open of the base and every integer degree,
between the restriction of the homogeneous piece to the chart and the absolute twist. -/
public def chartData (algebra : RelativeProjTwists.SchemeGradedAlgebra (relativeProj A).scheme)
    (e : ∀ (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ),
      Scheme.Modules.restrict (algebra.piece n) ((relativeProj A).chart U hU) ≅
        twistingSheaf (A.grading U) n) :
    RelativeProjTwists.ChartData A algebra where
  chart_isOpenImmersion U hU := isOpenImmersion_chart (relativeProj A) U hU
  chart_range U hU := chart_image_top (relativeProj A) U hU
  chartIso := e

end Reduction

end Stacks.AlgebraicGeometry.RelativeProjTwistGlue

end
