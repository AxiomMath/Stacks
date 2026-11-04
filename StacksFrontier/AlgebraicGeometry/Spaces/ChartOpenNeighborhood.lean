module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularSections

/-!
# Zariski opens of a pointed étale chart as small étale neighbourhoods

Let `X` be an algebraic space over a scheme `S`, let `x̄` be a geometric point of `X` and let
`V` be a small étale neighbourhood of `x̄` whose chart is a scheme `U`.  A Zariski open `W` of
`U` is again an étale chart of `X` (`AlgebraicGeometry.Space.chartOpens`), and if `W` contains
the point of `U` under the chosen lift of `x̄` then that lift factors through `W`, so `W` is
again a small étale neighbourhood of `x̄`, refining `V`.

This is the cofinal system of neighbourhoods on which the Zariski stalk of the restriction of a
module to the chart and the stalk at the geometric point are compared in Stacks 05VP.

## Main definitions

* `AlgebraicGeometry.Space.chartOpenNeighborhood` is a Zariski open of the chart of a small
  étale neighbourhood, containing the point under the chosen lift, read as a small étale
  neighbourhood of the same geometric point.
* `AlgebraicGeometry.Space.chartOpenNeighborhoodHom` is the morphism of small étale
  neighbourhoods from such an open to the chart it is an open of.

## Main results

* `AlgebraicGeometry.Space.chartOpenNeighborhood_point_comp`: the chosen lift of the geometric
  point into the open composes with the inclusion of the open to the chosen lift into the
  chart.
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {x : GeometricPoint B S hS X}

/-- The lift of a geometric point into a Zariski open of the chart of a small étale
neighbourhood containing the point under the chosen lift. -/
noncomputable def chartOpenLift (V : SmallEtaleNeighborhood x)
    (W : (chartScheme V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    (chartGeometricPoint V).source ⟶ W.toScheme :=
  IsOpenImmersion.lift W.ι (chartGeometricPoint V).hom (by
    rintro _ ⟨z, rfl⟩
    have hz : z = closedPoint (chartGeometricPoint V).residueField := Subsingleton.elim _ _
    subst z
    exact ⟨⟨_, hw⟩, rfl⟩)

/-- The lift into a Zariski open of the chart composes with the inclusion of the open to the
geometric point of the chart. -/
theorem chartOpenLift_comp (V : SmallEtaleNeighborhood x)
    (W : (chartScheme V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    chartOpenLift B S hS V W hw ≫ W.ι = (chartGeometricPoint V).hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- The chosen lift of the geometric point into a Zariski open of the chart, as a morphism over
the base into `AlgebraicGeometry.Space.chartOpenOver`. -/
noncomputable def chartOpenPoint (V : SmallEtaleNeighborhood x)
    (W : (chartScheme V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    x.val.siteObject ⟶ chartOpenOver B S hS V.chart W :=
  Over.homMk (ObjectProperty.homMk (chartOpenLift B S hS V W hw)) (by
    apply ObjectProperty.hom_ext
    change chartOpenLift B S hS V W hw ≫ W.ι ≫ _ = _
    rw [← Category.assoc, chartOpenLift_comp]
    exact congrArg (fun a => a.hom) V.point.w)

/-- The chosen lift into a Zariski open of the chart composes with the inclusion of the open to
the chosen lift into the chart. -/
theorem chartOpenPoint_comp_ι (V : SmallEtaleNeighborhood x)
    (W : (chartScheme V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    chartOpenPoint B S hS V W hw ≫ chartOpenOverι B S hS V.chart W = V.point := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact chartOpenLift_comp B S hS V W hw

/-- **A Zariski open of the chart of a small étale neighbourhood is a small étale
neighbourhood.**  A Zariski open of the chart containing the point under the chosen lift of the
geometric point, read as a small étale neighbourhood of the same geometric point. -/
noncomputable def chartOpenNeighborhood (V : SmallEtaleNeighborhood x)
    (W : (chartScheme V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    SmallEtaleNeighborhood x where
  chart := (chartOpens B S hS V.chart).obj W
  point := chartOpenPoint B S hS V W hw
  point_comp := by
    change V.chart.obj.hom.app _
      (chartOpenPoint B S hS V W hw ≫ chartOpenOverι B S hS V.chart W) = _
    rw [chartOpenPoint_comp_ι]
    exact V.point_comp

/-- The chart of `AlgebraicGeometry.Space.chartOpenNeighborhood` is the Zariski open read as an
étale chart. -/
theorem chartOpenNeighborhood_chart (V : SmallEtaleNeighborhood x)
    (W : (chartScheme V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    (chartOpenNeighborhood B S hS V W hw).chart = (chartOpens B S hS V.chart).obj W :=
  rfl

/-- The chosen lift of the geometric point into a Zariski open of the chart composes with the
inclusion of the open to the chosen lift into the chart. -/
theorem chartOpenNeighborhood_point_comp (V : SmallEtaleNeighborhood x)
    (W : (chartScheme V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    (chartOpenNeighborhood B S hS V W hw).point ≫ chartOpenOverι B S hS V.chart W =
      V.point :=
  chartOpenPoint_comp_ι B S hS V W hw

/-- The inclusion of a Zariski open of the chart of a small étale neighbourhood, as a morphism
of small étale neighbourhoods of the geometric point. -/
noncomputable def chartOpenNeighborhoodHom (V : SmallEtaleNeighborhood x)
    (W : (chartScheme V.chart).Opens) (hw : chartPoint B S hS X V ∈ W) :
    chartOpenNeighborhood B S hS V W hw ⟶ V where
  hom := ObjectProperty.homMk (CostructuredArrow.homMk (chartOpenOverι B S hS V.chart W) rfl)
  point_comp := chartOpenNeighborhood_point_comp B S hS V W hw

end AlgebraicGeometry.Space

end
