module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange

/-!
# The base change of an étale chart to a closed subspace

Let `X` be an algebraic space and `Y ⊆ X` a closed subspace in the sense of Stacks 02YU. For
every étale scheme chart `W` of `X`, the base change `W ×_X Y` along the closed immersion
`Y → X` is an étale scheme chart of `Y` (Stacks 03G2, part (4)), its projection to `W` is a
closed immersion of schemes, and its image in `W` is exactly the preimage of `|Y|`. So the
scheme of `W ×_X Y` is a closed subscheme of the scheme of `W` supported on the preimage
of `|Y|`.

## Main definitions

* `AlgebraicGeometry.Space.closedSubspaceBaseChangeChart`: the étale chart `W ×_X Y` of `Y`.
* `AlgebraicGeometry.Space.closedSubspaceBaseChangeChartDiagram`: the cartesian square of
  charts over the inclusion.
* `AlgebraicGeometry.Space.closedSubspaceBaseChangeChartProj`: the projection of schemes
  `W ×_X Y → W`.

## Main results

* `AlgebraicGeometry.Space.isClosedImmersion_closedSubspaceBaseChangeChartProj`: the projection
  is a closed immersion of schemes.
* `AlgebraicGeometry.Space.chartSchemeToPoints_closedSubspaceBaseChangeChartProj`: it is
  compatible with the maps to `|X|`.
* `AlgebraicGeometry.Space.range_closedSubspaceBaseChangeChartProj`: its image is the preimage
  of `|Y|`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Y : Subfunctor X) (hY : IsClosedSubspace B S hS Y)

/-- **The étale chart `W ×_X Y` of a closed subspace `Y ⊆ X`**, the base change of an étale
chart `W` of `X` along the closed immersion `Y → X` (Stacks 03G2, part (4)). -/
abbrev closedSubspaceBaseChangeChart (W : SmallEtale B S hS X) :
    SmallEtale B S hS Y.toFunctor :=
  (smallBaseChange B S hS (closedSubspaceHom B S hS hX Y hY)
    (isClosedImmersion_closedSubspaceHom B S hS hX Y hY).rep).obj W

/-- The cartesian square of charts over the inclusion of a closed subspace, at the base change
of an étale chart `W` of `X`. -/
def closedSubspaceBaseChangeChartDiagram (W : SmallEtale B S hS X) :
    ChartDiagram B S hS Y.toFunctor X (closedSubspaceHom B S hS hX Y hY).hom where
  U := closedSubspaceBaseChangeChart B S hS hX Y hY W
  V := W
  g := (isClosedImmersion_closedSubspaceHom B S hS hX Y hY).rep.snd W.obj.hom
  comm :=
    ((isClosedImmersion_closedSubspaceHom B S hS hX Y hY).rep.isPullback W.obj.hom).w

/-- The projection of schemes `W ×_X Y → W`. -/
abbrev closedSubspaceBaseChangeChartProj (W : SmallEtale B S hS X) :
    chartScheme (closedSubspaceBaseChangeChart B S hS hX Y hY W) ⟶ chartScheme W :=
  (BigFppfOver.toScheme B S hS).map
    (closedSubspaceBaseChangeChartDiagram B S hS hX Y hY W).g

/-- **The projection `W ×_X Y → W` is a closed immersion of schemes**, the base change of the
closed immersion `Y → X` along the chart. -/
theorem isClosedImmersion_closedSubspaceBaseChangeChartProj (W : SmallEtale B S hS X) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      (closedSubspaceBaseChangeChartProj B S hS hX Y hY W) :=
  (isClosedImmersion_closedSubspaceHom B S hS hX Y hY).property_snd W.obj.hom

/-- The projection `W ×_X Y → W` is compatible with the maps to `|X|`: a point of `W ×_X Y`
determines a point of `|Y|` whose image in `|X|` is the point determined by its projection. -/
theorem chartSchemeToPoints_closedSubspaceBaseChangeChartProj (W : SmallEtale B S hS X)
    (y : chartScheme (closedSubspaceBaseChangeChart B S hS hX Y hY W)) :
    chartSchemeToPoints B S hS X W (closedSubspaceBaseChangeChartProj B S hS hX Y hY W y) =
      pointsMap B S hS Y.toFunctor Y.ι
        (chartSchemeToPoints B S hS Y.toFunctor
          (closedSubspaceBaseChangeChart B S hS hX Y hY W) y) :=
  chartSchemeToPoints_map_chartDiagram B S hS
    (closedSubspaceBaseChangeChartDiagram B S hS hX Y hY W) y

/-- **A point of the chart over a point of `Y` lifts to `W ×_X Y`** (Stacks 03H4). -/
theorem exists_closedSubspaceBaseChangeChartProj_eq (W : SmallEtale B S hS X)
    (u : chartScheme W) (hu : chartSchemeToPoints B S hS X W u ∈ subspacePointSet B S hS X Y) :
    ∃ y : chartScheme (closedSubspaceBaseChangeChart B S hS hX Y hY W),
      closedSubspaceBaseChangeChartProj B S hS hX Y hY W y = u := by
  obtain ⟨a, ha⟩ := hu
  set b := (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj W)).symm u with hb
  have hab : pointsMap B S hS Y.toFunctor (closedSubspaceHom B S hS hX Y hY).hom a =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj W)) W.obj.hom b :=
    ha.trans (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X W u)
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
    ((isClosedImmersion_closedSubspaceHom B S hS hX Y hY).rep.isPullback W.obj.hom) a b hab
  refine ⟨pointsToScheme B S hS _ w, ?_⟩
  refine (pointsToScheme_pointsMap_yoneda B S hS
    ((isClosedImmersion_closedSubspaceHom B S hS hX Y hY).rep.snd W.obj.hom) w).symm.trans ?_
  rw [hw, hb]
  exact (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj W)).apply_symm_apply u

/-- **The image of `W ×_X Y → W` is the preimage of `|Y|`.** -/
theorem range_closedSubspaceBaseChangeChartProj (W : SmallEtale B S hS X) :
    Set.range (closedSubspaceBaseChangeChartProj B S hS hX Y hY W) =
      chartSchemeToPoints B S hS X W ⁻¹' subspacePointSet B S hS X Y := by
  ext u
  constructor
  · rintro ⟨y, rfl⟩
    rw [Set.mem_preimage,
      chartSchemeToPoints_closedSubspaceBaseChangeChartProj B S hS hX Y hY W y]
    exact ⟨_, rfl⟩
  · exact exists_closedSubspaceBaseChangeChartProj_eq B S hS hX Y hY W u

end AlgebraicGeometry.Space

end
