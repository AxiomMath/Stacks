module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange

/-!
# The base change of an étale chart to a prime divisor

Let `X` be an algebraic space, `Z ⊂ X` a prime divisor and `W` an étale scheme chart of `X`.
The étale chart `W ×_X Z` of `Z` is the base change of `W` along the closed immersion `Z → X`
(Stacks 03G2, part (4)). Its projection to `W` is a closed immersion of schemes, its scheme is
reduced, and its image is exactly the preimage of `|Z|` in the chart. So the scheme of `W ×_X Z`
is the reduced closed subscheme of the scheme of `W` on the preimage of `|Z|`.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.inclusionHom`: the closed immersion `Z → X` as a
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChart`: the étale chart `W ×_X Z` of `Z`.
* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartDiagram`: the cartesian square of charts.
* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartProj`: the projection of schemes
  `W ×_X Z → W`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.isClosedImmersion_baseChangeChartProj`: the projection
  is a closed immersion.
* `AlgebraicGeometry.Space.PrimeDivisor.chartSchemeToPoints_baseChangeChartProj`: it is
  compatible with the maps to `|X|`.
* `AlgebraicGeometry.Space.PrimeDivisor.range_baseChangeChartProj`: its image is the preimage
  of `|Z|`.
* `AlgebraicGeometry.Space.PrimeDivisor.isReduced_chartScheme_baseChangeChart`: the scheme of
  `W ×_X Z` is reduced.

## References

* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
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
    (Z : PrimeDivisor B S hS X)

/-- The inclusion of a prime divisor, as a morphism of algebraic spaces over `S`. -/
abbrev PrimeDivisor.inclusionHom :
    (⟨Z.subspace.toFunctor, Z.closed.1⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩ :=
  closedSubspaceHom B S hS hX Z.subspace Z.closed

/-- The inclusion of a prime divisor is a closed immersion of algebraic spaces. -/
theorem PrimeDivisor.isClosedImmersion_inclusionHom :
    IsClosedImmersion B S hS (Z.inclusionHom B S hS hX).hom :=
  isClosedImmersion_closedSubspaceHom B S hS hX Z.subspace Z.closed

/-- **The étale chart `W ×_X Z` of a prime divisor `Z`**, the base change of an étale chart `W`
of `X` along the closed immersion `Z → X` (Stacks 03G2, part (4)). -/
abbrev PrimeDivisor.baseChangeChart (W : SmallEtale B S hS X) :
    SmallEtale B S hS Z.subspace.toFunctor :=
  (smallBaseChange B S hS (Z.inclusionHom B S hS hX)
    (Z.isClosedImmersion_inclusionHom B S hS hX).rep).obj W

/-- The cartesian square of charts over the inclusion of a prime divisor at the base change of
an étale chart `W` of `X`. -/
def PrimeDivisor.baseChangeChartDiagram (W : SmallEtale B S hS X) :
    ChartDiagram B S hS Z.subspace.toFunctor X (Z.inclusionHom B S hS hX).hom where
  U := Z.baseChangeChart B S hS hX W
  V := W
  g := (Z.isClosedImmersion_inclusionHom B S hS hX).rep.snd W.obj.hom
  comm := ((Z.isClosedImmersion_inclusionHom B S hS hX).rep.isPullback W.obj.hom).w

/-- The projection of schemes `W ×_X Z → W`. -/
abbrev PrimeDivisor.baseChangeChartProj (W : SmallEtale B S hS X) :
    chartScheme (Z.baseChangeChart B S hS hX W) ⟶ chartScheme W :=
  (BigFppfOver.toScheme B S hS).map (Z.baseChangeChartDiagram B S hS hX W).g

/-- **The projection `W ×_X Z → W` is a closed immersion of schemes**, the base change of the
closed immersion `Z → X` along the chart. -/
theorem PrimeDivisor.isClosedImmersion_baseChangeChartProj (W : SmallEtale B S hS X) :
    _root_.AlgebraicGeometry.IsClosedImmersion (Z.baseChangeChartProj B S hS hX W) :=
  (Z.isClosedImmersion_inclusionHom B S hS hX).property_snd W.obj.hom

/-- The projection `W ×_X Z → W` is compatible with the maps to `|X|`: a point of `W ×_X Z`
determines a point of `|Z|` whose image in `|X|` is the point determined by its projection. -/
theorem PrimeDivisor.chartSchemeToPoints_baseChangeChartProj (W : SmallEtale B S hS X)
    (y : chartScheme (Z.baseChangeChart B S hS hX W)) :
    chartSchemeToPoints B S hS X W (Z.baseChangeChartProj B S hS hX W y) =
      pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι
        (chartSchemeToPoints B S hS Z.subspace.toFunctor (Z.baseChangeChart B S hS hX W) y) :=
  chartSchemeToPoints_map_chartDiagram B S hS (Z.baseChangeChartDiagram B S hS hX W) y

/-- **A point of the chart over a point of `Z` lifts to `W ×_X Z`** (Stacks 03H4). -/
theorem PrimeDivisor.exists_baseChangeChartProj_eq (W : SmallEtale B S hS X) (u : chartScheme W)
    (hu : chartSchemeToPoints B S hS X W u ∈ Z.support B S hS X) :
    ∃ y : chartScheme (Z.baseChangeChart B S hS hX W),
      Z.baseChangeChartProj B S hS hX W y = u := by
  obtain ⟨a, ha⟩ := hu
  set b := (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj W)).symm u with hb
  have hab : pointsMap B S hS Z.subspace.toFunctor (Z.inclusionHom B S hS hX).hom a =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj W)) W.obj.hom b :=
    ha.trans (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X W u)
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
    ((Z.isClosedImmersion_inclusionHom B S hS hX).rep.isPullback W.obj.hom) a b hab
  refine ⟨pointsToScheme B S hS _ w, ?_⟩
  refine (pointsToScheme_pointsMap_yoneda B S hS
    ((Z.isClosedImmersion_inclusionHom B S hS hX).rep.snd W.obj.hom) w).symm.trans ?_
  rw [hw, hb]
  exact (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X).obj W)).apply_symm_apply u

/-- **The image of `W ×_X Z → W` is the preimage of `|Z|`.** -/
theorem PrimeDivisor.range_baseChangeChartProj (W : SmallEtale B S hS X) :
    Set.range (Z.baseChangeChartProj B S hS hX W) =
      chartSchemeToPoints B S hS X W ⁻¹' Z.support B S hS X := by
  ext u
  constructor
  · rintro ⟨y, rfl⟩
    rw [Set.mem_preimage, Z.chartSchemeToPoints_baseChangeChartProj B S hS hX W y]
    exact ⟨_, rfl⟩
  · exact Z.exists_baseChangeChartProj_eq B S hS hX W u

/-- **The scheme of `W ×_X Z` is reduced**, `Z` being an integral algebraic space. -/
theorem PrimeDivisor.isReduced_chartScheme_baseChangeChart (W : SmallEtale B S hS X) :
    IsReduced (chartScheme (Z.baseChangeChart B S hS hX W)) :=
  isReduced_chartScheme_of_isIntegralSpace Z.closed.1 Z.integral _

end AlgebraicGeometry.Space

end
