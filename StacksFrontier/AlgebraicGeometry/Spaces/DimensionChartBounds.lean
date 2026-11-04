module

public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingProperness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.SingularPointNeighborhoods

/-!
# Bounds on the dimension of an algebraic space through étale charts

The dimension of an algebraic space `F` at a point is the local dimension of any étale scheme
chart at a point above it (Stacks 04N5), and the dimension of `F` is the supremum of these
(Stacks 04N6).  This file records the two comparisons with the dimension of a chart which follow:

* the dimension of the scheme `U` of an étale chart `yoneda U ⟶ F` is at most the dimension of
  `F` (`AlgebraicGeometry.Space.topologicalKrullDim_le_dimension_of_etale`);
* if the chart is surjective on points, the dimension of `F` is at most that of `U`.

## Main results

* `AlgebraicGeometry.Space.dimensionAtPoint_le_topologicalKrullDim_of_chart`: the dimension at
  a point is at most the dimension of an étale chart through it.
* `AlgebraicGeometry.Space.dimension_le_topologicalKrullDim_of_surjective`: the dimension of `F`
  is at most the dimension of an étale chart surjective on points.
* `AlgebraicGeometry.Space.dimension_le_topologicalKrullDim_of_isClosedImmersion`: a closed
  subspace of `F` has dimension at most that of an étale chart of `F` surjective on points, its
  base change being a surjective étale chart of the subspace by a closed subscheme of the chart.
* `AlgebraicGeometry.Space.dimension_spaceOverSmallerBase_le`: an algebraic space over `S`
  mapping to a scheme `W` over `S`, regarded as an algebraic space over `W` (Stacks 04SG), has
  dimension at most its dimension over `S`: the two small étale sites have the same charts.

## References

* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04N6](https://stacks.math.columbia.edu/tag/04N6)
* [Stacks Project, Tag 0B7I](https://stacks.math.columbia.edu/tag/0B7I)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)

/-- **The dimension at a point is at most the dimension of an étale chart through it.** -/
theorem dimensionAtPoint_le_topologicalKrullDim_of_chart (x : points B S hS F)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hp : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x) :
    dimensionAtPoint B S hS F hF x ≤ topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
  rw [dimensionAtPoint_eq_of_etale_chart B S hS F hF x U a ha p hp]
  exact topologicalKrullDimAt_le_topologicalKrullDim _

/-- **The dimension of an algebraic space is at most the dimension of an étale chart which is
surjective on points.** -/
theorem dimension_le_topologicalKrullDim_of_surjective (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ F)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hs : Function.Surjective (pointsMap B S hS (yoneda.obj U) a)) :
    dimension B S hS F hF ≤ topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
  refine iSup_le fun x => ?_
  obtain ⟨q, hq⟩ := hs x
  obtain ⟨p, rfl⟩ := Quot.exists_rep q
  exact dimensionAtPoint_le_topologicalKrullDim_of_chart B S hS hF x U a ha p hq

include hF in
/-- **A closed subspace has dimension at most that of a surjective étale chart of the ambient
space.**  The base change of a surjective étale chart `yoneda U ⟶ F` along a closed immersion
`Z ⟶ F` is a surjective étale chart of `Z` whose scheme is a closed subscheme of `U`. -/
theorem dimension_le_topologicalKrullDim_of_isClosedImmersion
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z) (i : Z ⟶ F)
    (hi : IsClosedImmersion B S hS i) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hs : Function.Surjective (pointsMap B S hS (yoneda.obj U) a)) :
    dimension B S hS Z hZ ≤ topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
  have sq := (hi.rep.isPullback a).flip
  have hfst : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hi.rep.fst a) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq ha
  have hsurj : Function.Surjective
      (pointsMap B S hS (yoneda.obj (hi.rep.pullback a)) (hi.rep.fst a)) :=
    isSurjective_baseChange_of_isPullback
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS U) hZ hF sq hs
  have hcl : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd a)) := hi.property_snd a
  exact (dimension_le_topologicalKrullDim_of_surjective B S hS hZ _ _ hfst hsurj).trans
    ((BigFppfOver.toScheme B S hS).map
      (hi.rep.snd a)).isClosedEmbedding.isInducing.topologicalKrullDim_le

/-- **The dimension of an algebraic space over a smaller base.**  For an algebraic space `Y` over
`S` with a morphism `φ` to a scheme `W` over `S`, the algebraic space `Y'` over `W` of Stacks 04SG
has dimension at most the dimension of `Y` over `S`: an étale chart of `Y'` is an étale chart of
`Y` with the same scheme (`AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalence`). -/
theorem dimension_spaceOverSmallerBase_le (W : Scheme.{u}) (hW : B.Contains W)
    (h : B.obj hW ⟶ B.obj hS) (Y : AlgebraicSpaces B S hS) (φ : Y.1 ⟶ yoneda.obj (Over.mk h)) :
    dimension B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2 ≤ dimension B S hS Y.1 Y.2 := by
  refine iSup_le fun z => ?_
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B W hW _
    (spaceOverSmallerBase B W S hW hS h Y φ).2 z
  refine (dimensionAtPoint_le_topologicalKrullDim_of_chart B W hW _ z U a ha p hp).trans ?_
  let V := (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).functor.obj
    ⟨CostructuredArrow.mk a, ha⟩
  exact topologicalKrullDim_le_dimension_of_etale B S hS Y.2 V.obj.left V.obj.hom V.property

end AlgebraicGeometry.Space
